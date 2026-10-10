import OAI.Analysis.KadisonKastler.GraphMomentBounds

namespace OAI

/-! # Finite matrix samples with bounded graph cost

The matrix-stage centralizer identities preserve the two second moments
and the diagonal fourth moments. Relative irreducibility supplies the
mixed-moment limits. Thus the bound of ten is attained by an actual
finite stage and a finite independent sample family.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem expect_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (f : G → ℝ) : (𝔼 g, f (e g)) = 𝔼 g, f g :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

private theorem expect_pair_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (f : G → G → ℝ) :
    (𝔼 g, 𝔼 h, f (e g) (e h)) = 𝔼 g, 𝔼 h, f g h := by
  have hi (g : G) : (𝔼 h, f (e g) (e h)) = 𝔼 h, f (e g) h :=
    expect_comp_equiv e (f (e g))
  simp_rw [hi]
  exact expect_comp_equiv e (fun g => 𝔼 h, f g h)

private theorem firstMoment_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (Ω : H) (a : G → H →L[ℂ] H) :
    orbitFirstPairMoment Ω (fun g => a (e g)) = orbitFirstPairMoment Ω a :=
  expect_pair_comp_equiv e (fun g h =>
    realVectorState Ω ((star (a g) * a g) * (star (a h) * a h)))

private theorem thirdMoment_comp_equiv {G : Type*} [Fintype G]
    (e : G ≃ G) (Ω : H) (a : G → H →L[ℂ] H) :
    orbitThirdPairMoment Ω (fun g => a (e g)) = orbitThirdPairMoment Ω a :=
  expect_pair_comp_equiv e (fun g h =>
    realVectorState Ω ((star (a g) * a h) * (star (a h) * a g)))

/-- Taking adjoints exchanges the two independent matrix samples. -/
theorem star_matrixOrbitSample {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (x : H →L[ℂ] H) (g : MatrixOrbitIndex d) :
    star (matrixOrbitSample E x g) = matrixOrbitSample E (star x) g.swap := by
  simp only [matrixOrbitSample, unitaryDoubleOrbit, star_mul, star_star]
  noncomm_ring

private theorem state_conj (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (g : SignedPermutation (Fin d)) (x : H →L[ℂ] H) (hx : x ∈ M) :
    realVectorState Ω (unitaryConj (matrixUnitSignedRepresentation E g) x) =
      realVectorState Ω x := by
  let u := matrixUnitSignedRepresentation E g
  have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E g
  have he := hc u hu (x * star (u : H →L[ℂ] H))
    (M.mul_mem hx (M.toStarSubalgebra.star_mem' (hEM hu)))
  apply congrArg Complex.re
  change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (x Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using he

/-- Every actual matrix sample has the original right second moment. -/
theorem matrixOrbit_right_second (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω (star (matrixOrbitSample E x g) * matrixOrbitSample E x g) =
      ‖x Ω‖ ^ 2 := by
  rw [matrixOrbitSample, unitaryDoubleOrbit_star_mul_self]
  rw [state_conj M Ω E hEM hc g.2 _ (M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx)]
  exact realVectorState_star_mul_self Ω x

/-- The left second moment is preserved as well. -/
theorem matrixOrbit_left_second (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (g : MatrixOrbitIndex d) :
    realVectorState Ω (matrixOrbitSample E x g * star (matrixOrbitSample E x g)) =
      ‖star x Ω‖ ^ 2 := by
  have he := matrixOrbit_right_second M Ω E hEM hc (star x)
    (M.toStarSubalgebra.star_mem' hx) g.swap
  simpa only [← star_matrixOrbitSample, star_star] using he

private theorem left_positive_state (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω (x * star x) = (‖star x Ω‖ ^ 2 : ℝ) := by
  simpa only [star_star] using operatorVectorState_star_mul_self Ω (star x)

section Limits

variable (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M)

include M hΩ hmono hEM hirr hc hx

/-- The first actual sample pairing converges to the square of its
right second moment. -/
theorem matrixOrbit_firstMoment_tendsto :
    Tendsto (fun j => orbitFirstPairMoment Ω (matrixOrbitSample (E j) x)) atTop
      (𝓝 ((‖x Ω‖ ^ 2) ^ 2)) := by
  have hs := M.mul_mem (M.toStarSubalgebra.star_mem' hx) hx
  have ht := matrixState_two_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star x * x) (star x * x) hs hs
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hc _) _ _ hs hs] at ht
  rw [operatorVectorState_star_mul_self] at ht
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp_rw [orbitFirstPairMoment, matrixOrbit_first_pairing_expect M Ω _ (hEM _) (hc _) x hx]
  simpa only [Function.comp_def, realVectorState_apply, operatorVectorState_apply,
    operatorVectorState_star_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, pow_two] using hr

/-- The positive mixed pairing converges to the product of the right
and left second moments. -/
theorem matrixOrbit_thirdMoment_tendsto :
    Tendsto (fun j => orbitThirdPairMoment Ω (matrixOrbitSample (E j) x)) atTop
      (𝓝 (‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2)) := by
  have hs := M.mul_mem hx (M.toStarSubalgebra.star_mem' hx)
  have ht := matrixState_relative_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star x) (x * star x) x hs
  simp_rw [matrixState_relative_orbit_average] at ht
  rw [left_positive_state, operatorVectorState_star_mul_self] at ht
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp_rw [orbitThirdPairMoment, matrixOrbit_third_pairing_expect M Ω _ (hEM _) (hc _) x hx]
  simpa only [Function.comp_def, operatorVectorState_star_mul_self, left_positive_state,
    ← Complex.ofReal_mul, Complex.ofReal_re, realVectorState_apply, operatorVectorState_apply,
    mul_comm] using hr

/-- The full off-diagonal cost has its required actual scalar limit. -/
theorem matrixOrbit_graphPairing_tendsto (k : ℝ) :
    Tendsto (fun j =>
      orbitFirstPairMoment Ω (matrixOrbitSample (E j) x) +
      2 * orbitThirdPairMoment Ω (matrixOrbitSample (E j) x) +
      k * (orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) +
        2 * orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)))) atTop
      (𝓝 ((‖x Ω‖ ^ 2) ^ 2 + k * (‖star x Ω‖ ^ 2) ^ 2 +
        2 * (k + 1) * ‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2)) := by
  have hr := matrixOrbit_firstMoment_tendsto M Ω hΩ d E hmono hEM hirr hc x hx
  have hm := matrixOrbit_thirdMoment_tendsto M Ω hΩ d E hmono hEM hirr hc x hx
  have hstar := M.toStarSubalgebra.star_mem' hx
  have hl := matrixOrbit_firstMoment_tendsto M Ω hΩ d E hmono hEM hirr hc (star x) hstar
  have hn := matrixOrbit_thirdMoment_tendsto M Ω hΩ d E hmono hEM hirr hc (star x) hstar
  have he1 (j : ℕ) :
      orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        orbitFirstPairMoment Ω (matrixOrbitSample (E j) (star x)) := by
    simp_rw [star_matrixOrbitSample]
    exact firstMoment_comp_equiv (Equiv.prodComm _ _) Ω _
  have he3 (j : ℕ) :
      orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        orbitThirdPairMoment Ω (matrixOrbitSample (E j) (star x)) := by
    simp_rw [star_matrixOrbitSample]
    exact thirdMoment_comp_equiv (Equiv.prodComm _ _) Ω _
  simp_rw [he1, he3]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hk : Tendsto (fun _ : ℕ => k) atTop (𝓝 k) := tendsto_const_nhds
  have hlim := (hr.add (htwo.mul hm)).add (hk.mul (hl.add (htwo.mul hn)))
  convert hlim using 1
  congr 1
  simp only [star_star]
  ring

/-- There is a genuine finite matrix stage and a positive sample size
whose independently sampled signed graph cost is at most ten. -/
theorem exists_matrixOrbit_graphCost_le_ten {k : ℝ} (hk : 1 ≤ k)
    (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1) :
    ∃ j m, 1 ≤ m ∧
      (𝔼 ω : Fin m → MatrixOrbitIndex (d j), 𝔼 ε : Fin m → Bool,
        graphMomentCost Ω k
          (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε)) ≤ 10 := by
  let C : ℕ → ℕ → ℝ := fun j m =>
    𝔼 ω : Fin m → MatrixOrbitIndex (d j), 𝔼 ε : Fin m → Bool,
      graphMomentCost Ω k
        (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε)
  let T : ℕ → ℝ := fun j =>
    orbitFirstPairMoment Ω (matrixOrbitSample (E j) x) +
    2 * orbitThirdPairMoment Ω (matrixOrbitSample (E j) x) +
    k * (orbitFirstPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) +
      2 * orbitThirdPairMoment Ω (fun g => star (matrixOrbitSample (E j) x g)))
  let L := (‖x Ω‖ ^ 2) ^ 2 + k * (‖star x Ω‖ ^ 2) ^ 2 +
    2 * (k + 1) * ‖x Ω‖ ^ 2 * ‖star x Ω‖ ^ 2
  let D := realVectorState Ω ((star x * x) ^ 2) +
    k * realVectorState Ω ((x * star x) ^ 2)
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hL6 : L ≤ 6 := graph_pairing_scalar_le_six (sq_nonneg _) (sq_nonneg _) hk hxnorm.le
  have hT : Tendsto T atTop (𝓝 L) :=
    matrixOrbit_graphPairing_tendsto M Ω hΩ d E hmono hEM hirr hc x hx k
  have hC (j m : ℕ) (hm : 1 ≤ m) :
      C j m ≤ 1 + D / m + (1 - (m : ℝ)⁻¹) * T j := by
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    let : NeZero m := ⟨Nat.ne_of_gt hm0⟩
    have hb := expect_sampled_graphMomentCost_le (I := Fin m) Ω hk0
      (matrixOrbitSample (E j) x)
    have hsecond : orbitSecondMoment Ω k (matrixOrbitSample (E j) x) = 1 := by
      unfold orbitSecondMoment
      simp only [matrixOrbit_right_second M Ω (E j) (hEM j) (hc j) x hx,
        matrixOrbit_left_second M Ω (E j) (hEM j) (hc j) x hx, Fintype.expect_const]
      exact hxnorm
    have hdiag : orbitDiagonalMoment Ω (matrixOrbitSample (E j) x) =
        realVectorState Ω ((star x * x) ^ 2) := by
      unfold orbitDiagonalMoment
      simp only [matrixOrbit_diagonal_fourth M Ω (E j) (hEM j) (hc j) x hx,
        Fintype.expect_const]
    have hdiagstar : orbitDiagonalMoment Ω (fun g => star (matrixOrbitSample (E j) x g)) =
        realVectorState Ω ((x * star x) ^ 2) := by
      have hh (g : MatrixOrbitIndex (d j)) :=
        matrixOrbit_diagonal_fourth M Ω (E j) (hEM j) (hc j) (star x)
          (M.toStarSubalgebra.star_mem' hx) g.swap
      have hv (g : MatrixOrbitIndex (d j)) :
          realVectorState Ω ((star (star (matrixOrbitSample (E j) x g)) *
            star (matrixOrbitSample (E j) x g)) ^ 2) =
          realVectorState Ω ((x * star x) ^ 2) := by
        simpa only [← star_matrixOrbitSample, star_star] using hh g
      simp only [orbitDiagonalMoment, hv, Fintype.expect_const]
    simpa only [C, T, D, hsecond, hdiag, hdiagstar, Fintype.card_fin] using hb
  exact exists_stage_sample_cost_le_ten C T hL0 hL6 hT hC

end Limits

end

end KadisonKastler

end OAI
