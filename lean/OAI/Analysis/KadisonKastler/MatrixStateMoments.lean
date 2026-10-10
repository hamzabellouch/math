import OAI.Analysis.KadisonKastler.MatrixStateAveraging

namespace OAI

/-! # Mixed vector-state moments of finite matrix orbits

These are the two independent-copy pairings used in graph flattening.
The finite signed-permutation averages are actual matrix averages, and
only the common vector-state centralizer identity is used. In particular
none of the state calculations presupposes a tracial ambient state.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The ambient vector functional, without an algebra-membership wrapper. -/
def operatorVectorState (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun x := inner ℂ Ω (x Ω)
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

omit [CompleteSpace H] in
@[simp] theorem operatorVectorState_apply (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω x = inner ℂ Ω (x Ω) := rfl

private theorem average_linear {G V W : Type*} [Fintype G]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (L : V →ₗ[ℂ] W) (f : G → V) :
    finiteAverage (fun g => L (f g)) = L (finiteAverage f) := by
  simp only [finiteAverage, map_smul, map_sum]

private theorem average_sandwich {G : Type*} [Fintype G]
    (a b : H →L[ℂ] H) (f : G → H →L[ℂ] H) :
    finiteAverage (fun g => a * f g * b) = a * finiteAverage f * b := by
  simp only [finiteAverage, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]

private theorem state_unitaryConj (M : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M)
    (hcentral : ∀ z ∈ M, inner ℂ Ω (((u : H →L[ℂ] H) * z) Ω) =
      inner ℂ Ω ((z * (u : H →L[ℂ] H)) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    operatorVectorState Ω (unitaryConj u x) = operatorVectorState Ω x := by
  have hc := hcentral (x * star (u : H →L[ℂ] H))
    (M.mul_mem hx (M.toStarSubalgebra.star_mem' hu))
  change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (x Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using hc

/-- The first pairing of two independently conjugated copies is exactly
one matrix average, paired against the unaveraged first element. -/
theorem matrixState_two_orbit_average
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hcentral : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) :
    finiteAverage (fun g : SignedPermutation (Fin d) =>
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω
          (unitaryConj (matrixUnitSignedRepresentation E g) a *
            unitaryConj (matrixUnitSignedRepresentation E h) b))) =
      operatorVectorState Ω (a * matrixUnitAverage E b) := by
  let B := matrixUnitAverage E b
  have hB : B ∈ M := matrixUnitAverage_mem_algebra M E hEM b hb
  have he (g : SignedPermutation (Fin d)) :
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω
          (unitaryConj (matrixUnitSignedRepresentation E g) a *
            unitaryConj (matrixUnitSignedRepresentation E h) b)) =
      operatorVectorState Ω (a * B) := by
    rw [average_linear]
    have hm : finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          unitaryConj (matrixUnitSignedRepresentation E h) b) =
        unitaryConj (matrixUnitSignedRepresentation E g) a * B := by
      change finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          unitaryConj (matrixUnitSignedRepresentation E h) b) =
        unitaryConj (matrixUnitSignedRepresentation E g) a *
          finiteAverage (fun h : SignedPermutation (Fin d) =>
            unitaryConj (matrixUnitSignedRepresentation E h) b)
      simpa only [mul_one] using average_sandwich (H := H)
        (unitaryConj (matrixUnitSignedRepresentation E g) a) 1
        (fun h => unitaryConj (matrixUnitSignedRepresentation E h) b)
    rw [hm]
    have hi : unitaryConj (matrixUnitSignedRepresentation E g) B = B :=
      finiteUnitaryAverage_invariant (H := H) (matrixUnitSignedRepresentation E) b g
    have hp : unitaryConj (matrixUnitSignedRepresentation E g) (a * B) =
        unitaryConj (matrixUnitSignedRepresentation E g) a * B := by
      have hmul := map_mul (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)
        (matrixUnitSignedRepresentation E g)) a B
      change unitaryConj _ (a * B) = unitaryConj _ a * unitaryConj _ B at hmul
      rwa [hi] at hmul
    rw [← hp]
    exact state_unitaryConj M Ω _ (hEM (matrixUnitSignedRepresentation_mem E g))
      (hcentral _ (matrixUnitSignedRepresentation_mem E g)) (a * B) (M.mul_mem ha hB)
  simp only [he, finiteAverage_const]
  rfl

/-- Averaging a relative pair of independently sampled matrix unitaries
also gives the ordinary matrix average. -/
theorem matrixState_relative_orbit_average
    (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (a b c : H →L[ℂ] H) :
    finiteAverage (fun g : SignedPermutation (Fin d) =>
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω (a *
          unitaryConj (star (matrixUnitSignedRepresentation E g))
            (unitaryConj (matrixUnitSignedRepresentation E h) b) * c))) =
      operatorVectorState Ω (a * matrixUnitAverage E b * c) := by
  have he (g : SignedPermutation (Fin d)) :
      finiteAverage (fun h : SignedPermutation (Fin d) =>
        operatorVectorState Ω (a *
          unitaryConj (star (matrixUnitSignedRepresentation E g))
            (unitaryConj (matrixUnitSignedRepresentation E h) b) * c)) =
      operatorVectorState Ω (a * matrixUnitAverage E b * c) := by
    rw [average_linear, average_sandwich]
    have hm : finiteAverage (fun h : SignedPermutation (Fin d) =>
        unitaryConj (star (matrixUnitSignedRepresentation E g))
          (unitaryConj (matrixUnitSignedRepresentation E h) b)) =
        unitaryConj (star (matrixUnitSignedRepresentation E g)) (matrixUnitAverage E b) := by
      change finiteAverage (fun h : SignedPermutation (Fin d) =>
        (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H) *
          unitaryConj (matrixUnitSignedRepresentation E h) b *
          star (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H)) =
        (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H) *
          finiteAverage (fun h : SignedPermutation (Fin d) =>
            unitaryConj (matrixUnitSignedRepresentation E h) b) *
          star (star (matrixUnitSignedRepresentation E g) : H →L[ℂ] H)
      exact average_sandwich (H := H) _ _ _
    rw [hm]
    have hi := finiteUnitaryAverage_invariant (H := H) (matrixUnitSignedRepresentation E) b g
    have hi' := congrArg (unitaryConj (star (matrixUnitSignedRepresentation E g))) hi
    rw [unitaryConj_star_unitaryConj] at hi'
    change matrixUnitAverage E b =
      unitaryConj (star (matrixUnitSignedRepresentation E g)) (matrixUnitAverage E b) at hi'
    rw [← hi']
  simp only [he, finiteAverage_const]

/-- The first independent-copy pairing tends to the product of the two
vector-state values. -/
theorem matrixState_two_orbit_tendsto
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) :
    Tendsto (fun n => finiteAverage (fun g : SignedPermutation (Fin (d n)) =>
      finiteAverage (fun h : SignedPermutation (Fin (d n)) =>
        operatorVectorState Ω (unitaryConj (matrixUnitSignedRepresentation (E n) g) a *
          unitaryConj (matrixUnitSignedRepresentation (E n) h) b)))) atTop
      (𝓝 (operatorVectorState Ω a * operatorVectorState Ω b)) := by
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hcentral _) a b ha hb]
  have hl := vectorState_sandwich_tendsto (fun n => matrixUnitAverage (E n) b)
    ((operatorVectorState Ω b) • (1 : H →L[ℂ] H))
    (matrixUnitAverage_tendsto_vectorState M Ω hΩ d E hmono hEM hirr hcentral b hb)
    Ω a 1
  simpa only [mul_one, mul_smul_comm, mul_one, smul_apply, inner_smul_right,
    operatorVectorState_apply, mul_comm] using hl

/-- The nested relative-conjugation pairing tends to the scalar state
value of the averaged element times the state of the sandwich. -/
theorem matrixState_relative_orbit_tendsto
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (a b c : H →L[ℂ] H) (hb : b ∈ M) :
    Tendsto (fun n => finiteAverage (fun g : SignedPermutation (Fin (d n)) =>
      finiteAverage (fun h : SignedPermutation (Fin (d n)) =>
        operatorVectorState Ω (a * unitaryConj (star (matrixUnitSignedRepresentation (E n) g))
          (unitaryConj (matrixUnitSignedRepresentation (E n) h) b) * c)))) atTop
      (𝓝 (operatorVectorState Ω b * operatorVectorState Ω (a * c))) := by
  simp_rw [matrixState_relative_orbit_average]
  have hl := vectorState_sandwich_tendsto (fun n => matrixUnitAverage (E n) b)
    ((operatorVectorState Ω b) • (1 : H →L[ℂ] H))
    (matrixUnitAverage_tendsto_vectorState M Ω hΩ d E hmono hEM hirr hcentral b hb)
    Ω a c
  simpa only [mul_smul_comm, smul_mul_assoc, mul_one, smul_apply, inner_smul_right,
    operatorVectorState_apply] using hl

/-- The crossed fourth-moment pairing is controlled by the two positive
pairings. This is the vector-state version, with no trace assumption. -/
theorem operatorVectorState_square_re_le (Ω : H) (a : H →L[ℂ] H) :
    2 * (operatorVectorState Ω (a ^ 2)).re ≤
      ‖a Ω‖ ^ 2 + ‖(star a) Ω‖ ^ 2 := by
  have hn := sq_nonneg ‖(star a) Ω - a Ω‖
  rw [norm_sub_sq (𝕜 := ℂ)] at hn
  have he : inner ℂ ((star a) Ω) (a Ω) = operatorVectorState Ω (a ^ 2) := by
    simp only [operatorVectorState_apply, pow_two, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [he] at hn
  change 0 ≤ ‖(star a) Ω‖ ^ 2 -
    2 * (operatorVectorState Ω (a ^ 2)).re + ‖a Ω‖ ^ 2 at hn
  linarith

end

end KadisonKastler

end OAI
