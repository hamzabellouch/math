import OAI.Probability.RadialTransition.BoltzmannMeasure

namespace OAI

universe uX uI

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

lemma cell_young {D G n : ℝ} (hD : 0 < D) : n * G ≤ D / 4 * n^2 + G^2 / D := by
  have hh := sq_nonneg (D*n - 2*G)
  have he : G^2 / D * D = G^2 := div_mul_cancel₀ _ hD.ne'
  nlinarith

theorem one_cell_exponential_moment {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν]
    (z : ℝ) {β D B J G : ℝ} (hβ : 0 ≤ β) (hD : 0 < D) (hJ : J ≤ D)
    {H : ParticleState X → ℝ} (hH : Measurable H)
    (henergy : ∀ x, (D-J/2) * (particleCount x : ℝ)^2 - B*particleCount x -
      (particleCount x : ℝ)*G ≤ H x - H particleVacuum) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*D/4*(particleCount x : ℝ)^2 - β*H x)) ∂particleBase ν z) ≤
      ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) *
      ENNReal.ofReal (Real.exp (β*G^2/D)) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂particleBase ν z := by
  let A := Real.exp (β*G^2/D - β*H particleVacuum)
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-β*H x))) :=
    (Real.measurable_exp.comp (measurable_const.mul hH)).ennreal_ofReal
  have hlower : ENNReal.ofReal (Real.exp (-β*H particleVacuum)) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂particleBase ν z := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-β*H x)) ∂Measure.dirac particleVacuum :=
        (lintegral_dirac' _ hm).symm
      _ ≤ _ := lintegral_mono' (dirac_vacuum_le_particleBase ν z) le_rfl
  have hupper : (∫⁻ x, ENNReal.ofReal (Real.exp (β*D/4*(particleCount x : ℝ)^2 - β*H x)) ∂particleBase ν z) ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal A * ENNReal.ofReal (Real.exp (β*B*particleCount x)) ∂particleBase ν z := by
        apply lintegral_mono
        intro x
        dsimp only [A]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hy := cell_young (G := G) (n := (particleCount x : ℝ)) hD
        have hj := mul_nonneg (sub_nonneg.mpr hJ) (sq_nonneg (particleCount x : ℝ))
        have he := mul_le_mul_of_nonneg_left (henergy x) hβ
        have hy' := mul_le_mul_of_nonneg_left hy hβ
        have hj' := mul_nonneg hβ hj
        have heq : β * (G^2/D) = β*G^2/D := by ring
        nlinarith
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_exp_particleCount]
  calc
    _ ≤ _ := hupper
    _ = ENNReal.ofReal (Real.exp ((ν univ).toReal * Real.exp (z+β*B))) *
        ENNReal.ofReal (Real.exp (β*G^2/D)) * ENNReal.ofReal (Real.exp (-β*H particleVacuum)) := by
      dsimp [A]
      rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [neg_mul]
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hlower

section ProductCells
variable {I : Type uI} [Fintype I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

def cellN (i : I) (x : ∀ j, ParticleState (X j)) : ℝ := particleCount (x i)

omit [Fintype I] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] in
theorem cellN_nonneg (i : I) (x : ∀ j, ParticleState (X j)) : 0 ≤ cellN i x := Nat.cast_nonneg _

omit [Fintype I] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]
  [∀ i, MeasurableSpace (X i)] in
theorem measurable_cellN (i : I) : Measurable (cellN (X := X) i) :=
  ((show Measurable (fun n : ℕ => (n : ℝ)) from continuous_of_discreteTopology.measurable).comp
    continuous_particleCount.measurable).comp (measurable_pi_apply i)

theorem integrable_exp_cell_total (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z c : ℝ) : Integrable (fun x => Real.exp (c * ∑ i, cellN i x))
      (Measure.pi (fun i => particleBase (ν i) z)) := by
  have hh := Integrable.fintype_prod_dep (fun i => integrable_exp_particleCount (ν i) z c)
  convert hh using 1
  ext x
  rw [Finset.mul_sum, Real.exp_sum]
  rfl

theorem cell_partition_pos (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {E : (∀ i, ParticleState (X i)) → ℝ}
    (hi : Integrable (fun x => Real.exp (-E x)) (Measure.pi (fun i => particleBase (ν i) z))) :
    0 < boltzmannPartition (Measure.pi (fun i => particleBase (ν i) z)) E := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr
  have hs : Function.support (fun x => Real.exp (-E x)) = univ := by
    ext x
    simp [Function.support, Real.exp_ne_zero]
  rw [hs]
  rw [Measure.pi_univ]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [particleBase_univ (measure_ne_top (ν i) univ)]
  exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

theorem weighted_square_le {I : Type uI} [Fintype I] (w n : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hrow : ∑ i, w i ≤ 1) :
    (∑ i, w i * n i)^2 ≤ ∑ i, w i * (n i)^2 := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg (n i)))
    (fun i (_ : i ∈ Finset.univ) => (show (w i * n i)^2 ≤ w i * (w i * (n i)^2) by nlinarith))
  exact hh.trans (mul_le_of_le_one_left (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg (n i)))) hrow)

theorem integrable_cell_numerator (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B : ℝ} {E f : (∀ i, ParticleState (X i)) → ℝ}
    (hE : Measurable E) (hf : Measurable f)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x)
    (hfbound : ∀ x, f x ≤ D/2 * ∑ i, (cellN i x)^2) :
    Integrable (fun x => Real.exp (f x - E x)) (Measure.pi (fun i => particleBase (ν i) z)) := by
  apply (integrable_exp_cell_total ν z B).mono' (Real.measurable_exp.comp (hf.sub hE)).aestronglyMeasurable
  filter_upwards [] with x
  change |Real.exp (f x - E x)| ≤ Real.exp (B * ∑ i, cellN i x)
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [hstable x, hfbound x])

theorem uniform_cell_exponential_moment [Nonempty I] [DecidableEq I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (z : ℝ) {D B V : ℝ} (hD : 0 < D) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (θ : I → I → ℝ) (hθ : ∀ i j, 0 ≤ θ i j) (hθdiag : ∀ i, θ i i = 0)
    (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    {E : (∀ i, ParticleState (X i)) → ℝ} (hE : Measurable E)
    (hstable : ∀ x, D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ E x)
    (hconditional : ∀ i x s, D/2 * (particleCount s : ℝ)^2 - B * particleCount s -
      (particleCount s : ℝ) * (D/8 * ∑ j, θ i j * cellN j x) ≤
      E (Function.update x i s) - E (Function.update x i particleVacuum)) :
    ∀ i, (∫ x, Real.exp (D/4 * (cellN i x)^2)
      ∂boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z)) E) ≤
      Real.exp (16/15 * V * Real.exp (z+B)) := by
  classical
  let μ := Measure.pi (fun j => particleBase (ν j) z)
  let F (i : I) (x : ∀ j, ParticleState (X j)) := D/4 * (cellN i x)^2
  let g (i : I) (x : ∀ j, ParticleState (X j)) := (1/16:ℝ) * ∑ j, θ i j * F j x
  let C := Real.exp (V * Real.exp (z+B))
  have hFmeas (i : I) : Measurable (F i) := measurable_const.mul ((measurable_cellN i).pow_const 2)
  have hF0 (i : I) (x : ∀ j, ParticleState (X j)) : 0 ≤ F i x := mul_nonneg (by positivity) (sq_nonneg _)
  have hθ1 (i j : I) : θ i j ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hθ i k) (Finset.mem_univ j)).trans (hrow i)
  have hFbound (i : I) (x : ∀ j, ParticleState (X j)) : F i x ≤ D/2 * ∑ j, (cellN j x)^2 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => (cellN j x)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    dsimp [F]
    nlinarith [sq_nonneg (cellN i x)]
  have hgmeas (i : I) : Measurable (g i) :=
    measurable_const.mul (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hFmeas j)))
  have hgBound (i : I) (x : ∀ j, ParticleState (X j)) : g i x ≤ D/2 * ∑ j, (cellN j x)^2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => mul_le_of_le_one_left (hF0 j x) (hθ1 i j))
    have hsum : ∑ j, F j x = D/4 * ∑ j, (cellN j x)^2 := by simp only [F, Finset.mul_sum]
    have hn : 0 ≤ ∑ j, (cellN j x)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [g]
    rw [hsum] at hh
    nlinarith
  have hiE : Integrable (fun x => Real.exp (-E x)) μ := by
    simpa using integrable_cell_numerator ν z hE measurable_const hstable
      (f := fun _ => 0) (fun x => mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hp := cell_partition_pos ν z hiE
  let := boltzmannMeasure_probability hiE hp
  have hiF (i : I) := integrable_cell_numerator ν z hE (hFmeas i) hstable (hFbound i)
  have hig (i : I) := integrable_cell_numerator ν z hE (hgmeas i) hstable (hgBound i)
  have hif (i : I) : Integrable (fun x => Real.exp (F i x)) (boltzmannMeasure μ E) := by
    apply integrable_boltzmann hE _ hp
    convert hiF i using 1
    ext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hC1 : 1 ≤ C := Real.one_le_exp_iff.mpr (mul_nonneg hV (Real.exp_pos _).le)
  have hint (i : I) : (∫ x, Real.exp (F i x) ∂boltzmannMeasure μ E) ≤
      C*(∫ x, Real.exp (g i x) ∂boltzmannMeasure μ E) := by
    have hfmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (F i x - E x))) :=
      (Real.measurable_exp.comp ((hFmeas i).sub hE)).ennreal_ofReal
    have hgmeas' : Measurable (fun x => ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x - E x))) :=
      measurable_const.mul (Real.measurable_exp.comp ((hgmeas i).sub hE)).ennreal_ofReal
    have hlocal : lmarginal (fun j => particleBase (ν j) z) {i}
        (fun x => ENNReal.ofReal (Real.exp (F i x - E x))) ≤
      lmarginal (fun j => particleBase (ν j) z) {i}
        (fun x => ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x - E x))) := by
      rw [lmarginal_singleton, lmarginal_singleton]
      intro x
      have hginv (s : ParticleState (X i)) : g i (Function.update x i s) = g i x := by
        dsimp only [g, F, cellN]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [hθdiag]
        · simp [Function.update_of_ne hj]
      have hcur := one_cell_exponential_moment (ν i) z (β := 1) (D := D) (B := B) (J := D)
        (G := D/8 * ∑ j, θ i j * cellN j x) (by norm_num) hD le_rfl
        (H := fun s => E (Function.update x i s))
        (hE.comp (measurable_update x (a := i))) (fun s => by
          convert hconditional i x s using 1; ring)
      have hG : (D/8 * ∑ j, θ i j * cellN j x)^2 / D ≤ g i x := by
        have hh := weighted_square_le (θ i) (fun j => cellN j x) (hθ i) (hrow i)
        have hs : ∑ j, θ i j * F j x = D/4 * ∑ j, θ i j * (cellN j x)^2 := by
          dsimp only [F]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        dsimp only [g]
        rw [hs]
        apply (div_le_iff₀ hD).mpr
        nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hh)]
      have hCi : Real.exp ((ν i univ).toReal * Real.exp (z+B)) ≤ C :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hvol i) (Real.exp_pos _).le)
      simp only [one_mul, neg_one_mul] at hcur
      calc
        _ = ∫⁻ s, ENNReal.ofReal (Real.exp (D/4*(particleCount s : ℝ)^2 -
            E (Function.update x i s))) ∂particleBase (ν i) z := by
          apply lintegral_congr
          intro s
          simp only [F, cellN, Function.update_self]
        _ ≤ _ := hcur
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp (g i x)) *
            ∫⁻ s, ENNReal.ofReal (Real.exp (-E (Function.update x i s))) ∂particleBase (ν i) z := by
          gcongr
        _ = _ := by
          rw [mul_assoc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply lintegral_congr
          intro s
          rw [hginv, Real.exp_sub]
          simp only [div_eq_mul_inv, Real.exp_neg, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have htotal := lintegral_le_of_lmarginal_le {i} hfmeas hgmeas' hlocal
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hiF i) (Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      ← ofReal_integral_eq_lintegral_ofReal (hig i) (Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      ← ENNReal.ofReal_mul (by linarith [hC1])] at htotal
    have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [hC1])
      (integral_nonneg (fun _ => (Real.exp_pos _).le)))).mp htotal
    rw [integral_boltzmann hE, integral_boltzmann hE]
    simp_rw [← Real.exp_add, neg_add_eq_sub]
    have hh := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hp.le)
    nlinarith
  have hc := occupation_moment_closure F θ hC1 (by norm_num : 0 ≤ (1/16:ℝ))
    (by norm_num : (1/16:ℝ) < 1) hFmeas hF0 hif hθ hrow hint
  intro i
  convert hc i using 1
  congr 1
  dsimp [C]
  rw [Real.log_exp]
  ring

end ProductCells
end RadialTransition

end

end OAI
