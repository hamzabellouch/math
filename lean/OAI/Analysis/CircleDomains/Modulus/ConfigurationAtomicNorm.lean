import OAI.Analysis.CircleDomains.Probability.ConfigurationMeasures
import OAI.Analysis.CircleDomains.Selection.AtomicHitTests

namespace OAI

/-! The mean measure of separated unit-square-norm configurations has atomic
square norm at most one. Separation makes the point assignment injective;
Cauchy--Schwarz then passes the finite-dimensional bound through averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

private theorem sum_sq_fibers_le {I X : Type*} [Fintype I] [DecidableEq X]
    (p : I → X) (hp : Injective p) (w : I → ℝ) (F : Finset X) :
    ∑ x ∈ F, (∑ i, if p i = x then w i else 0) ^ 2 ≤ ∑ i, w i ^ 2 := by
  classical
  have he (x : X) : (∑ i, if p i = x then w i else 0) ^ 2 =
      ∑ i, if p i = x then w i ^ 2 else 0 := by
    by_cases hx : ∃ i, p i = x
    · obtain ⟨i, hi⟩ := hx
      have heq (j : I) : p j = x ↔ j = i := by
        constructor
        · intro h; exact hp (h.trans hi.symm)
        · rintro rfl; exact hi
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · have hn (i : I) : p i ≠ x := fun hi => hx ⟨i, hi⟩
      simp [hn]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_ite_eq]
  split
  · exact le_rfl
  · exact sq_nonneg _

private theorem sum_sq_integrals_le_one {I T : Type*} [Fintype I] [MeasurableSpace T]
    (P : ProbabilityMeasure T) (h : I → T → ℝ)
    (hi : ∀ i, Integrable (h i) (P : Measure T))
    (hbound : ∀ t, ∑ i, h i t ^ 2 ≤ 1) :
    ∑ i, (∫ t, h i t ∂(P : Measure T)) ^ 2 ≤ 1 := by
  let v : I → ℝ := fun i => ∫ t, h i t ∂(P : Measure T)
  let S := ∑ i, v i ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb (t : T) : ∑ i, v i * h i t ≤ Real.sqrt S := by
    have hh : Real.sqrt (∑ i, h i t ^ 2) ≤ 1 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hbound t⟩
    exact (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v (fun i => h i t)).trans
      (by simpa only [S, mul_one] using mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg S))
  have hsi : Integrable (fun t => ∑ i, v i * h i t) (P : Measure T) :=
    integrable_finsetSum _ fun i _ => (hi i).const_mul (v i)
  have he : ∫ t, ∑ i, v i * h i t ∂(P : Measure T) = S := by
    rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (v i))]
    simp only [integral_const_mul, S, v, sq]
  have hle : S ≤ Real.sqrt S := by
    calc
      S = ∫ t, ∑ i, v i * h i t ∂(P : Measure T) := he.symm
      _ ≤ Real.sqrt S := by
        simpa only [integral_const, probReal_univ, one_smul] using
          integral_mono_ae hsi (integrable_const (Real.sqrt S)) (Eventually.of_forall hb)
  have hsq := Real.sq_sqrt hS0
  change S ≤ 1
  nlinarith [Real.sqrt_nonneg S]

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {n : ℕ} {r : ℝ}

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem HitConfiguration.points_injective (hr : 0 < r) (p : HitConfiguration X n r) :
    Injective p.val.1 := by
  intro i j hij
  by_contra hne
  have h := p.property.2 i j hne
  rw [hij, dist_self] at h
  exact (not_le.mpr hr) h

theorem configurationMeasure_atom_real [DecidableEq X] (p : HitConfiguration X n r) (x : X) :
    (configurationMeasure p {x}).toReal =
      ∑ i, if p.val.1 i = x then (p.val.2 i : ℝ) else 0 := by
  classical
  simp only [configurationMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    mem_singleton_iff, Pi.one_apply]
  rw [ENNReal.toReal_sum (fun i _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [ENNReal.toReal_ofReal (p.val.2 i).property.1]

theorem configurationMeasure_hasAtomicSquareBound (hr : 0 < r)
    (p : HitConfiguration X n r) : HasAtomicSquareBound (configurationMeasure p) := by
  classical
  intro F
  simp_rw [configurationMeasure_atom_real]
  exact (sum_sq_fibers_le p.val.1 (HitConfiguration.points_injective hr p) (fun i => (p.val.2 i : ℝ)) F).trans
    p.property.1

instance (p : HitConfiguration X n r) : IsFiniteMeasure (configurationMeasure p) :=
  ⟨lt_of_le_of_lt (configurationMeasure_mass_le p) (by simp)⟩

theorem meanConfigurationMeasure_atom_real
    (P : ProbabilityMeasure (HitConfiguration X n r)) (x : X) :
    (meanConfigurationMeasure P {x}).toReal =
      ∫ p, (configurationMeasure p {x}).toReal ∂(P : Measure (HitConfiguration X n r)) := by
  rw [meanConfigurationMeasure, Measure.bind_apply (measurableSet_singleton x)
    measurable_configurationMeasure.aemeasurable]
  exact (integral_toReal
    ((Measure.measurable_coe (measurableSet_singleton x)).comp
      measurable_configurationMeasure).aemeasurable
    (Eventually.of_forall fun p => measure_lt_top (configurationMeasure p) {x})).symm

theorem integrable_configuration_atom
    (P : ProbabilityMeasure (HitConfiguration X n r)) (x : X) :
    Integrable (fun p => (configurationMeasure p {x}).toReal)
      (P : Measure (HitConfiguration X n r)) := by
  apply Integrable.of_bound
    (((Measure.measurable_coe (measurableSet_singleton x)).comp
      measurable_configurationMeasure).ennreal_toReal.aestronglyMeasurable) n
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  change (configurationMeasure p {x}).toReal ≤ (n : ℝ)
  have hle : configurationMeasure p {x} ≤ n :=
    (measure_mono (subset_univ _)).trans (configurationMeasure_mass_le p)
  simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono (by simp) hle

theorem meanConfigurationMeasure_hasAtomicSquareBound (hr : 0 < r)
    (P : ProbabilityMeasure (HitConfiguration X n r)) :
    HasAtomicSquareBound (meanConfigurationMeasure P) := by
  classical
  intro F
  let a : F → HitConfiguration X n r → ℝ := fun x p => (configurationMeasure p {x.val}).toReal
  have hi (x : F) : Integrable (a x) (P : Measure (HitConfiguration X n r)) :=
    integrable_configuration_atom P x.val
  have hb (p : HitConfiguration X n r) : ∑ x : F, a x p ^ 2 ≤ 1 := by
    exact (Finset.sum_coe_sort F (fun x : X => (configurationMeasure p {x}).toReal ^ 2)).le.trans
      (configurationMeasure_hasAtomicSquareBound hr p F)
  have h := sum_sq_integrals_le_one P a hi hb
  simp_rw [meanConfigurationMeasure_atom_real]
  exact (Finset.sum_coe_sort F (fun x : X =>
    (∫ p, (configurationMeasure p {x}).toReal ∂(P : Measure (HitConfiguration X n r))) ^ 2)).symm.le.trans h

end CircleDomainRigidity

end

end OAI
