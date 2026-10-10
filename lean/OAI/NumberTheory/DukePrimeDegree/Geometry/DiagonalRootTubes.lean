import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingIntrinsicProduct
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootProductInformation

namespace OAI

/-! # Finite diagonal orbit tubes in a remaining root group

These are actual conjugation tubes, not assumed entropy partitions.
Their information is computed exactly; the passage from these tubes to
metric entropy is a separate step.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exp_scaled_abs_lt_iff (a ρ x : ℝ) :
    |Real.exp a * x| < Real.exp (-ρ) ↔ |x| < Real.exp (-(ρ+a)) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos a), mul_comm (Real.exp a),
    ←lt_div_iff₀ (Real.exp_pos a), ←Real.exp_sub,
    show -ρ-a = -(ρ+a) by ring]

lemma finite_exp_scaled_abs_lt_iff (a ρ x : ℝ) (N : ℕ) :
    (∀ k : ℕ, k ≤ N → |Real.exp (a*k) * x| < Real.exp (-ρ)) ↔
      |x| < Real.exp (-(ρ+(N:ℝ)*max a 0)) := by
  simp_rw [exp_scaled_abs_lt_iff]
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    constructor
    · intro h
      simpa only [mul_comm a] using h N le_rfl
    · intro h k hk
      apply h.trans_le
      apply Real.exp_le_exp.mpr
      have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
      nlinarith
  · rw [max_eq_right (le_of_not_ge ha),mul_zero,add_zero]
    constructor
    · intro h
      simpa only [Nat.cast_zero,mul_zero,add_zero] using h 0 (Nat.zero_le _)
    · intro h k _
      apply h.trans_le
      apply Real.exp_le_exp.mpr
      have hak : a*(k:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge ha) (Nat.cast_nonneg _)
      linarith

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

/-- The tube followed by the backward diagonal orbit, with every
remaining matrix entry bounded by `exp (-ρ)` through time `N`. -/
def remainingBackwardTube (_c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ) :
    Set (positiveRootGeneratedGroup (allPositiveRoots n \ P)) :=
  {u | ∀ k : ℕ, k ≤ N → ∀ p : ↥(allPositiveRoots n \ P),
    |(diagonalOneParameter ell hell k * u.val *
      diagonalOneParameter ell hell (-k)).val p.val.1 p.val.2| < Real.exp (-ρ)}

theorem remainingBackwardTube_eq_rectangle (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ) :
    c.remainingBackwardTube ell hell ρ N =
      (c.remainingGroupCoordinates hP hf).symm ''
        Set.pi univ (fun p => Metric.ball 0
          (Real.exp (-(ρ+(N:ℝ)*max (ell p.val.1-ell p.val.2) 0)))) := by
  let E := c.remainingGroupCoordinates hP hf
  ext u
  constructor
  · intro hu
    refine ⟨E u, ?_, E.symm_apply_apply u⟩
    intro p _
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero]
    rw [remainingGroupCoordinates_apply]
    apply (finite_exp_scaled_abs_lt_iff _ _ _ N).mp
    intro k hk
    simpa only [conjugation_entry] using hu k hk p
  · rintro ⟨v,hv,rfl⟩ k hk p
    rw [conjugation_entry]
    apply (finite_exp_scaled_abs_lt_iff _ _ _ N).mpr ?_ k hk
    have hp := hv p (mem_univ p)
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero] at hp
    have he : (E.symm v).val.val p.val.1 p.val.2 = v p := by
      rw [←c.remainingGroupCoordinates_apply hP hf]
      exact congrFun (E.apply_symm_apply v) p
    change |(E.symm v).val.val p.val.1 p.val.2| < _
    rw [he]
    exact hp

theorem remainingBackwardTube_measurableSet (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ) :
    MeasurableSet (c.remainingBackwardTube ell hell ρ N) := by
  rw [c.remainingBackwardTube_eq_rectangle hP hf]
  apply (c.remainingGroupCoordinates hP hf).symm.measurableEmbedding.measurableSet_image.mpr
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => Metric.isOpen_ball.measurableSet)

/-- Negative log mass of an actual finite-time diagonal tube in the
intrinsic remaining-subgroup leaf. -/
def remainingBackwardTubeInformation (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) : ℝ :=
  -Real.log ((c.remainingIntrinsicProduct hP hf μ x)
    (c.remainingBackwardTube ell hell ρ N)).toReal

end EliminationChain

namespace EliminationChain
variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}

theorem remainingBackwardTubeInformation_eq (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ] (x : X (d+1)) :
    c.remainingBackwardTubeInformation hP hf ell hell ρ N μ x =
      rootProductInformation d (fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.1)
        (fun p => p.val.2)
        (fun p => ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)
        μ (fun p => ρ+(N:ℝ)*max (ell p.val.1-ell p.val.2) 0) x := by
  let E := c.remainingGroupCoordinates hP hf
  rw [remainingBackwardTubeInformation,c.remainingBackwardTube_eq_rectangle hP hf]
  have hB : MeasurableSet (Set.pi univ (fun p : ↥(allPositiveRoots (d+1) \ P) =>
      Metric.ball (0:ℝ) (Real.exp (-(ρ+(N:ℝ)*max (ell p.val.1-ell p.val.2) 0))))) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => Metric.isOpen_ball.measurableSet)
  rw [remainingIntrinsicProduct,Measure.map_apply E.symm.measurable
    (E.symm.measurableEmbedding.measurableSet_image.mpr hB),E.symm.injective.preimage_image]
  rfl

theorem integrable_remainingBackwardTubeInformation (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    Integrable (c.remainingBackwardTubeInformation hP hf ell hell ρ N μ) μ := by
  have he := funext (c.remainingBackwardTubeInformation_eq hP hf ell hell ρ N μ)
  rw [he]
  exact integrable_rootProductInformation d _ _ _ μ hA _

/-- The mean tube information is linear in time, with a constant
depending only on its initial radius. -/
theorem integral_remainingBackwardTubeInformation (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    (∫ x, c.remainingBackwardTubeInformation hP hf ell hell ρ N μ x ∂μ) =
      ρ * (∑ p : ↥(allPositiveRoots (d+1) \ P), canonicalRootCoefficient d μ p.val.1 p.val.2) +
      (N:ℝ) * (∑ p : ↥(allPositiveRoots (d+1) \ P),
        max (ell p.val.1-ell p.val.2) 0 * canonicalRootCoefficient d μ p.val.1 p.val.2) := by
  simp_rw [c.remainingBackwardTubeInformation_eq hP hf]
  rw [integral_rootProductInformation d _ _ _ μ hA]
  simp only [add_mul,Finset.sum_add_distrib,←Finset.mul_sum,mul_assoc]

/-- Every fixed initial radius gives the same mean information rate. -/
theorem tendsto_mean_remainingBackwardTubeInformation (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    Tendsto (fun N : ℕ =>
      (∫ x, c.remainingBackwardTubeInformation hP hf ell hell ρ N μ x ∂μ) / (N:ℝ))
      atTop (𝓝 (∑ p : ↥(allPositiveRoots (d+1) \ P),
        max (ell p.val.1-ell p.val.2) 0 * canonicalRootCoefficient d μ p.val.1 p.val.2)) := by
  let a := ρ * (∑ p : ↥(allPositiveRoots (d+1) \ P),
    canonicalRootCoefficient d μ p.val.1 p.val.2)
  let b := ∑ p : ↥(allPositiveRoots (d+1) \ P),
    max (ell p.val.1-ell p.val.2) 0 * canonicalRootCoefficient d μ p.val.1 p.val.2
  have H : Tendsto (fun N : ℕ => a/(N:ℝ)+b) atTop (𝓝 b) := by
    simpa only [zero_add] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => a/(N:ℝ)) atTop (𝓝 0)).add tendsto_const_nhds
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  rw [c.integral_remainingBackwardTubeInformation hP hf ell hell ρ N μ hA]
  change a/(N:ℝ)+b = (a+(N:ℝ)*b)/(N:ℝ)
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

end EliminationChain
end DukePrimeDegree

end

end OAI
