import OAI.Analysis.CircleDomains.Rigidity.TraceMaskAEPayment

namespace OAI

/-! Measurability and a uniform bound for the actual infinite primitive;
the raw endpoint only needs to be measurable. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) (n : ℕ) :
    finiteTraceMask (fun j z => cutoff j (φ z)) I y t n =
      finiteTraceMask cutoff I (φ y) t n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteTraceMask,ih]

 theorem infiniteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) :
    infiniteTraceMask (fun j z => cutoff j (φ z)) I y t =
      infiniteTraceMask cutoff I (φ y) t := by
  simp only [infiniteTraceMask,finiteTraceMask_comp]

 theorem infiniteTracePrimitive_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (a : ℝ) (y : Y) (t : ℝ) :
    infiniteTracePrimitive (fun j z => cutoff j (φ z)) I a y t =
      infiniteTracePrimitive cutoff I a (φ y) t := by
  simp only [infiniteTracePrimitive,infiniteTraceMask_comp]

 theorem infinite_masked_scalar_measurable {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (hcc : ∀ j, Continuous (cutoff j))
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j))
    (hIf : ∀ j, volume (I j) ≠ ∞) {b : X → ℝ} (hb : Measurable b) (a : ℝ) :
    Measurable (fun x => infiniteTracePrimitive cutoff I a x (b x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x => finiteTracePrimitive cutoff I a x (b x) n)
  · intro n
    exact (finiteTracePrimitive_continuous hc hcc hI hIf a n).measurable.comp
      (measurable_id.prodMk hb)
  · exact tendsto_pi_nhds.mpr (fun x => finiteTracePrimitive_tendsto hc hI x a (b x))

 theorem infiniteTracePrimitive_norm_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (a : ℝ) (x : X) (t : ℝ) :
    ‖infiniteTracePrimitive cutoff I a x t‖ ≤ ‖t-a‖ := by
  simpa only [infiniteTracePrimitive,intervalIntegral.integral_same,dist_zero_right,
    NNReal.coe_one,one_mul,Real.dist_eq,Real.norm_eq_abs] using
    (infiniteTracePrimitive_lipschitz hc hI x a).dist_le_mul t a

 theorem infinite_masked_scalar_memLp {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} (hbm : Measurable b) (hb : MemLp b 2 μ) (a : ℝ) :
    MemLp (fun x => infiniteTracePrimitive cutoff I a x (b x)) 2 μ := by
  apply (hb.sub (memLp_const a)).of_le
    (infinite_masked_scalar_measurable hc hcc hI hIf hbm a).aestronglyMeasurable
  exact Eventually.of_forall (fun x => infiniteTracePrimitive_norm_le hc hI a x (b x))

end CircleDomainRigidity

end

end OAI
