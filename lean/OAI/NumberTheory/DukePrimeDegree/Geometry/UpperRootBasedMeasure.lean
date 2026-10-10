import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootRebase

namespace OAI

/-! # Full upper-root measures normalized at their current point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
lemma zeroTime_mem_cube {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) {R : ℝ} (hR : 0 < R) : c.zeroTime ∈ c.cube R := by
  induction c with
  | done => exact mem_univ _
  | step a b hab hP hb tail ih =>
      change (tail.zeroTime, (0 : ℝ)) ∈ tail.cube R ×ˢ Ioo (-R) R
      exact ⟨ih, by constructor <;> linarith⟩
end EliminationChain

lemma centerUpperRootMeasure_unit_pos (n : ℕ) (ν : Measure (UpperRootTime n))
    (t : UpperRootTime n) (ht : t ∈ ν.support) :
    0 < centerUpperRootMeasure n ν t ((completeRootChain n).cube 1) := by
  rw [centerUpperRootMeasure, Measure.map_apply (upperRootRebase n t).measurable
    ((completeRootChain n).cube_open 1).measurableSet]
  apply (ν.mem_support_iff_forall t).mp ht
  apply IsOpen.mem_nhds (((completeRootChain n).cube_open 1).preimage
    (upperRootRebase n t).continuous)
  rw [Set.mem_preimage, upperRootRebase_self]
  exact (completeRootChain n).zeroTime_mem_cube zero_lt_one

def basedUpperRootMeasure (n : ℕ) (ν : Measure (UpperRootTime n)) (t : UpperRootTime n) :
    Measure (UpperRootTime n) :=
  anchorNormalize (centerUpperRootMeasure n ν t) ((completeRootChain n).cube 1)

lemma basedUpperRootMeasure_unit (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (t : UpperRootTime n) (ht : t ∈ ν.support) :
    basedUpperRootMeasure n ν t ((completeRootChain n).cube 1) = 1 := by
  let : IsLocallyFiniteMeasure (centerUpperRootMeasure n ν t) :=
    centerUpperRootMeasure_locallyFinite n ν t
  have hpos := centerUpperRootMeasure_unit_pos n ν t ht
  have hfin : centerUpperRootMeasure n ν t ((completeRootChain n).cube 1) < ∞ :=
    (measure_mono ((completeRootChain n).cube_subset_closedCube 1)).trans_lt
      ((completeRootChain n).closedCube_compact 1).measure_lt_top
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

lemma basedUpperRootMeasure_locallyFinite (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (t : UpperRootTime n) (ht : t ∈ ν.support) :
    IsLocallyFiniteMeasure (basedUpperRootMeasure n ν t) := by
  let : IsLocallyFiniteMeasure (centerUpperRootMeasure n ν t) :=
    centerUpperRootMeasure_locallyFinite n ν t
  have hpos := centerUpperRootMeasure_unit_pos n ν t ht
  constructor
  intro u
  obtain ⟨U,hu,hU,hfin⟩ := Measure.exists_isOpen_measure_lt_top (centerUpperRootMeasure n ν t) u
  refine ⟨U,hU.mem_nhds hu,?_⟩
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hpos) hfin

def centerUpperRootKernel {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) [IsSFiniteKernel κ] :
    Kernel (S × UpperRootTime n) (UpperRootTime n) where
  toFun z := centerUpperRootMeasure n (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight (UpperRootTime n) κ)
      (((continuous_upperRootRebase n).measurable.comp
        (measurable_fst.snd.prodMk measurable_snd)) hU)
    convert H using 1
    funext z
    exact Measure.map_apply (upperRootRebase n z.2).measurable hU

def basedUpperRootKernel {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) [IsSFiniteKernel κ] :
    Kernel (S × UpperRootTime n) (UpperRootTime n) where
  toFun z := basedUpperRootMeasure n (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    change Measurable (fun z =>
      (centerUpperRootKernel n κ z ((completeRootChain n).cube 1))⁻¹ * centerUpperRootKernel n κ z U)
    exact (centerUpperRootKernel n κ |>.measurable_coe
      ((completeRootChain n).cube_open 1).measurableSet).inv.mul
        (centerUpperRootKernel n κ |>.measurable_coe hU)

namespace UpperRootBox
variable {n : ℕ} {g : G n}

def basedLeaf (A : UpperRootBox n g) (R : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (z : UpperRootTransverse n × UpperRootTime n) : Measure (UpperRootTime n) :=
  basedUpperRootMeasure n (A.leafMeasure R μ z.1) z.2

lemma aemeasurable_basedLeaf (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    AEMeasurable (A.basedLeaf R μ) (A.coordinateMeasure μ) := by
  have he : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.regularLeafKernel R hAR μ hfree z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  exact (basedUpperRootKernel n (A.regularLeafKernel R hAR μ hfree)).measurable.aemeasurable.congr
    (he.mono fun z hz => congrArg (fun ν => basedUpperRootMeasure n ν z.2) hz)

theorem ae_basedLeaf_spec (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.basedLeaf R μ z) ∧
      A.basedLeaf R μ z ((completeRootChain n).cube 1) = 1 := by
  have hlf : ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [hlf,A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz ht
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz
  exact ⟨basedUpperRootMeasure_locallyFinite n _ _ ht, basedUpperRootMeasure_unit n _ _ ht⟩

end UpperRootBox
end DukePrimeDegree

end

end OAI
