import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLeafMeasure
import OAI.NumberTheory.PrimePackets.RootLeaves

namespace OAI

/-!
# Chosen normalized full upper-root leaf measures

The projectively compatible box conditionals determine locally finite
measures on all upper-root times. Their normalization is independent of
the exhaustion radius and their restrictions agree with every larger box.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox
variable {n : ℕ} {g : G n}

def IsNormalizedUpperRootLeaf (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n) (ν : Measure (UpperRootTime n)) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
    ν.restrict A.time = A.conditionalKernel μ s ∧
    ∀ (m : ℕ) (B : UpperRootBox n g), B ∈ upperRootLongBoxFamily n g R m →
      s ∈ B.transverse → ν.restrict (upperRootWindow n R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m)



def leafMeasure (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n) : Measure (UpperRootTime n) :=
  if h : ∃ ν : Measure (UpperRootTime n), A.IsNormalizedUpperRootLeaf R μ s ν then h.choose else 0

lemma leafMeasure_spec_of_exists (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n)
    (h : ∃ ν, A.IsNormalizedUpperRootLeaf R μ s ν) :
    A.IsNormalizedUpperRootLeaf R μ s (A.leafMeasure R μ s) := by
  simpa only [leafMeasure,dite_eq_left h] using h.choose_spec


theorem ae_leafMeasure_spec (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.IsNormalizedUpperRootLeaf R μ s (A.leafMeasure R μ s) := by
  filter_upwards [A.ae_exists_upperRootLeafMeasure R hAR μ hfree] with s hs
  exact A.leafMeasure_spec_of_exists R μ s hs

lemma IsNormalizedUpperRootLeaf.unique (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n)
    (hs : Function.Injective (fun t : UpperRootTime n => upperRootQuotientParam n g (s,t)))
    {ν ρ : Measure (UpperRootTime n)} (hν : A.IsNormalizedUpperRootLeaf R μ s ν)
    (hρ : A.IsNormalizedUpperRootLeaf R μ s ρ) : ν = ρ :=
  A.upperRootLeafMeasure_unique R μ s hs ν ρ hν.2.2.2 hρ.2.2.2

lemma IsNormalizedUpperRootLeaf.ne_zero (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n)
    {ν : Measure (UpperRootTime n)} (hν : A.IsNormalizedUpperRootLeaf R μ s ν) : ν ≠ 0 := by
  intro hz
  have H := hν.2.1
  simp only [hz,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H


theorem ae_leafMeasure_restrict (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (D : UpperRootBox n g) (hAD : A.time ⊆ D.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time := by
  let C := upperRootLongBoxFamily n g R
  let (m : ℕ) : Countable (C m) := (upperRootLongBoxFamily_countable n g R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = upperRootWindow n R m :=
    upperRootLongBoxFamily_time n g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (upperRootWindow_mono n R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse → s ∈ D.transverse →
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) =
          (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [base_overlap_anchorNormalize A B.val D (hinc m B) hAD μ] with s hs
    exact fun hB hD => (hs hB hD).2.2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_upperRoot_slice_of_ae_free μ hfree,hp,base_anchor_restrict A D hAD μ]
      with s hs hi hp ha
  intro hsD
  refine ⟨(ha hsD).1,?_⟩
  apply measure_eq_of_restrictionChain (upperRootWindow n R) (upperRootWindow_mono n R)
    (upperRootWindow_cover n R)
  intro m
  obtain ⟨B,hBC,hsB⟩ := upperRootLongBoxFamily_covers n g R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hp m B' hsB hsD
  rw [hT m B'] at H
  calc
    ((A.leafMeasure R μ s).restrict D.time).restrict (upperRootWindow n R m) =
        ((A.leafMeasure R μ s).restrict (upperRootWindow n R m)).restrict D.time :=
      Measure.restrict_comm (upperRootWindow_open n R m).measurableSet
    _ = ((anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m)).restrict D.time := by
      rw [hs.2.2.2 m B hBC hsB]
    _ = (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m ∩ D.time) := by
      rw [Measure.restrict_restrict D.time_open.measurableSet,inter_comm]
    _ = (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m ∩ D.time) := H
    _ = ((anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time).restrict (upperRootWindow n R m) :=
      (Measure.restrict_restrict (upperRootWindow_open n R m).measurableSet).symm


theorem ae_leafMeasure_radius_independent (A : UpperRootBox n g) (R S : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0) (hAS : A.time ⊆ upperRootWindow n S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    A.leafMeasure R μ =ᵐ[(A.coordinateMeasure μ).fst] A.leafMeasure S μ := by
  let C := upperRootLongBoxFamily n g S
  let (m : ℕ) : Countable (C m) := (upperRootLongBoxFamily_countable n g S m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = upperRootWindow n S m :=
    upperRootLongBoxFamily_time n g S m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAS.trans (upperRootWindow_mono n S (Nat.zero_le m))
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (A.leafMeasure R μ s).restrict (upperRootWindow n S m) =
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (upperRootWindow n S m) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B)] with s hs
    intro hsB
    simpa only [hT m B] using (hs hsB).2
  filter_upwards [A.ae_leafMeasure_spec S hAS μ hfree,
    A.ae_injective_upperRoot_slice_of_ae_free μ hfree,H] with s hs hi hR
  apply A.upperRootLeafMeasure_unique S μ s hi _ _ _ hs.2.2.2
  intro m B hB hsB
  exact hR m ⟨B,hB⟩ hsB


end UpperRootBox
end DukePrimeDegree

end

end OAI
