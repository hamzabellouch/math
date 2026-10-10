import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLeafMeasure

namespace OAI

/-! # Normalized remaining-subgroup leaf measures

The chosen measure is characterized by actual prefix-box conditionals,
and is independent of the exhaustion radius.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def IsNormalizedPrefixLeaf (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T)) (ν : Measure (c.Time)) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
    ν.restrict A.time = A.conditionalKernel μ s ∧
    ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
      s ∈ B.transverse → ν.restrict (c.remainingWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)



def leafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T)) : Measure (c.Time) :=
  if h : ∃ ν : Measure (c.Time), A.IsNormalizedPrefixLeaf R μ s ν then h.choose else 0

lemma leafMeasure_spec_of_exists (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T))
    (h : ∃ ν, A.IsNormalizedPrefixLeaf R μ s ν) :
    A.IsNormalizedPrefixLeaf R μ s (A.leafMeasure R μ s) := by
  simpa only [leafMeasure,dite_eq_left h] using h.choose_spec


theorem ae_leafMeasure_spec (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.IsNormalizedPrefixLeaf R μ s (A.leafMeasure R μ s) := by
  filter_upwards [A.ae_exists_prefixLeafMeasure R hAR μ hfree] with s hs
  exact A.leafMeasure_spec_of_exists R μ s hs

lemma IsNormalizedPrefixLeaf.unique (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T))
    (hs : Function.Injective (fun t : c.Time => Pfx.timeParam c hP hfinal g (s,t)))
    {ν ρ : Measure (c.Time)} (hν : A.IsNormalizedPrefixLeaf R μ s ν)
    (hρ : A.IsNormalizedPrefixLeaf R μ s ρ) : ν = ρ :=
  A.prefixLeafMeasure_unique R μ s hs ν ρ hν.2.2.2 hρ.2.2.2

lemma IsNormalizedPrefixLeaf.ne_zero (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T))
    {ν : Measure (c.Time)} (hν : A.IsNormalizedPrefixLeaf R μ s ν) : ν ≠ 0 := by
  intro hz
  have H := hν.2.1
  simp only [hz,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H


theorem ae_leafMeasure_restrict (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (D : RootPrefixBox Pfx c hP hfinal g) (hAD : A.time ⊆ D.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time := by
  let C := Pfx.longBoxFamily c hP hfinal g R
  let (m : ℕ) : Countable (C m) := (Pfx.longBoxFamily_countable c hP hfinal g R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = c.remainingWindow R m :=
    Pfx.longBoxFamily_time c hP hfinal g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (c.remainingWindow_mono R (Nat.zero_le m))
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
    A.ae_injective_slice_of_ae_free μ hfree,hp,base_anchor_restrict A D hAD μ]
      with s hs hi hp ha
  intro hsD
  refine ⟨(ha hsD).1,?_⟩
  apply measure_eq_of_restrictionChain (c.remainingWindow R) (c.remainingWindow_mono R)
    (c.remainingWindow_cover R)
  intro m
  obtain ⟨B,hBC,hsB⟩ := Pfx.longBoxFamily_covers c hP hfinal g R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hp m B' hsB hsD
  rw [hT m B'] at H
  calc
    ((A.leafMeasure R μ s).restrict D.time).restrict (c.remainingWindow R m) =
        ((A.leafMeasure R μ s).restrict (c.remainingWindow R m)).restrict D.time :=
      Measure.restrict_comm (c.remainingWindow_open R m).measurableSet
    _ = ((anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)).restrict D.time := by
      rw [hs.2.2.2 m B hBC hsB]
    _ = (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m ∩ D.time) := by
      rw [Measure.restrict_restrict D.time_open.measurableSet,inter_comm]
    _ = (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m ∩ D.time) := H
    _ = ((anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time).restrict (c.remainingWindow R m) :=
      (Measure.restrict_restrict (c.remainingWindow_open R m).measurableSet).symm


theorem ae_leafMeasure_radius_independent (A : RootPrefixBox Pfx c hP hfinal g) (R S : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0) (hAS : A.time ⊆ c.remainingWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    A.leafMeasure R μ =ᵐ[(A.coordinateMeasure μ).fst] A.leafMeasure S μ := by
  let C := Pfx.longBoxFamily c hP hfinal g S
  let (m : ℕ) : Countable (C m) := (Pfx.longBoxFamily_countable c hP hfinal g S m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = c.remainingWindow S m :=
    Pfx.longBoxFamily_time c hP hfinal g S m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAS.trans (c.remainingWindow_mono S (Nat.zero_le m))
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (A.leafMeasure R μ s).restrict (c.remainingWindow S m) =
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (c.remainingWindow S m) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B)] with s hs
    intro hsB
    simpa only [hT m B] using (hs hsB).2
  filter_upwards [A.ae_leafMeasure_spec S hAS μ hfree,
    A.ae_injective_slice_of_ae_free μ hfree,H] with s hs hi hR
  apply A.prefixLeafMeasure_unique S μ s hi _ _ _ hs.2.2.2
  intro m B hB hsB
  exact hR m ⟨B,hB⟩ hsB



end RootPrefixBox
end DukePrimeDegree

end

end OAI
