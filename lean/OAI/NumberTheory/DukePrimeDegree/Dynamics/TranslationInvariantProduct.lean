import OAI.NumberTheory.DukePrimeDegree.Dynamics.TranslationInvariantSlices
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-! # Splitting off a translation-invariant neutral factor -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

def firstCoordinateSlice (ρ : Measure (Z × V)) (K : Set V) : Measure Z :=
  (ρ.restrict (univ ×ˢ K)).map Prod.fst

lemma firstCoordinateSlice_apply (ρ : Measure (Z × V)) (K : Set V)
    {A : Set Z} (hA : MeasurableSet A) :
    firstCoordinateSlice ρ K A=ρ (A ×ˢ K) := by
  rw [firstCoordinateSlice,Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]

variable [TopologicalSpace Z] [TopologicalSpace V] [BorelSpace Z] [BorelSpace V]
  [T2Space Z] [T2Space V]

omit [BorelSpace V] [T2Space V] in
theorem firstCoordinateSlice_finiteOnCompacts (ρ : Measure (Z × V))
    [IsFiniteMeasureOnCompacts ρ] {K : Set V} (hK : IsCompact K) :
    IsFiniteMeasureOnCompacts (firstCoordinateSlice ρ K) := by
  constructor
  intro A hA
  rw [firstCoordinateSlice_apply ρ K hA.measurableSet]
  exact (hA.prod hK).measure_lt_top

theorem translationInvariant_eq_product
    [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [SigmaCompactSpace Z]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure]
    (K : Set V) (hK : IsCompact K) (hηK : η K=1) :
    ρ=(firstCoordinateSlice ρ K).prod η := by
  let τ := firstCoordinateSlice ρ K
  let := firstCoordinateSlice_finiteOnCompacts ρ hK
  apply Eq.symm
  apply Measure.prod_eq
  intro A B hA hB
  let An : ℕ → Set Z := fun k => A ∩ compactCovering Z k
  have hAn (k : ℕ) : MeasurableSet (An k) :=
    hA.inter (isCompact_compactCovering Z k).measurableSet
  have hAnc (k : ℕ) : IsCompact (closure (An k)) :=
    (isCompact_compactCovering Z k).of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_right (isCompact_compactCovering Z k).isClosed)
  have hrect (k : ℕ) : ρ (An k ×ˢ B)=τ (An k)*η B := by
    obtain ⟨c,hc⟩ := translationInvariant_rectangle ρ (hAn k) (hAnc k) hinv η
    have ht : τ (An k)=(c : ℝ≥0∞) := by
      rw [firstCoordinateSlice_apply ρ K (hAn k),hc K hK.measurableSet,hηK,mul_one]
    rw [hc B hB,ht]
  have hmono : Monotone An := fun i j hij =>
    inter_subset_inter Subset.rfl (compactCovering_subset Z hij)
  have hunion : (⋃ k, An k)=A := by
    simp only [An,←inter_iUnion,iUnion_compactCovering,inter_univ]
  have hprodmono : Monotone (fun k => An k ×ˢ B) := fun i j hij =>
    Set.prod_mono (hmono hij) Subset.rfl
  have hprodunion : (⋃ k, An k ×ˢ B)=A ×ˢ B := by
    rw [←iUnion_prod_const,hunion]
  calc
    ρ (A ×ˢ B)=⨆ k, ρ (An k ×ˢ B) := by
      rw [←hprodunion,hprodmono.measure_iUnion]
    _ = ⨆ k, τ (An k)*η B := iSup_congr hrect
    _ = (⨆ k, τ (An k))*η B := (ENNReal.iSup_mul _ _).symm
    _ = τ A*η B := by rw [←hmono.measure_iUnion,hunion]

end DukePrimeDegree

end

end OAI
