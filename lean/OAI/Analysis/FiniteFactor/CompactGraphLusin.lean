import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

/-- A function whose graph is compact above Q is continuous on Q. -/
theorem continuousOn_of_compact_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} {K : Set (X × Y)} (hK : IsCompact K)
    (hgraph : ∀ z ∈ K, f z.1 = z.2) : ContinuousOn f (Prod.fst '' K) := by
  let Q := Prod.fst '' K
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → X := fun z => z.1.1
  have hg : Continuous g := continuous_fst.comp continuous_subtype_val
  have hi : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    apply Prod.ext h
    exact (hgraph z.1 z.2).symm.trans ((congrArg f h).trans (hgraph w.1 w.2))
  have hmem (x : Q) : (x.1, f x.1) ∈ K := by
    obtain ⟨z,hz,hx⟩ := x.2
    have he : (x.1, f x.1) = z := by
      apply Prod.ext hx.symm
      simpa only [← hx] using hgraph z hz
    rwa [he]
  let inv : Q → K := fun x => ⟨(x.1, f x.1), hmem x⟩
  have hinv : Continuous inv :=
    (hg.isClosedEmbedding hi).isEmbedding.isInducing.continuous_iff.mpr continuous_subtype_val
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hinv))

/-- Lusin's theorem on Polish spaces, obtained from compact subsets of the
measurable graph. The compact set can be required to lie in a prescribed
Borel conull set. -/
theorem exists_compact_lusin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {s : Set X} (hs : MeasurableSet s)
    (hfull : ∀ᵐ x ∂μ, x ∈ s) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ μ Qᶜ < ε ∧ ContinuousOn f Q := by
  let graph : X → X × Y := fun x => (x,f x)
  have hgraph : Measurable graph := measurable_id.prodMk hf
  let G : Set (X × Y) := {z | z.1 ∈ s ∧ f z.1 = z.2}
  have hG : MeasurableSet G :=
    (hs.preimage measurable_fst).inter (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd)
  let ν := μ.map graph
  obtain ⟨K,hKG,hK,hsmall⟩ := hG.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top _ _) hε
  let Q : Set X := Prod.fst '' K
  have hQ : IsCompact Q := hK.image continuous_fst
  have hQs : Q ⊆ s := by
    rintro x ⟨z,hz,rfl⟩
    exact (hKG hz).1
  have hmem (x : X) : graph x ∈ K ↔ x ∈ Q := by
    constructor
    · intro hx; exact ⟨graph x,hx,rfl⟩
    · rintro ⟨z,hz,hx⟩
      have he : graph x = z := by
        apply Prod.ext hx.symm
        simpa only [graph, ← hx] using (hKG hz).2
      rwa [he]
  have hpre : graph ⁻¹' (G \ K) = s \ Q := by
    ext x
    change ((x ∈ s ∧ f x = f x) ∧ graph x ∉ K) ↔ (x ∈ s ∧ x ∉ Q)
    rw [hmem]
    simp
  have hsmall' : μ (s \ Q) < ε := by
    have he : ν (G \ K) = μ (s \ Q) := by
      rw [Measure.map_apply hgraph (hG.diff hK.isClosed.measurableSet), hpre]
    rwa [he] at hsmall
  have heq : μ (s \ Q) = μ Qᶜ := by
    apply measure_congr
    filter_upwards [hfull] with x hx
    apply propext
    change (x ∈ s ∧ x ∉ Q) ↔ x ∉ Q
    simp [hx]
  refine ⟨Q,hQs,hQ,heq ▸ hsmall',?_⟩
  exact continuousOn_of_compact_graph hK (fun z hz => (hKG hz).2)

end
end FiniteFactor

end OAI
