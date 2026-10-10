import OAI.Probability.BenjaminiSchramm.PeakFiniteEnergy
import OAI.Probability.BenjaminiSchramm.LayerFreshSelection

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {E : Type*}

def finiteModification (F : Finset E) (B : Set (Set E)) : Set (Set E) :=
  ⋃ σ : Set (F : Set E), (forceOn (F : Set E) (Subtype.val '' σ)) ⁻¹' B

lemma forceOn_finitePattern_eq (F : Finset E) (σ : Set (F : Set E)) (ω : Set E)
    (hω : ω ∈ finiteBondPattern F (Subtype.val '' σ)) :
    forceOn (F : Set E) (Subtype.val '' σ) ω=ω := by
  ext e
  rw [mem_forceOn]
  by_cases he : e ∈ (F : Set E)
  · simpa only [he,ite_true] using (Iff.of_eq (hω e he)).symm
  · simp only [he,ite_false]

lemma finiteBondPattern_pairwise (F : Finset E) :
    Pairwise (fun σ τ : Set (F : Set E) => Disjoint
      (finiteBondPattern F (Subtype.val '' σ)) (finiteBondPattern F (Subtype.val '' τ))) := by
  intro σ τ hστ
  apply Set.disjoint_left.mpr
  intro ω hσ hτ
  apply hστ
  ext e
  have hh := (hσ e e.property).symm.trans (hτ e e.property)
  simpa only [Set.mem_image,Subtype.val_injective.eq_iff,exists_eq_right] using Iff.of_eq hh

lemma iUnion_finiteBondPattern (F : Finset E) :
    (⋃ σ : Set (F : Set E), finiteBondPattern F (Subtype.val '' σ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  refine Set.mem_iUnion.mpr ⟨Subtype.val ⁻¹' ω,?_⟩
  intro e he
  apply propext
  simp only [Set.mem_image,Set.mem_preimage]
  constructor
  · intro heω
    exact ⟨⟨e,he⟩,heω,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact hz

lemma forced_event_dependsOn_compl (F : Finset E) (σ : Set E) (B : Set (Set E)) :
    DependsOn (fun ω => forceOn (F : Set E) σ ω ∈ B) (F : Set E)ᶜ := by
  intro ω η hωη
  let ξ : Set E := {e | ω e}
  let ζ : Set E := {e | η e}
  have hh : forceOn (F : Set E) σ ξ=forceOn (F : Set E) σ ζ := by
    ext e
    rw [mem_forceOn,mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,ite_true]
    · simp only [he,ite_false]
      exact Iff.of_eq (hωη e he)
  exact congrArg (fun ξ : Set E => ξ ∈ B) hh

variable [Countable E]

lemma finiteModification_probability (p : unitInterval) (F : Finset E)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p (finiteModification F B) ≤ law p B := by
  let A (σ : Set (F : Set E)) := (forceOn (F : Set E) (Subtype.val '' σ)) ⁻¹' B
  let P (σ : Set (F : Set E)) := finiteBondPattern F (Subtype.val '' σ)
  have hmA (σ : Set (F : Set E)) : MeasurableSet (A σ) :=
    hB.preimage (measurable_forceOn _ _)
  have hcell (σ : Set (F : Set E)) :
      law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤ law p (B ∩ P σ) := by
    have he : A σ ∩ P σ=B ∩ P σ := by
      ext ω
      constructor
      · rintro ⟨ha,hp⟩
        exact ⟨forceOn_finitePattern_eq F σ ω hp ▸ ha,hp⟩
      · rintro ⟨hb,hp⟩
        refine ⟨?_,hp⟩
        change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
        rw [forceOn_finitePattern_eq F σ ω hp]
        exact hb
    have hh := fresh_finiteBondPattern_cell_lower p (F : Set E)ᶜ (A σ) (hmA σ)
      (forced_event_dependsOn_compl F _ B) F (by simp only [compl_compl]; exact Set.Subset.rfl)
        (Subtype.val '' σ)
    rwa [he] at hh
  have hd : Pairwise (fun σ τ : Set (F : Set E) => Disjoint (B ∩ P σ) (B ∩ P τ)) :=
    fun σ τ hστ => (finiteBondPattern_pairwise F hστ).mono Set.inter_subset_right Set.inter_subset_right
  have hp : (⋃ σ : Set (F : Set E), B ∩ P σ)=B := by
    rw [←Set.inter_iUnion,iUnion_finiteBondPattern,Set.inter_univ]
  calc
    _ ≤ ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*∑' σ : Set (F : Set E), law p (A σ) :=
      mul_le_mul' le_rfl (measure_iUnion_le A)
    _ = ∑' σ : Set (F : Set E), law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
      rw [ENNReal.tsum_mul_right,mul_comm]
    _ ≤ ∑' σ : Set (F : Set E), law p (B ∩ P σ) := ENNReal.tsum_le_tsum hcell
    _ = _ := by rw [←measure_iUnion hd (fun σ => hB.inter (measurableSet_finiteBondPattern F _)),hp]

theorem finite_energy_modification_bound (p : unitInterval) (F : Finset E)
    (A B : Set (Set E)) (hB : MeasurableSet B)
    (hmod : ∀ ω ∈ A, ∃ η ∈ B, ∀ e ∉ F, (e ∈ ω)=(e ∈ η)) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p A ≤ law p B := by
  apply (mul_le_mul' le_rfl (measure_mono ?_)).trans (finiteModification_probability p F B hB)
  intro ω hω
  obtain ⟨η,hη,hagree⟩ := hmod ω hω
  let σ : Set (F : Set E) := Subtype.val ⁻¹' η
  refine Set.mem_iUnion.mpr ⟨σ,?_⟩
  have hh : forceOn (F : Set E) (Subtype.val '' σ) ω=η := by
    ext e
    rw [mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,ite_true,Set.mem_image]
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro heη
        exact ⟨⟨e,he⟩,heη,rfl⟩
    · simpa only [he,ite_false] using Iff.of_eq (hagree e he)
  change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
  rw [hh]
  exact hη

end Percolation.BenjaminiSchramm

end

end OAI
