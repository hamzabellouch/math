import OAI.Dynamics.StandardMap.GraphUniqueness

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy

lemma continuous_factor_compact {A B C : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [T2Space B] [TopologicalSpace C]
    (p : A → B) (f : A → C) (g : B → C)
    (hp : Continuous p) (hsurj : Function.Surjective p) (hf : Continuous f)
    (hfg : ∀ x, g (p x)=f x) : Continuous g := by
  apply (Topology.IsQuotientMap.of_surjective_continuous hsurj hp).continuous_iff.mpr
  exact hf.congr (fun x => (hfg x).symm)

lemma compact_graph_relabel {A : Type*} [TopologicalSpace A]
    (S : Set A) (I : Set ℝ) (hs : IsCompact S) (hI : IsCompact I)
    (y₀ : ℝ) (hy₀ : y₀ ∈ I) (b : A → ℝ → ℝ)
    (hb : ContinuousOn (fun z : A × ℝ => b z.1 z.2) (S ×ˢ I))
    (hunique : ∀ z ∈ S, ∀ w ∈ S, b z y₀=b w y₀ → ∀ y ∈ I, b z y=b w y) :
    ∃ E : Set ℝ, ∃ X : ℝ × ℝ → ℝ,
      IsCompact E ∧ E=(fun z => b z y₀) '' S ∧
      ContinuousOn X (E ×ˢ I) ∧
      (∀ s ∈ E, X (s,y₀)=s) ∧
      (∀ z ∈ S, ∀ y ∈ I, X (b z y₀,y)=b z y) ∧
      (∀ s ∈ E, ∃ z ∈ S, ∀ y, X (s,y)=b z y) := by
  classical
  let l : A → ℝ := fun z => b z y₀
  let E := l '' S
  have hl : ContinuousOn l S := hb.comp
    (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz,hy₀⟩)
  have hE : IsCompact E := hs.image_of_continuousOn hl
  let rep : E → S := fun s => ⟨(show ∃ z ∈ S, l z = s.val from s.property).choose,
    (show ∃ z ∈ S, l z = s.val from s.property).choose_spec.1⟩
  have hrep (s : E) : l (rep s)=s := (show ∃ z ∈ S, l z = s.val from s.property).choose_spec.2
  let X : ℝ × ℝ → ℝ := fun z => if h : z.1 ∈ E then b (rep ⟨z.1,h⟩) z.2 else 0
  have hX (z : A) (hz : z ∈ S) (y : ℝ) (hy : y ∈ I) : X (l z,y)=b z y := by
    have hzl : l z ∈ E := mem_image_of_mem l hz
    simp only [X,dite_eq_left hzl]
    exact hunique _ (rep ⟨l z,hzl⟩).property z hz (hrep ⟨l z,hzl⟩) y hy
  let p : (S ×ˢ I) → (E ×ˢ I) := fun z => ⟨(l z.val.1,z.val.2),
    mem_image_of_mem l z.property.1,z.property.2⟩
  have hpc : Continuous p := by
    apply Continuous.subtype_mk
    have hp1 : Continuous (fun z : S ×ˢ I => (⟨z.val.1,z.property.1⟩ : S)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    exact (hl.domRestrict.comp hp1).prodMk (continuous_snd.comp continuous_subtype_val)
  have hps : Function.Surjective p := by
    intro z
    obtain ⟨w,hw,hlw⟩ := z.property.1
    refine ⟨⟨(w,z.val.2),hw,z.property.2⟩,?_⟩
    apply Subtype.ext
    change (l w,z.val.2)=(z.val.1,z.val.2)
    rw [hlw]
  let : CompactSpace (S ×ˢ I) := isCompact_iff_compactSpace.mp (hs.prod hI)
  have hcont : Continuous (fun z : E ×ˢ I => X z) := by
    apply continuous_factor_compact p (fun z : S ×ˢ I => b z.val.1 z.val.2)
      (fun z : E ×ˢ I => X z) hpc hps hb.domRestrict
    intro z
    exact hX z.val.1 z.property.1 z.val.2 z.property.2
  refine ⟨E,X,hE,rfl,continuousOn_iff_continuous_domRestrict.mpr hcont,?_,hX,?_⟩
  · intro s hs'
    obtain ⟨z,hz,rfl⟩ := hs'
    exact hX z hz y₀ hy₀
  · intro s hs'
    refine ⟨rep ⟨s,hs'⟩,(rep ⟨s,hs'⟩).property,?_⟩
    intro y
    simp only [X,dite_eq_left hs']
end StandardMapEntropy

end OAI
