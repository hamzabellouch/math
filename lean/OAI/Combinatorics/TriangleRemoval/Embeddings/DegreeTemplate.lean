import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RerootTemplate

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def degreeTemplate : RootedTemplate 2 where
  edges := {{0,1}}
  roots := {0}
  simple := by decide
  independent := by decide

lemma degreeTemplate_balanced : RootedTwoBalanced degreeTemplate := by
  unfold RootedTwoBalanced degreeTemplate
  decide

def degreeRoot {n : ℕ} (u : Fin n) : {v // v ∈ degreeTemplate.roots} ↪ Fin n where
  toFun := fun _ => u
  inj' := by
    intro a b _
    apply Subtype.ext
    exact (Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm

lemma degree_rooted_zero {n : ℕ} (u : Fin n) (φ : RootedInjection degreeTemplate (degreeRoot u)) :
    φ.val 0 = u := φ.property ⟨0,by decide⟩

lemma degree_image_subset {n : ℕ} (u : Fin n) (φ : RootedInjection degreeTemplate (degreeRoot u))
    (G : Graph n) : imageEdges degreeTemplate φ.val ⊆ G ↔ {u,φ.val 1} ∈ G := by
  simp [imageEdges,degreeTemplate,degree_rooted_zero u φ]

lemma degree_restrict_injective {n : ℕ} (u : Fin n) :
    Function.Injective (fun φ : RootedInjection degreeTemplate (degreeRoot u) => φ.val 1) := by
  intro φ χ h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  fin_cases i
  · exact (degree_rooted_zero u φ).trans (degree_rooted_zero u χ).symm
  · exact h

lemma degree_restrict_surj {n : ℕ} (u v : Fin n) (hne : u ≠ v) :
    ∃ φ : RootedInjection degreeTemplate (degreeRoot u), φ.val 1 = v := by
  let f : Fin 2 → Fin n := ![u,v]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  refine ⟨⟨⟨f,hf⟩,?_⟩,rfl⟩
  intro r
  have hr : r.val = 0 := Finset.mem_singleton.mp r.property
  change f r.val = u
  rw [hr]
  rfl

theorem degree_rootedCount {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    rootedCount degreeTemplate (degreeRoot u) G = currentDegree G u := by
  let A := Finset.univ.filter (fun φ : RootedInjection degreeTemplate (degreeRoot u) =>
    imageEdges degreeTemplate φ.val ⊆ G)
  have hA : rootedCount degreeTemplate (degreeRoot u) G = (A.card : ℝ) := by
    simp [rootedCount,copyCount,intact,A]
  rw [hA]
  unfold currentDegree
  congr 1
  apply Finset.card_bij (fun φ _ => φ.val 1)
  · intro φ hφ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(degree_image_subset u φ G).mp (Finset.mem_filter.mp hφ).2⟩
  · intro φ _ χ _ h
    exact degree_restrict_injective u h
  · intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    have hne : u ≠ v := by
      intro h
      have hh := mem_completeGraph.mp (hG hv')
      simp [h] at hh
    obtain ⟨φ,hφ⟩ := degree_restrict_surj u v hne
    refine ⟨φ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hφ⟩
    exact (degree_image_subset u φ G).mpr (hφ.symm ▸ hv')

@[simp] theorem degree_rootedScaling (n : ℕ) (p : ℝ) :
    rootedScaling degreeTemplate n p = (n : ℝ)*p := by
  simp [rootedScaling,degreeTemplate]

end SharpTerminalLeave
end
end

end OAI
