import Mathlib.Data.List.Chain
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

/-! Disjoint reflected copies of the exterior of finitely many disjoint caps.
Only the elementary side swapping and involution of each reflection are used. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [TopologicalSpace X]

def reflectionWord (R : I → X ≃ₜ X) : List I → X ≃ₜ X
  | [] => Homeomorph.refl X
  | i::w => (reflectionWord R w).trans (R i)

def reflectionTile (R : I → X ≃ₜ X) (K : I → Set X) (w : List I) : Set X :=
  reflectionWord R w '' (⋃i,K i)ᶜ

@[simp] lemma reflectionTile_nil (R : I → X ≃ₜ X) (K : I → Set X) :
    reflectionTile R K []=(⋃i,K i)ᶜ := by
  simp [reflectionTile,reflectionWord]

lemma reflectionTile_cons (R : I → X ≃ₜ X) (K : I → Set X) (i : I) (w : List I) :
    reflectionTile R K (i::w)=R i '' reflectionTile R K w := by
  change ((R i) ∘ reflectionWord R w) '' (⋃j,K j)ᶜ=_
  rw [image_comp]
  rfl

lemma reflectionTile_cons_subset (R : I → X ≃ₜ X) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i) (i : I) (w : List I)
    (hw : (i::w).IsChain (·≠·)) : reflectionTile R K (i::w)⊆U i := by
  induction w generalizing i with
  | nil =>
    rw [reflectionTile_cons,reflectionTile_nil]
    exact (image_mono (compl_subset_compl.mpr (subset_iUnion K i))).trans (hr i)
  | cons j w ih =>
    obtain ⟨hij,ht⟩ := List.isChain_cons_cons.mp hw
    rw [reflectionTile_cons]
    apply Subset.trans (image_mono ?_) (hr i)
    intro x hx hxi
    exact Set.disjoint_left.mp (hd hij) hxi (hUK j (ih j ht hx))

lemma reflectionTiles_pairwise_disjoint (R : I → X ≃ₜ X) (K U : I → Set X)
    (hUK : ∀i,U i⊆K i) (hd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hr : ∀i,R i '' (K i)ᶜ⊆U i) :
    Pairwise (fun w v : {w : List I // w.IsChain (·≠·)} =>
      Disjoint (reflectionTile R K w.val) (reflectionTile R K v.val)) := by
  classical
  have hbase (i : I) : Disjoint ((⋃j,K j)ᶜ) (U i) := by
    apply Set.disjoint_left.mpr
    intro x hx hi
    exact hx (mem_iUnion.mpr ⟨i,hUK i hi⟩)
  have haux (w : List I) : ∀v : List I,w.IsChain (·≠·) → v.IsChain (·≠·) → w≠v →
      Disjoint (reflectionTile R K w) (reflectionTile R K v) := by
    induction w with
    | nil =>
      intro v _ hv hne
      cases v with
      | nil => exact (hne rfl).elim
      | cons j v =>
        rw [reflectionTile_nil]
        exact (hbase j).mono_right (reflectionTile_cons_subset R K U hUK hd hr j v hv)
    | cons i w ih =>
      intro v hw hv hne
      cases v with
      | nil =>
        rw [reflectionTile_nil]
        exact ((hbase i).mono_right (reflectionTile_cons_subset R K U hUK hd hr i w hw)).symm
      | cons j v =>
        by_cases hij : i=j
        · subst j
          have hn : w≠v := fun he => hne (congrArg (List.cons i) he)
          have hdis := ih v (List.isChain_cons.mp hw).2 (List.isChain_cons.mp hv).2 hn
          rw [reflectionTile_cons,reflectionTile_cons]
          apply Set.disjoint_left.mpr
          rintro y ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
          have hba := (R i).injective he
          exact Set.disjoint_left.mp hdis ha (hba ▸ hb)
        · exact (hd hij).mono
            ((reflectionTile_cons_subset R K U hUK hd hr i w hw).trans (hUK i))
            ((reflectionTile_cons_subset R K U hUK hd hr j v hv).trans (hUK j))
  intro w v hne
  exact haux w.val v.val w.property v.property (fun he => hne (Subtype.ext he))

end CircleDomainRigidity

end

end OAI
