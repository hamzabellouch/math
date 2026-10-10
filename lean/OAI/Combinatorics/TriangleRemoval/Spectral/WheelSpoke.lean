import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RerootTemplate

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma cycleNext_val {j : ℕ} (i : Fin j) :
    (cycleNext i).val = if i.val+1 < j then i.val+1 else 0 := by
  unfold cycleNext
  dsimp
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val+1 = j := by omega
    simp [he]

lemma cycleNext_injective (j : ℕ) : Function.Injective (@cycleNext j) := by
  intro i k h
  have hh := congrArg Fin.val h
  rw [cycleNext_val,cycleNext_val] at hh
  apply Fin.ext
  split_ifs at hh <;> omega

lemma cycleNext_ne {j : ℕ} (hj : 2 ≤ j) (i : Fin j) : cycleNext i ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  rw [cycleNext_val] at hh
  split_ifs at hh <;> omega

lemma cycleNext_twice_ne {j : ℕ} (hj : 3 ≤ j) (i : Fin j) :
    cycleNext (cycleNext i) ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  have h1 := cycleNext_val i
  have h2 := cycleNext_val (cycleNext i)
  split_ifs at h1 h2 <;> omega

def wheelSpoke {j : ℕ} (i : Fin j) : Finset (Fin (j+1)) := {0,i.succ}
def wheelRim {j : ℕ} (i : Fin j) : Finset (Fin (j+1)) := {i.succ,(cycleNext i).succ}

lemma wheelSpoke_injective (j : ℕ) : Function.Injective (@wheelSpoke j) := by
  intro i k h
  have hh : i.succ ∈ wheelSpoke k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [wheelSpoke,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh
  · exact (Fin.succ_ne_zero i hh).elim
  · exact Fin.succ_injective _ hh

lemma wheelRim_injective {j : ℕ} (hj : 3 ≤ j) : Function.Injective (@wheelRim j) := by
  intro i k h
  have ha : i.succ ∈ wheelRim k := h ▸ Finset.mem_insert_self _ _
  have hb : (cycleNext i).succ ∈ wheelRim k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [wheelRim,Finset.mem_insert,Finset.mem_singleton,Fin.succ_inj] at ha hb
  rcases ha with rfl | ha
  · rfl
  rcases hb with hb | hb
  · have hh : cycleNext (cycleNext k) = k := by rw [← ha,hb]
    exact (cycleNext_twice_ne hj k hh).elim
  · exact ((cycleNext_ne (by omega) i) (hb.trans ha.symm)).elim

lemma wheelSpoke_ne_rim {j : ℕ} (i k : Fin j) : wheelSpoke i ≠ wheelRim k := by
  intro h
  have hh : (0 : Fin (j+1)) ∈ wheelRim k := h ▸ Finset.mem_insert_self _ _
  simp only [wheelRim,Finset.mem_insert,Finset.mem_singleton,(Ne.symm (Fin.succ_ne_zero _)),or_self] at hh

def wheelTemplate (j : ℕ) (hj : 3 ≤ j) : RootedTemplate (j+1) where
  edges := Finset.univ.image wheelSpoke ∪ Finset.univ.image wheelRim
  roots := {0}
  simple := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      simp [wheelSpoke,(Ne.symm (Fin.succ_ne_zero _))]
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hne : i.succ ≠ (cycleNext i).succ := by
        intro h; exact cycleNext_ne (by omega) i (Fin.succ_injective _ h).symm
      simp [wheelRim,hne]
  independent := by
    intro e he hsub
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hh := hsub (show i.succ ∈ wheelSpoke i by simp [wheelSpoke])
      simp at hh
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hh := hsub (show i.succ ∈ wheelRim i by simp [wheelRim])
      simp at hh

@[simp] lemma wheelTemplate_roots_card (j : ℕ) (hj : 3 ≤ j) :
    (wheelTemplate j hj).roots.card = 1 := Finset.card_singleton _

@[simp] lemma wheelTemplate_edges_card (j : ℕ) (hj : 3 ≤ j) :
    (wheelTemplate j hj).edges.card = 2*j := by
  have hd : Disjoint (Finset.univ.image (@wheelSpoke j)) (Finset.univ.image (@wheelRim j)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hf
    exact wheelSpoke_ne_rim i k hk.symm
  rw [wheelTemplate,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (wheelSpoke_injective j),
    Finset.card_image_of_injective _ (wheelRim_injective hj)]
  simp
  omega

lemma wheelTemplate_balanced (j : ℕ) (hj : 3 ≤ j) : RootedTwoBalanced (wheelTemplate j hj) := by
  intro J hJ
  have h0 : (0 : Fin (j+1)) ∈ J := hJ (Finset.mem_singleton_self _)
  let A := Finset.univ.filter (fun i : Fin j => i.succ ∈ J)
  have hsub : ((wheelTemplate j hj).edges.filter (· ⊆ J)) ⊆
      A.image wheelSpoke ∪ A.image wheelRim := by
    intro e he
    obtain ⟨he,hsub⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,rfl⟩)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hsub (Finset.mem_insert_self _ _)⟩,rfl⟩)
  have hA : A.card ≤ (J.erase 0).card := by
    apply Finset.card_le_card_of_injOn Fin.succ
    · intro i hi
      exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i,(Finset.mem_filter.mp hi).2⟩
    · intro a _ b _ hab
      exact Fin.succ_injective _ hab
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_image_le (s := A) (f := wheelSpoke)
  have h2 := Finset.card_image_le (s := A) (f := wheelRim)
  rw [Finset.card_erase_of_mem h0] at hA
  rw [wheelTemplate_roots_card]
  omega

def wheelRoot {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) :
    {v // v ∈ (wheelTemplate j hj).roots} ↪ Fin n where
  toFun := fun _ => u
  inj' := by
    intro a b _
    apply Subtype.ext
    have ha : a.val = 0 := Finset.mem_singleton.mp a.property
    have hb : b.val = 0 := Finset.mem_singleton.mp b.property
    exact ha.trans hb.symm

lemma wheelRooted_zero {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) : φ.val 0 = u :=
  φ.property ⟨0,Finset.mem_singleton_self _⟩

def wheelRestrict {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) : Fin j ↪ Fin n :=
  (Fin.succEmb j).trans φ.val

lemma wheel_image_subset {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) (G : Graph n) :
    imageEdges (wheelTemplate j hj) φ.val ⊆ G ↔
      ∀ i, {u,wheelRestrict hj u φ i} ∈ G ∧
        {wheelRestrict hj u φ i,wheelRestrict hj u φ (cycleNext i)} ∈ G := by
  have hs (i : Fin j) : (wheelSpoke i).map φ.val = {u,wheelRestrict hj u φ i} := by
    simp [wheelSpoke,wheelRestrict,wheelRooted_zero hj u φ]
  have hr (i : Fin j) : (wheelRim i).map φ.val =
      {wheelRestrict hj u φ i,wheelRestrict hj u φ (cycleNext i)} := by simp [wheelRim,wheelRestrict]
  constructor
  · intro h i
    constructor
    · rw [← hs]
      exact h (Finset.mem_image.mpr ⟨wheelSpoke i,Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩),rfl⟩)
    · rw [← hr]
      exact h (Finset.mem_image.mpr ⟨wheelRim i,Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩),rfl⟩)
  · intro h e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      rw [hs]; exact (h i).1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      rw [hr]; exact (h i).2

lemma wheelRestrict_injective {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) :
    Function.Injective (wheelRestrict hj u) := by
  intro φ χ h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (wheelRooted_zero hj u φ).trans (wheelRooted_zero hj u χ).symm
  · exact congrArg (fun f : Fin j ↪ Fin n => f i) h

lemma wheelRestrict_surj {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) (φ : Fin j ↪ Fin n)
    (havoid : ∀ i, φ i ≠ u) :
    ∃ χ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u), wheelRestrict hj u χ = φ := by
  let f : Fin (j+1) → Fin n := Fin.cases u φ
  have hf : Function.Injective f := by
    intro a b h
    revert h
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro _; rfl
      · intro h; exact (havoid b h.symm).elim
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro h; exact (havoid a h).elim
      · intro h; exact congrArg Fin.succ (φ.injective h)
  let χ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u) :=
    ⟨⟨f,hf⟩,by intro v; have hv : v.val = 0 := Finset.mem_singleton.mp v.property; change f v.val = u; rw [hv]; rfl⟩
  exact ⟨χ,by ext i; rfl⟩

theorem wheel_rootedCount {j n : ℕ} (hj : 3 ≤ j) (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    rootedCount (wheelTemplate j hj) (wheelRoot hj u) G = linkCycleCount j G u := by
  let A := Finset.univ.filter (fun φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u) =>
    imageEdges (wheelTemplate j hj) φ.val ⊆ G)
  let B := Finset.univ.filter (fun φ : Fin j ↪ Fin n =>
    ∀ i, {u,φ i} ∈ G ∧ {φ i,φ (cycleNext i)} ∈ G)
  have hA : rootedCount (wheelTemplate j hj) (wheelRoot hj u) G = (A.card : ℝ) := by
    simp [rootedCount,copyCount,intact,A]
  have hB : linkCycleCount j G u = (B.card : ℝ) := by
    simp [linkCycleCount,B,Finset.sum_boole]
  rw [hA,hB]
  congr 1
  apply Finset.card_bij (fun φ _ => wheelRestrict hj u φ)
  · intro φ hφ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(wheel_image_subset hj u φ G).mp (Finset.mem_filter.mp hφ).2⟩
  · intro φ _ χ _ h
    exact wheelRestrict_injective hj u h
  · intro φ hφ
    have hp := (Finset.mem_filter.mp hφ).2
    have hav : ∀ i, φ i ≠ u := by
      intro i he
      have hh := mem_completeGraph.mp (hG (hp i).1)
      simp [he] at hh
    obtain ⟨χ,hχ⟩ := wheelRestrict_surj hj u φ hav
    refine ⟨χ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hχ⟩
    exact (wheel_image_subset hj u χ G).mpr (hχ.symm ▸ hp)

@[simp] theorem wheel_rootedScaling {j n : ℕ} (hj : 3 ≤ j) (p : ℝ) :
    rootedScaling (wheelTemplate j hj) n p = ((n : ℝ)*p^2)^j := by
  simp only [rootedScaling,wheelTemplate_roots_card,wheelTemplate_edges_card,Nat.add_sub_cancel,
    mul_pow,← pow_mul]

end SharpTerminalLeave
end
end

end OAI
