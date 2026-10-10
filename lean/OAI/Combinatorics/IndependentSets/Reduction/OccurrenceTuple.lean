import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LabelCoverData

namespace OAI

namespace LargeIndependentSets

section
open scoped Classical

def occurrenceTuple {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : ℕ) : MixedTuple U V n i :=
  ⟨fun h => if h.val < i then Sum.inl (lc.right (c h)) else Sum.inr (lc.left (c h)), by
    intro h
    by_cases hh : h.val < i <;> simp [hh]⟩

def occurrenceQuestion {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : Fin (n+1)) : LayerQuestion U V n :=
  ⟨i, occurrenceTuple lc c i.val⟩

def chainComposite {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i j : ℕ) (hij : i ≤ j) :
    MixedTuple L R n i → MixedTuple L R n j :=
  fun x => ⟨fun h => if i ≤ h.val ∧ h.val < j then
      Sum.inl ((x.val h).elim id (lc.project (c h))) else x.val h, by
    intro h
    by_cases hh : i ≤ h.val ∧ h.val < j
    · simp [hh]
    · have he : (h.val < i) = (h.val < j) := propext (by omega)
      simp [hh, x.property h, he]⟩

@[simp] lemma chainComposite_self {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : ℕ) (hi : i ≤ i) (x : MixedTuple L R n i) :
    chainComposite lc c i i hi x = x := by
  apply Subtype.ext
  funext h
  simp [chainComposite, show ¬(i ≤ h.val ∧ h.val < i) from by omega]

lemma chainComposite_comp {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (x : MixedTuple L R n i) :
    chainComposite lc c j k hjk (chainComposite lc c i j hij x) =
      chainComposite lc c i k (hij.trans hjk) x := by
  apply Subtype.ext
  funext h
  dsimp [chainComposite]
  by_cases h₁ : h.val < i
  · simp [show ¬i ≤ h.val from by omega, show ¬j ≤ h.val from by omega]
  · by_cases h₂ : h.val < j
    · simp [show i ≤ h.val from by omega, h₂, show h.val < k from by omega,
        show ¬ j ≤ h.val from by omega]
    · by_cases h₃ : h.val < k
      · simp [show i ≤ h.val from by omega, show j ≤ h.val from by omega, h₂, h₃]
      · simp [h₂, h₃]

lemma chainComposite_adjacent {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (h : Fin n) :
    chainComposite lc c h.val (h.val+1) (by omega) = mixedProject h (lc.project (c h)) := by
  funext x
  apply Subtype.ext
  funext k
  have he : (h.val ≤ k.val ∧ k.val < h.val+1) ↔ k = h := by
    constructor
    · intro hk; apply Fin.ext; omega
    · intro hk; subst k; omega
  simp only [chainComposite, mixedProject, he]
  split_ifs with hk
  · subst k; rfl
  · rfl

lemma occurrence_chain_imposed {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (h : Fin n) :
    (layeredSystem lc n).imposed (occurrenceQuestion lc c h.castSucc)
      (occurrenceQuestion lc c h.succ) (chainComposite lc c h.val (h.val+1) (by omega)) := by
  rw [chainComposite_adjacent]
  apply LayerImposed.adjacent h (occurrenceTuple lc c h.val)
    (occurrenceTuple lc c (h.val+1)) (c h)
  · simp [occurrenceTuple]
  · simp [occurrenceTuple]
  · intro k hk
    have hne : k.val ≠ h.val := fun he => hk (Fin.ext he)
    have he : (k.val < h.val) = (k.val < h.val+1) := propext (by omega)
    simp only [occurrenceTuple, he]

lemma imposed_path_zero {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] {q q' : Q} (π : M q → M q') (hπ : S.imposed q q' π)
    (v : M q' → ZMod D) : pathDistance S.linkLength ⟨q, v ∘ π⟩ ⟨q', v⟩ = 0 := by
  apply le_antisymm _ bot_le
  apply (pathDistance_le_link _ _ _).trans
  have hz : S.ZeroLink D ⟨q, v ∘ π⟩ ⟨q', v⟩ := Or.inl (.link q q' π hπ v)
  simp only [ProjectionSystem.linkLength, ite_eq_left hz]
  exact le_rfl

theorem occurrence_chain_path_zero {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) {D : ℕ} [NeZero D] (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n)
    (v : MixedTuple L R n j → ZMod D) :
    pathDistance (layeredSystem lc n).linkLength
      ⟨occurrenceQuestion lc c ⟨i, by omega⟩, v ∘ chainComposite lc c i j hij⟩
      ⟨occurrenceQuestion lc c ⟨j, by omega⟩, v⟩ = 0 := by
  induction j, hij using Nat.le_induction with
  | base =>
    have he : v ∘ chainComposite lc c i i (by omega) = v := by
      funext x; simp
    simp only [occurrenceQuestion] at ⊢
    rw [he]
    exact pathDistance_self _ (linkLength_self _) _
  | succ j hij ih =>
    let w : MixedTuple L R n j → ZMod D := v ∘ chainComposite lc c j (j+1) (by omega)
    have hleft := ih (by omega) w
    have hright := imposed_path_zero (layeredSystem lc n)
      (q := occurrenceQuestion lc c ⟨j, by omega⟩)
      (q' := occurrenceQuestion lc c ⟨j+1, by omega⟩)
      (chainComposite lc c j (j+1) (by omega))
      (occurrence_chain_imposed lc c ⟨j, by omega⟩) v
    have he : w ∘ chainComposite lc c i j hij = v ∘ chainComposite lc c i (j+1) (by omega) := by
      funext x
      exact congrArg v (chainComposite_comp lc c i j (j+1) hij (by omega) x)
    simp only [occurrenceQuestion] at hleft
    rw [he] at hleft
    apply le_antisymm _ bot_le
    exact (pathDistance_triangle _ _
      ⟨occurrenceQuestion lc c ⟨j, by omega⟩, w⟩ _).trans
      (by
        simp only [occurrenceQuestion] at hright ⊢
        rw [hleft, hright, add_zero]
        exact le_rfl)

end

open scoped Classical BigOperators
noncomputable def paddedList {X : Type*} (A : Finset X) (d : ℕ) (x₀ : X) (i : Fin d) : X :=
  if hi : i.val < A.card then (A.equivFin.symm ⟨i.val, hi⟩).val else x₀

lemma mem_paddedList {X : Type*} (A : Finset X) (d : ℕ) (x₀ x : X)
    (hd : A.card ≤ d) (hx : x ∈ A) : ∃ i : Fin d, paddedList A d x₀ i = x := by
  let j := A.equivFin ⟨x, hx⟩
  refine ⟨⟨j.val, j.isLt.trans_le hd⟩, ?_⟩
  simp only [paddedList, j.isLt, dite_eq_left]
  exact congrArg Subtype.val (A.equivFin.symm_apply_apply ⟨x, hx⟩)

def LabelCoverData.Sound {U V L R C : Type*} [Fintype C]
    (lc : LabelCoverData U V L R C) (σ : ℝ) : Prop :=
  ∀ (l : U → L) (r : V → R),
    ((Finset.univ.filter (fun c => lc.project c (l (lc.left c)) = r (lc.right c))).card : ℝ) ≤
      σ * Fintype.card C

theorem bounded_list_decoding {U V L R C : Type*} [Fintype C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    (d : ℕ) (A : U → Finset L) (B : V → Finset R)
    (hA : ∀ u, (A u).card ≤ d) (hB : ∀ v, (B v).card ≤ d) :
    ((Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
      lc.project c l = r)).card : ℝ) ≤ (d : ℝ)^2 * σ * Fintype.card C := by
  classical
  let ls : Fin d → U → L := fun i u => paddedList (A u) d (Classical.arbitrary L) i
  let rs : Fin d → V → R := fun i v => paddedList (B v) d (Classical.arbitrary R) i
  let E : Fin d × Fin d → Finset C := fun ij => Finset.univ.filter
    (fun c => lc.project c (ls ij.1 (lc.left c)) = rs ij.2 (lc.right c))
  have hcover : Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
        lc.project c l = r) ⊆ Finset.univ.biUnion E := by
    intro c hc
    obtain ⟨l, hl, r, hr, he⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨i, hi⟩ := mem_paddedList (A (lc.left c)) d (Classical.arbitrary L) l (hA _) hl
    obtain ⟨j, hj⟩ := mem_paddedList (B (lc.right c)) d (Classical.arbitrary R) r (hB _) hr
    apply Finset.mem_biUnion.mpr
    refine ⟨(i,j), Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [ls, rs, hi, hj] using he⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcr : ((Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
        lc.project c l = r)).card : ℝ) ≤ ∑ ij, ((E ij).card : ℝ) := by
    exact_mod_cast hc
  have he : ∑ ij, ((E ij).card : ℝ) ≤ ∑ _ij : Fin d × Fin d, σ * Fintype.card C := by
    apply Finset.sum_le_sum
    intro ij _
    exact hsound (ls ij.1) (rs ij.2)
  calc
    _ ≤ _ := hcr.trans he
    _ = (d : ℝ)^2 * σ * Fintype.card C := by
      simp [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc]

theorem bounded_list_probability {U V L R C : Type*} [Fintype C] [Nonempty C]
    [Nonempty L] [Nonempty R] (lc : LabelCoverData U V L R C)
    {σ : ℝ} (hsound : lc.Sound σ) (d : ℕ) (A : U → Finset L) (B : V → Finset R)
    (hA : ∀ u, (A u).card ≤ d) (hB : ∀ v, (B v).card ≤ d) :
    ((Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c),
      lc.project c l = r)).card : ℝ) / Fintype.card C ≤ (d : ℝ)^2 * σ := by
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card C)).mpr
  exact bounded_list_decoding lc hsound d A B hA hB

end LargeIndependentSets

end OAI
