import OAI.Analysis.SphereIsometry.FiniteComplex
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Ranks and carriers of finite face-chains -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_eq_of_card_eq {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card = b.val.card) :
    a = b := by
  apply Subtype.ext
  rcases hc a ha b hb with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

theorem chain_subset_of_card_le {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card ≤ b.val.card) :
    a.val ⊆ b.val := by
  rcases hc a ha b hb with hab | hba
  · exact hab
  · intro x hx
    rw [Finset.eq_of_subset_of_card_le hba h]
    exact hx

def ranks (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Finset ℕ :=
  c.image (fun a => a.val.card)

@[simp] theorem mem_ranks {c : Finset (FaceVertex K)} {r : ℕ} :
    r ∈ K.ranks c ↔ ∃ a ∈ c, a.val.card = r :=
  Finset.mem_image

theorem card_ranks {c : Finset (FaceVertex K)} (hc : K.chain c) :
    (K.ranks c).card = c.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact chain_eq_of_card_eq hc ha hb hab

theorem ranks_subset {m : ℕ} (hK : K.CardBound m) (c : Finset (FaceVertex K)) :
    K.ranks c ⊆ Finset.Icc 1 (m + 1) := by
  intro r hr
  obtain ⟨a, _, rfl⟩ := mem_ranks.mp hr
  exact Finset.mem_Icc.mpr
    ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩

theorem sd_cardBound {m : ℕ} (hK : K.CardBound m) : K.sd.CardBound m := by
  intro c hc
  have h := Finset.card_le_card (ranks_subset hK c)
  rw [card_ranks (mem_sd_iff.mp hc)] at h
  simpa using h

theorem top_ranks {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.topCells m) : K.ranks c = Finset.Icc 1 (m + 1) := by
  obtain ⟨hc, hcard⟩ := mem_topCells.mp hc
  apply Finset.eq_of_subset_of_card_le (ranks_subset hK c)
  rw [card_ranks (mem_sd_iff.mp hc), hcard]
  simp

theorem missing_rank {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.codimFaces m) :
    ∃ r, 1 ≤ r ∧ r ≤ m + 1 ∧ K.ranks c = (Finset.Icc 1 (m + 1)).erase r := by
  obtain ⟨hchain, hcard⟩ := mem_codimFaces.mp hc
  have hsub := ranks_subset hK c
  have hd : ((Finset.Icc 1 (m + 1)) \ K.ranks c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, card_ranks (mem_sd_iff.mp hchain), hcard]
    simp
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hd
  have hrmem : r ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c := by
    rw [hr]
    exact Finset.mem_singleton_self _
  obtain ⟨hrI, hrnot⟩ := Finset.mem_sdiff.mp hrmem
  refine ⟨r, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2, ?_⟩
  ext q
  constructor
  · intro hq
    exact Finset.mem_erase.mpr ⟨fun hqr => hrnot (hqr ▸ hq), hsub hq⟩
  · intro hq
    obtain ⟨hqr, hqI⟩ := Finset.mem_erase.mp hq
    by_contra hnot
    have : q ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c :=
      Finset.mem_sdiff.mpr ⟨hqI, hnot⟩
    rw [hr] at this
    exact hqr (Finset.mem_singleton.mp this)

theorem exists_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    (hne : c.Nonempty) : ∃ a ∈ c, ∀ b ∈ c, b.val ⊆ a.val := by
  obtain ⟨a, ha, hmax⟩ := c.exists_max_image (fun b => b.val.card) hne
  exact ⟨a, ha, fun b hb => chain_subset_of_card_le hc hb ha (hmax b hb)⟩

theorem card_le_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a : FaceVertex K} (_ha : a ∈ c) (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    c.card ≤ a.val.card := by
  have hsub : K.ranks c ⊆ Finset.Icc 1 a.val.card := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := mem_ranks.mp hr
    exact Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr b.property.2, Finset.card_le_card (hmax b hb)⟩
  have h := Finset.card_le_card hsub
  rw [card_ranks hc] at h
  simpa using h

variable {I : Type v} [DecidableEq I]

theorem faceCarrier_sd_eq_greatest {carrier : V → Finset I}
    {c : Finset (FaceVertex K)} {a : FaceVertex K} (ha : a ∈ c)
    (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    faceCarrier (K.sdCarrier carrier) c = faceCarrier carrier a.val := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨b, hb, hbi⟩ := mem_faceCarrier.mp hi
    exact faceCarrier_mono carrier (hmax b hb) hbi
  · intro i hi
    exact mem_faceCarrier.mpr ⟨a, ha, hi⟩

theorem sd_card_le_carrier {carrier : V → Finset I}
    (hK : ∀ s ∈ K.faces, s.card ≤ (faceCarrier carrier s).card)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.faces) :
    c.card ≤ (faceCarrier (K.sdCarrier carrier) c).card := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨a, ha, hmax⟩ := exists_greatest (mem_sd_iff.mp hc) hne
    rw [faceCarrier_sd_eq_greatest ha hmax]
    exact (card_le_greatest (mem_sd_iff.mp hc) ha hmax).trans (hK a.val a.property.1)

end Tingley.FiniteComplex

end

end OAI
