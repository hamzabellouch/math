import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Enum

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
variable {σ P : Type*} [Fintype σ] [Fintype P] [DecidableEq P]

def support (x : σ → Option P) : Finset P := univ.filter (fun p => ∃ s, x s=some p)

@[simp] lemma mem_support (x : σ → Option P) (p : P) :
    p ∈ support x ↔ ∃ s, x s=some p := by simp [support]

noncomputable def firstSlot (x : σ → Option P) (p : support x) : σ :=
  Classical.choose ((mem_support x p.val).mp p.property)

lemma firstSlot_eq (x : σ → Option P) (p : support x) : x (firstSlot x p)=some p.val :=
  Classical.choose_spec ((mem_support x p.val).mp p.property)

lemma firstSlot_injective (x : σ → Option P) : Function.Injective (firstSlot x) := by
  intro p q he
  apply Subtype.ext
  apply Option.some.inj
  rw [←firstSlot_eq x p,←firstSlot_eq x q,he]

lemma card_support_le (x : σ → Option P) : (support x).card ≤ Fintype.card σ := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ (firstSlot_injective x)

noncomputable def values (x : σ → Option P) : Fin (support x).card ↪ P where
  toFun i := (FiniteSlotEncoding.enum (support x) i).val
  inj' := fun _ _ h => (FiniteSlotEncoding.enum (support x)).injective (Subtype.ext h)

noncomputable def pattern (x : σ → Option P) (s : σ) : Option (Fin (support x).card) :=
  match h : x s with
  | none => none
  | some p => some ((FiniteSlotEncoding.enum (support x)).symm ⟨p,(mem_support x p).mpr ⟨s,h⟩⟩)

lemma decode_pattern (x : σ → Option P) (s : σ) :
    (pattern x s).map (values x)=x s := by
  unfold pattern
  split <;> rename_i he
  · exact he.symm
  · change some ((FiniteSlotEncoding.enum (support x))
        ((FiniteSlotEncoding.enum (support x)).symm _)).val = x s
    simpa only [Equiv.apply_symm_apply] using he.symm

abbrev Code (σ P : Type*) [Fintype σ] :=
  (m : Fin (Fintype.card σ+1)) × (σ → Option (Fin m.val)) × (Fin m.val → P)

noncomputable def encode (x : σ → Option P) : Code σ P :=
  ⟨⟨(support x).card,Nat.lt_succ_of_le (card_support_le x)⟩,pattern x,values x⟩

def decode (z : Code σ P) (s : σ) : Option P := (z.2.1 s).map z.2.2

lemma decode_encode (x : σ → Option P) : decode (encode x)=x :=
  funext (decode_pattern x)

lemma encode_injective : Function.Injective (encode (σ:=σ) (P:=P)) :=
  Function.LeftInverse.injective decode_encode

lemma weight_identity (x : σ → Option P) (W : P → ℝ) :
    (∏ p ∈ support x, W p) = ∏ i, W (values x i) := by
  rw [←prod_coe_sort (support x) W]
  exact ((FiniteSlotEncoding.enum (support x)).prod_comp (fun p => W p.val)).symm

noncomputable def codeWeight (z : Code σ P) (W : P → ℝ) : ℝ := ∏ i, W (z.2.2 i)

lemma codeWeight_encode (x : σ → Option P) (W : P → ℝ) :
    codeWeight (encode x) W=∏ p ∈ support x, W p := (weight_identity x W).symm

theorem weighted_code_sum (G : (σ → Option P) → ℝ) (hG : ∀ x, 0 ≤ G x)
    (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) :
    (∑ x : σ → Option P, G x * ∏ p ∈ support x, W p) ≤
      ∑ z : Code σ P, G (decode z) * codeWeight z W := by
  calc
    _ = ∑ z ∈ (univ : Finset (σ → Option P)).image encode, G (decode z)*codeWeight z W := by
      rw [sum_image (fun x _ y _ h => encode_injective h)]
      apply sum_congr rfl
      intro x hx
      rw [decode_encode,codeWeight_encode]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn =>
      mul_nonneg (hG _) (prod_nonneg (fun i hi => hW _)))

end OrdinaryCorrelations.SharedSlotPatterns

end

end OAI
