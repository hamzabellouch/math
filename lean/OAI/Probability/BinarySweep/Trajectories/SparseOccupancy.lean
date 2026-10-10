import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.UniformFiniteProbability

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω L : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem occupancy_probability_le [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀u, 0 ≤ p u) (hp1 : ∑u, p u=1)
    (E : Ω → Prop) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hE : finiteProbability p E ≤ δ) (w : ℕ) :
    productProbability p (fun x : I → Ω => w ≤ (Finset.univ.filter (fun i => E (x i))).card) ≤
      (2:ℝ)^Fintype.card I * δ^w := by
  let root : Ω := Classical.choice inferInstance
  have hT (T : Finset I) :
      productProbability p (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) ≤ δ^w := by
    by_cases h : w ≤ T.card
    · have hb := depthOne_probability_le p hp hp1 (fun u _ => E u) δ hδ
        (fun _ => hE) T (fun _ => Sum.inr ()) (fun _ : Unit => root)
      have he : (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) =
          (fun x : I → Ω => ∀i : T, E (x i)) := by
        funext x
        simp only [h,true_and,Subtype.forall]
      rw [he]
      exact hb.trans (pow_le_pow_of_le_one hδ hδ1 h)
    · simp only [h,false_and,productProbability,ite_false,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hδ w
  calc
    _ ≤ productProbability p (fun x : I → Ω => ∃T : Finset I, w ≤ T.card ∧ ∀i∈T, E (x i)) :=
      productProbability_mono hp (fun x hx => ⟨_,hx,fun i hi => (Finset.mem_filter.mp hi).2⟩)
    _ ≤ ∑T : Finset I, productProbability p (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) :=
      productProbability_union_le hp _
    _ ≤ _ := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        using Finset.sum_le_sum (s:=Finset.univ) (fun T _ => hT T)

variable [Fintype L] [DecidableEq L]

def smallSetEncode {r : ℕ} (S : {S : Finset L // S.card ≤ r}) : Fin r → Option L :=
  fun i => if h : i.val < S.val.card then
    some ((Fintype.equivFin S.val).symm ⟨i.val,by simpa using h⟩).val else none

omit [Fintype L] [DecidableEq L] in
lemma smallSetEncode_mem {r : ℕ} (S : {S : Finset L // S.card ≤ r}) (l : L) :
    l∈S.val ↔ ∃i, smallSetEncode S i=some l := by
  constructor
  · intro hl
    let j := Fintype.equivFin S.val ⟨l,hl⟩
    have hj : j.val < S.val.card := by simpa using j.isLt
    refine ⟨⟨j.val,lt_of_lt_of_le hj S.property⟩,?_⟩
    simp only [smallSetEncode,dite_eq_left hj]
    have he : (⟨j.val,by simpa using hj⟩ : Fin (Fintype.card S.val))=j := rfl
    rw [he,Equiv.symm_apply_apply]
  · rintro ⟨i,hi⟩
    unfold smallSetEncode at hi
    split_ifs at hi with h
    · cases Option.some.inj hi
      exact ((Fintype.equivFin S.val).symm ⟨i.val,by simpa using h⟩).property

omit [Fintype L] [DecidableEq L] in
lemma smallSetEncode_injective (r : ℕ) : Function.Injective (smallSetEncode (L:=L) (r:=r)) := by
  intro S T h
  apply Subtype.ext
  ext l
  rw [smallSetEncode_mem,smallSetEncode_mem,h]

omit [DecidableEq L] in
lemma smallSet_card_bound (r : ℕ) :
    Fintype.card {S : Finset L // S.card ≤ r} ≤ (Fintype.card L+1)^r := by
  simpa only [Fintype.card_fun,Fintype.card_option,Fintype.card_fin]
    using Fintype.card_le_of_injective _ (smallSetEncode_injective (L:=L) r)

theorem line_sets_occupancy_probability_le [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀u, 0 ≤ p u) (hp1 : ∑u, p u=1)
    (line : Ω → L) (r w : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmass : ∀S : Finset L, S.card ≤ r → finiteProbability p (fun u => line u∈S) ≤ δ) :
    productProbability p (fun x : I → Ω => ∃S : Finset L, S.card ≤ r ∧
      w ≤ (Finset.univ.filter (fun i => line (x i)∈S)).card) ≤
      ((Fintype.card L+1:ℕ):ℝ)^r * (2:ℝ)^Fintype.card I * δ^w := by
  let E (S : {S : Finset L // S.card ≤ r}) (x : I → Ω) :=
    w ≤ (Finset.univ.filter (fun i => line (x i)∈S.val)).card
  have h1 := productProbability_union_le hp E
  have h2 : (∑S, productProbability p (E S)) ≤
      (Fintype.card {S : Finset L // S.card ≤ r}:ℝ)*((2:ℝ)^Fintype.card I*δ^w) := by
    calc
      _ ≤ ∑ S : {S : Finset L // S.card ≤ r}, ((2:ℝ)^Fintype.card I*δ^w) := by
        apply Finset.sum_le_sum
        intro S _
        convert occupancy_probability_le p hp hp1 (fun u => line u∈S.val) δ hδ hδ1
          (hmass S.val S.property) w (I:=I) using 1
        unfold productProbability E
        apply Finset.sum_congr rfl
        intro x _
        congr 2
        apply congrArg (fun t : Finset I => w ≤ t.card)
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      _ = _ := by simp
  have h3 : (Fintype.card {S : Finset L // S.card ≤ r}:ℝ) ≤ ((Fintype.card L+1:ℕ):ℝ)^r := by
    exact_mod_cast smallSet_card_bound (L:=L) r
  have he : (fun x : I → Ω => ∃S : Finset L, S.card ≤ r ∧
      w ≤ (Finset.univ.filter (fun i => line (x i)∈S)).card) = (fun x => ∃S, E S x) := by
    funext x
    simp only [E,Subtype.exists,exists_prop]
  rw [he]
  apply h1.trans (h2.trans _)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hδ w))

end BinaryCoordinateSweeps.Sparse

end

end OAI
