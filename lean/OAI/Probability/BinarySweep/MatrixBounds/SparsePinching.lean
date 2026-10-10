import Mathlib

namespace OAI

noncomputable section

section

open scoped BigOperators ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def blockVec (f : I → J) (a : J) (x : I → ℂ) : I → ℂ :=
  fun i => if f i = a then x i else 0

def pinch (f : I → J) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if f i = f j then A i j else 0

omit [Fintype I] in
lemma sum_blockVec (f : I → J) (x : I → ℂ) : ∑ a, blockVec f a x = x := by
  ext i
  simp [blockVec]

omit [Fintype I] [Fintype J] in
lemma pinch_hermitian (f : I → J) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (pinch f A).IsHermitian := by
  ext i j
  change star (if f j = f i then A j i else 0) = if f i = f j then A i j else 0
  by_cases h : f i = f j
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact congrFun (congrFun hA i) j
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), star_zero]

lemma pinch_form (f : I → J) (A : Matrix I I ℂ) (x : I → ℂ) :
    star x ⬝ᵥ (pinch f A).mulVec x =
      ∑ a, star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f a x) := by
  simp only [dotProduct, mulVec, blockVec, pinch, Pi.star_apply, apply_ite, star_zero,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : f i = f j
  · rw [h]
    simp
  · simp [h]

lemma pinch_posSemidef (f : I → J) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (pinch f A).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg (pinch_hermitian f hA.1) (fun x => ?_)
  rw [pinch_form]
  exact Finset.sum_nonneg (fun a _ => hA.dotProduct_mulVec_nonneg _)

lemma form_cross_le {A : Matrix I I ℂ} (hA : A.PosSemidef) (x y : I → ℂ) :
    star x ⬝ᵥ A.mulVec y + star y ⬝ᵥ A.mulVec x ≤
      star x ⬝ᵥ A.mulVec x + star y ⬝ᵥ A.mulVec y := by
  have h := hA.dotProduct_mulVec_nonneg (x-y)
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h
  exact sub_nonneg.mp (by convert h using 1; abel)

omit [Fintype J] in
lemma block_form_zero (f : I → J) (A : Matrix I I ℂ) (a b : J)
    (h : ∀ i j, f i = a → f j = b → A i j = 0) (x : I → ℂ) :
    star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f b x) = 0 := by
  simp only [dotProduct, mulVec, blockVec, Pi.star_apply, apply_ite, star_zero,
    Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases ha : f i = a
  · by_cases hb : f j = b
    · simp [ha, hb, h i j ha hb]
    · simp [hb]
  · simp [ha]

theorem sparse_pinching (f : I → J) (R : J → J → Prop) [DecidableRel R]
    (hR : ∀ ⦃left right⦄, R left right → R right left)
    (D : ℕ) (hD : ∀ a, (Finset.univ.filter (R a)).card ≤ D)
    {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hz : ∀ i j, ¬ R (f i) (f j) → A i j = 0) :
    ((D : ℂ) • pinch f A - A).PosSemidef := by
  have hp := pinch_hermitian f hA.1
  refine .of_dotProduct_mulVec_nonneg ((hp.smul (by simp)).sub hA.1) (fun x => ?_)
  let t : J → J → ℂ := fun a b => star (blockVec f a x) ⬝ᵥ A.mulVec (blockVec f b x)
  have hdiag (a : J) : 0 ≤ t a a := hA.dotProduct_mulVec_nonneg _
  have ht (a b : J) (hab : ¬R a b) : t a b = 0 := by
    apply block_form_zero
    intro i j hi hj
    exact hz i j (by simpa [hi, hj] using hab)
  have hsum : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a b = star x ⬝ᵥ A.mulVec x := by
    simp_rw [Finset.sum_filter]
    have ht' : ∀ a b, (if R a b then t a b else 0) = t a b := by
      intro a b
      split_ifs with h
      · rfl
      · exact (ht a b h).symm
    simp_rw [ht']
    dsimp [t]
    simp_rw [← dotProduct_sum, ← mulVec_sum, sum_blockVec]
    rw [← sum_dotProduct, ← star_sum, sum_blockVec]
  have hswap : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t b a =
      ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a b := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have he : R b a ↔ R a b := ⟨fun h => hR h, fun h => hR h⟩
    simp only [he]
  have hdeg : ∑ a, ∑ b ∈ Finset.univ.filter (R a), (t a a + t b b) =
      2 * ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a := by
    simp only [Finset.sum_add_distrib]
    have hs : ∑ a, ∑ b ∈ Finset.univ.filter (R a), t b b =
        ∑ a, ∑ b ∈ Finset.univ.filter (R a), t a a := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp only [show R b a ↔ R a b from ⟨fun h => hR h, fun h => hR h⟩]
    rw [hs]
    simp [two_mul]
  have hle := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset J)) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ.filter (R a)) =>
      form_cross_le hA (blockVec f a x) (blockVec f b x)))
  change (∑ a, ∑ b ∈ Finset.univ.filter (R a), (t a b + t b a)) ≤ _ at hle
  simp only [Finset.sum_add_distrib] at hle
  rw [hswap, hsum] at hle
  have hc : star x ⬝ᵥ A.mulVec x ≤ ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a := by
    have hh := hdeg
    simp only [Finset.sum_add_distrib] at hh
    rw [hh] at hle
    simp only [two_mul, Complex.le_def, Complex.add_re, Complex.add_im] at hle
    exact Complex.le_def.mpr ⟨by linarith [hle.1], by linarith [hle.2]⟩
  have hd : ∑ a, ((Finset.univ.filter (R a)).card : ℂ) * t a a ≤
      (D : ℂ) * ∑ a, t a a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD a) (hdiag a)
  have hf := hc.trans hd
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply sub_nonneg.mpr
  simpa only [pinch_form, t] using hf

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [LinearOrder I]

def subsetCode (k : ℕ) (s : Finset I) : Fin k → Option I :=
  fun i => if h : i.val < s.card then some (s.orderEmbOfFin rfl ⟨i.val,h⟩) else none

omit [Fintype I] in
lemma subsetCode_range (k : ℕ) (s : Finset I) (hs : s.card ≤ k) (j : I) :
    some j ∈ Set.range (subsetCode k s) ↔ j ∈ s := by
  constructor
  · rintro ⟨i,hi⟩
    dsimp only [subsetCode] at hi
    split_ifs at hi with h
    · have hj := Option.some.inj hi
      rw [← hj]
      exact Finset.orderEmbOfFin_mem s rfl _
  · intro hj
    have hr : j ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨i,hi⟩ := hr
    refine ⟨⟨i.val, i.isLt.trans_le hs⟩, ?_⟩
    simp only [subsetCode, dite_eq_left i.isLt]
    exact congrArg some hi

lemma card_small_subsets_le (k : ℕ) :
    Fintype.card {s : Finset I // s.card ≤ k} ≤ (Fintype.card I + 1)^k := by
  let f : {s : Finset I // s.card ≤ k} → (Fin k → Option I) := fun s => subsetCode k s.val
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    ext j
    rw [← subsetCode_range k s.val s.property j, ← subsetCode_range k t.val t.property j]
    rw [show Set.range (subsetCode k s.val) = Set.range (subsetCode k t.val) from
      congrArg Set.range h]
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_option] using hc

def hamming (a b : I → Bool) : ℕ := (Finset.univ.filter (fun i => a i ≠ b i)).card

omit [LinearOrder I] in
lemma hamming_symm (a b : I → Bool) : hamming a b = hamming b a := by
  unfold hamming
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

lemma hamming_degree (a : I → Bool) (k : ℕ) :
    (Finset.univ.filter (fun b => hamming a b ≤ k)).card ≤ (Fintype.card I + 1)^k := by
  let f : {b : I → Bool // hamming a b ≤ k} → {s : Finset I // s.card ≤ k} :=
    fun b => ⟨Finset.univ.filter (fun i => a i ≠ b.val i), b.property⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    funext i
    have hi := Finset.ext_iff.mp (congrArg Subtype.val h) i
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    cases ha : a i <;> cases hb : b.val i <;> cases hc : c.val i <;>
      simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, ne_eq,
        not_true_eq_false, iff_false, iff_true]
  have hh := (Fintype.card_le_of_injective f hf).trans (card_small_subsets_le (I := I) k)
  simpa only [Fintype.card_subtype] using hh

end BinaryCoordinateSweeps.Density

end

end OAI
