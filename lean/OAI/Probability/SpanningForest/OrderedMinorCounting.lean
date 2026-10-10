import OAI.Probability.SpanningForest.WeightedCauchyBinet

namespace OAI

noncomputable section

open scoped BigOperators
open Finset Function

namespace Problem336.OrderedMinorCounting

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def embeddingRange (f : n ↪ m) : Finset m := Finset.univ.map f

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] lemma mem_embeddingRange (f : n ↪ m) (x : m) :
    x ∈ embeddingRange f ↔ ∃ i, f i = x := by
  simp [embeddingRange]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] lemma card_embeddingRange (f : n ↪ m) :
    (embeddingRange f).card = Fintype.card n := by
  simp [embeddingRange]

def embeddingFiberEquiv (s : Finset m) :
    {f : n ↪ m // embeddingRange f = s} ≃ (n ≃ ↥s) where
  toFun f := Equiv.ofBijective
    (fun i => (⟨f.1 i, by simpa only [f.2] using (mem_embeddingRange f.1 _).mpr ⟨i, rfl⟩⟩ : ↥s))
    (by
      constructor
      · intro i j h
        exact f.1.injective (congrArg Subtype.val h)
      · intro x
        have hx : x.1 ∈ embeddingRange f.1 := by rw [f.2]; exact x.2
        obtain ⟨i, hi⟩ := (mem_embeddingRange f.1 x.1).mp hx
        exact ⟨i, Subtype.ext hi⟩)
  invFun e := ⟨e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩, by
    ext x
    rw [mem_embeddingRange]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩⟩
  left_inv f := by
    apply Subtype.ext
    ext i
    rfl
  right_inv e := by
    ext i
    rfl

lemma card_embedding_fiber (s : Finset m) (hs : s.card = Fintype.card n) :
    (Finset.univ.filter (fun f : n ↪ m => embeddingRange f = s)).card =
      Fintype.card (Equiv.Perm n) := by
  classical
  let e : n ≃ ↥s := Fintype.equivOfCardEq (by simpa using hs.symm)
  have hc := Fintype.card_congr (embeddingFiberEquiv (n := n) s)
  have he := Fintype.card_equiv e
  rw [Fintype.card_perm]
  rw [← he, ← hc]
  exact (Fintype.card_subtype _).symm

theorem sum_embeddingRange {R : Type*} [Semiring R] (F : Finset m → R) :
    (∑ f : n ↪ m, F (embeddingRange f)) =
      (Fintype.card (Equiv.Perm n) : R) *
        ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n), F s := by
  classical
  have hmap (f : n ↪ m) (_hf : f ∈ Finset.univ) :
      embeddingRange f ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n) := by
    simp
  rw [← Finset.sum_fiberwise_of_maps_to' hmap F]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [card_embedding_fiber s (Finset.mem_powersetCard.mp hs).2]

def minorSquare {R : Type*} [CommRing R] (A : Matrix n m R) (s : Finset m) : R :=
  Matrix.det ((A.transpose * A).submatrix (fun i : ↥s => i.1) (fun i : ↥s => i.1))

omit [Fintype m] in
lemma minorSquare_embeddingRange {R : Type*} [CommRing R]
    (A : Matrix n m R) (f : n ↪ m) :
    minorSquare A (embeddingRange f) = Matrix.det (A.submatrix id f) ^ 2 := by
  let e : n ≃ ↥(embeddingRange f) := embeddingFiberEquiv (embeddingRange f) ⟨f, rfl⟩
  unfold minorSquare
  rw [← Matrix.det_submatrix_equiv_self e]
  change Matrix.det ((A.transpose * A).submatrix f f) = _
  have hm : (A.transpose * A).submatrix f f =
      (A.submatrix id f).transpose * A.submatrix id f := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]
  rw [hm, Matrix.det_mul, Matrix.det_transpose, pow_two]

lemma sum_embedding_eq_sum_injective {R : Type*} [AddCommMonoid R] (F : (n → m) → R) :
    (∑ f : n ↪ m, F f) = ∑ f : n → m with Function.Injective f, F f := by
  classical
  have hs : (∑ f : n → m with Function.Injective f, F f) =
      ∑ f : {f : n → m // Function.Injective f}, F f.1 :=
    Finset.sum_subtype _ (by simp) F
  rw [hs]
  exact (Equiv.subtypeInjectiveEquivEmbedding n m).sum_comp (fun f : n ↪ m => F f) |>.symm

theorem weighted_gram_det_unordered (A : Matrix n m ℝ) (c : m → ℝ) :
    Matrix.det (A * Matrix.diagonal c * A.transpose) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        minorSquare A s * ∏ j ∈ s, c j := by
  classical
  have h := WeightedCauchyBinet.weighted_gram_det_injective A c
  rw [← sum_embedding_eq_sum_injective] at h
  have he : (∑ f : n ↪ m, Matrix.det (A.submatrix id f) ^ 2 * ∏ i, c (f i)) =
      ∑ f : n ↪ m, minorSquare A (embeddingRange f) * ∏ j ∈ embeddingRange f, c j := by
    apply Finset.sum_congr rfl
    intro f hf
    rw [minorSquare_embeddingRange A f]
    simp only [embeddingRange, Finset.prod_map]
  rw [he] at h
  rw [sum_embeddingRange (n := n) (fun s => minorSquare A s * ∏ j ∈ s, c j)] at h
  have hk : (Fintype.card (Equiv.Perm n) : ℝ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hk h

end Problem336.OrderedMinorCounting

end

end OAI
