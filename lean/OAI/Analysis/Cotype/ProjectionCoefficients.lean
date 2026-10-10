import OAI.Analysis.Cotype.CoefficientTarget
import OAI.Analysis.Cotype.GroupedPolynomial

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem fourier_const_mul (f : (ι → Bool) → ℝ) (a : ℝ) (p : ι → Bool) :
    fourier (fun S => a * f S) p = a * fourier f p := by
  simp only [fourier, average, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem fourier_sum {α : Type*} [Fintype α] (f : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun S => ∑ i, f i S) p = ∑ i, fourier (f i) p := by
  simp only [fourier, Finset.sum_mul, average_sum]

theorem fourier_character (p q : ι → Bool) :
    fourier (character p) q = if p = q then 1 else 0 := average_character_mul p q

theorem fourier_translate (f : (ι → Bool) → ℝ) (δ p : ι → Bool) :
    fourier (fun S => f (xorCube δ S)) p = fourier f p * character p δ := by
  have he : (fun S => f (xorCube δ S)) =
      fun S => ∑ q, (fourier f q * character q δ) * character q S := by
    funext S
    rw [← fourier_inversion f (xorCube δ S)]
    simp [character_xor, mul_assoc]
  rw [he, fourier_sum]
  simp_rw [fourier_const_mul, fourier_character]
  simp

theorem fourier_average_translate {α : Type*} [Fintype α]
    (f : (ι → Bool) → ℝ) (D : α → ι → Bool) (w : α → ℝ) (p : ι → Bool) :
    fourier (fun S => average (fun x => w x * f (xorCube (D x) S))) p =
      fourier f p * average (fun x => w x * character p (D x)) := by
  simp only [average, smul_eq_mul, fourier_const_mul, fourier_sum]
  simp_rw [fourier_translate]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def rowIndex (i : ι) (p : κ → Bool) : (ι × κ) → Bool :=
  fun ij => if ij.1 = i then p ij.2 else false

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem rowIndex_apply_self (i : ι) (p : κ → Bool) (j : κ) :
    rowIndex i p (i,j) = p j := by simp [rowIndex]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem rowIndex_injective (i : ι) : Function.Injective (rowIndex (κ := κ) i) := by
  intro p q h
  funext j
  simpa using congrFun h (i,j)

omit [DecidableEq κ] in
theorem character_rowIndex (i : ι) (p : κ → Bool) (S : (ι × κ) → Bool) :
    character (rowIndex i p) S = character p (fun j => S (i,j)) := by
  simp only [character, Fintype.prod_prod_type]
  have he (a : ι) : (∏ j, if rowIndex i p (a,j) then sign (S (a,j)) else 1) =
      if a = i then ∏ j, if p j then sign (S (i,j)) else 1 else 1 := by
    by_cases h : a = i <;> simp [h, rowIndex]
  simp_rw [he]
  simp

theorem fourier_rowLift (g : (κ → Bool) → ℝ) (i : ι) (p : κ → Bool) :
    fourier (fun S : (ι × κ) → Bool => g (fun j => S (i,j))) (rowIndex i p) =
      fourier g p := by
  have he : (fun S : (ι × κ) → Bool => g (fun j => S (i,j))) =
      fun S => ∑ q, fourier g q * character (rowIndex i q) S := by
    funext S
    simp only [character_rowIndex, fourier_inversion]
  rw [he, fourier_sum]
  simp_rw [fourier_const_mul, fourier_character, (rowIndex_injective i).eq_iff]
  simp

omit [Fintype ι] [Fintype κ] in
theorem rowIndex_setIndex (i : ι) (t : Finset κ) :
    rowIndex i (setIndex t) = rectangle {i} t := by
  funext ij
  by_cases h : ij.1 = i <;> simp [rowIndex, rectangle, setIndex, h]

theorem paritySign_setIndex (t : Finset ι) : paritySign (setIndex t) = (-1 : ℝ)^t.card := by
  simp [paritySign_eq, setIndex]

theorem row_rectangle_coefficient {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {g : Cube n → ℝ} {a : ℝ} (hΨ : IsOdd Ψ) (hg : IsOdd g)
    (hp : ∀ (i : Fin m) S, average (fun σ : Cube m =>
      sign (σ i) * Ψ (xorCube (rowCube σ) S)) = a * g (fun j => S (i,j)))
    (i : Fin m) (t : Finset (Fin n)) :
    fourier Ψ (rectangle {i} t) = a * fourier g (setIndex t) := by
  by_cases ht : Odd t.card
  · have he := congrArg (fun F => fourier F (rectangle {i} t)) (funext (hp i))
    rw [fourier_average_translate, fourier_const_mul,
      ← rowIndex_setIndex, fourier_rowLift] at he
    have hav : average (fun σ : Cube m => sign (σ i) *
        character (rowIndex i (setIndex t)) (rowCube σ)) = 1 := by
      simp_rw [rowIndex_setIndex, character_rectangle_row _ _ ht, character_setIndex,
        Finset.prod_singleton, sign_sq]
      simp [average, smul_eq_mul]
    rw [hav, mul_one] at he
    simpa only [rowIndex_setIndex] using he
  · have ht' := Nat.not_odd_iff_even.mp ht
    rw [odd_even_coefficient_zero hΨ (by simpa [paritySign_rectangle] using ht'.neg_one_pow (α := ℝ)),
      odd_even_coefficient_zero hg (by rw [paritySign_setIndex]; exact ht'.neg_one_pow)]
    simp

def transposeCube (S : (ι × κ) → Bool) : (κ × ι) → Bool := fun ij => S (ij.2,ij.1)

def transposeEquiv : ((ι × κ) → Bool) ≃ ((κ × ι) → Bool) where
  toFun := transposeCube
  invFun := transposeCube
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem character_transpose (P S : (ι × κ) → Bool) :
    character (transposeCube P) (transposeCube S) = character P S := by
  simp only [character, Fintype.prod_prod_type, transposeCube]
  exact Finset.prod_comm

theorem fourier_transpose (f : ((ι × κ) → Bool) → ℝ) (P : (ι × κ) → Bool) :
    fourier (fun S => f (transposeCube S)) (transposeCube P) = fourier f P := by
  simp only [fourier, average, smul_eq_mul]
  have hc : Fintype.card ((κ × ι) → Bool) = Fintype.card ((ι × κ) → Bool) :=
    Fintype.card_congr transposeEquiv.symm
  rw [hc]
  congr 1
  exact Fintype.sum_equiv transposeEquiv.symm _ _ (fun S => by
    exact congrArg (fun z => f (transposeCube S) * z)
      (character_transpose P (transposeCube S)))

omit [Fintype ι] [Fintype κ] in
theorem transpose_rectangle (s : Finset ι) (t : Finset κ) :
    transposeCube (rectangle s t) = rectangle t s := by
  funext ij
  simp [transposeCube, rectangle, and_comm]

theorem column_rectangle_coefficient {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {f : Cube m → ℝ} {b : ℝ} (hΨ : IsOdd Ψ) (hf : IsOdd f)
    (hp : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (xorCube (columnCube τ) S)) = b * f (fun i => S (i,j)))
    (s : Finset (Fin m)) (j : Fin n) :
    fourier Ψ (rectangle s {j}) = b * fourier f (setIndex s) := by
  have ho : IsOdd (fun S => Ψ (transposeCube S)) := fun S => hΨ (transposeCube S)
  have hproj : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (transposeCube (xorCube (rowCube τ) S))) =
        b * f (fun i => S (j,i)) := fun j S => hp j (transposeCube S)
  have h := row_rectangle_coefficient ho hf hproj j s
  rw [← transpose_rectangle s {j}, fourier_transpose] at h
  exact h

theorem Ckl_pair_sum (f : ((ι × κ) → Bool) → ℝ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    Ckl f k l = ∑ s ∈ Finset.univ.powersetCard k, ∑ t ∈ Finset.univ.powersetCard l,
      fourier f (rectangle s t) := by
  unfold Ckl rectangularIndices
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro st hst st' hst' he
    have hs : st.1.Nonempty := Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp (Finset.mem_product.mp hst).1).2]; exact hk)
    have ht : st.2.Nonempty := Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp (Finset.mem_product.mp hst).2).2]; exact hl)
    exact Prod.ext (rectangle_injective_nonempty hs ht he).1
      (rectangle_injective_nonempty hs ht he).2

def levelFourier (g : (ι → Bool) → ℝ) (l : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.powersetCard l, fourier g (setIndex t)

theorem Ckl_zero_right {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f) (k : ℕ) :
    Ckl f k 0 = 0 := by
  apply Finset.sum_eq_zero
  intro P hP
  obtain ⟨s, t, _, ht, rfl⟩ := mem_rectangularIndices.mp hP
  rw [Finset.card_eq_zero.mp ht]
  exact odd_even_coefficient_zero hf (by simp [paritySign_rectangle])

theorem Ckl_zero_left {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f) (l : ℕ) :
    Ckl f 0 l = 0 := by
  apply Finset.sum_eq_zero
  intro P hP
  obtain ⟨s, t, hs, _, rfl⟩ := mem_rectangularIndices.mp hP
  rw [Finset.card_eq_zero.mp hs]
  exact odd_even_coefficient_zero hf (by simp [paritySign_rectangle])

theorem levelFourier_zero {g : (ι → Bool) → ℝ} (hg : IsOdd g) : levelFourier g 0 = 0 := by
  simp only [levelFourier, Finset.powersetCard_zero, Finset.sum_singleton]
  exact odd_even_coefficient_zero hg (by simp [paritySign_setIndex])

theorem Ckl_one_row {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {g : Cube n → ℝ} {a : ℝ} (hΨ : IsOdd Ψ) (hg : IsOdd g)
    (hp : ∀ (i : Fin m) S, average (fun σ : Cube m =>
      sign (σ i) * Ψ (xorCube (rowCube σ) S)) = a * g (fun j => S (i,j)))
    (l : ℕ) : Ckl Ψ 1 l = (m : ℝ)*a*levelFourier g l := by
  by_cases hl : l = 0
  · simp [hl, Ckl_zero_right hΨ, levelFourier_zero hg]
  rw [Ckl_pair_sum Ψ (by omega) (by omega), Finset.powersetCard_one]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  simp_rw [row_rectangle_coefficient hΨ hg hp]
  simp [levelFourier, ← Finset.mul_sum, mul_assoc]

theorem Ckl_one_column {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {f : Cube m → ℝ} {b : ℝ} (hΨ : IsOdd Ψ) (hf : IsOdd f)
    (hp : ∀ (j : Fin n) S, average (fun τ : Cube n =>
      sign (τ j) * Ψ (xorCube (columnCube τ) S)) = b * f (fun i => S (i,j)))
    (k : ℕ) : Ckl Ψ k 1 = (n : ℝ)*b*levelFourier f k := by
  by_cases hk : k = 0
  · simp [hk, Ckl_zero_left hΨ, levelFourier_zero hf]
  rw [Ckl_pair_sum Ψ (by omega) (by omega), Finset.powersetCard_one]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk,
    column_rectangle_coefficient hΨ hf hp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_assoc, ← Finset.mul_sum, levelFourier]

end Cotype

end

end OAI
