import OAI.NumberTheory.Ostmann.Construction.InitialMovingSlots

namespace OAI

/-! # Preserving the original retained prior in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def initialMovingRegularPrior {P : Type*} (b r : ℕ)
    (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ) :
    MovingRegularSlot 0 (r + r) (b + b) → P → ℝ :=
  fun i => Sum.elim (Fin.append μc μc) (Fin.append μb μb) i.2

theorem initial_retained_prior {P : Type*} (b r : ℕ) (μg : P → ℝ)
    (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (i : InitialRetainedSlot b r ⊕ InitialRetainedSlot b r) :
    (Sum.elim (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc))
      (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc))) i =
    Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc)
      (initialRetainedIndexEquiv b r i) := by
  rcases i with ((u | (i | i)) | (u | (i | i))) <;>
    simp only [initialRetainedIndexEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
      initialMovingRegularPrior, Fin.append_left, Fin.append_right]

private theorem initial_sum_prior_split {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
    (μ : I → P → ℝ) (ν : J → P → ℝ) (H : (I ⊕ J → P) → ℂ) :
    (∑ x : I ⊕ J → P, ((∏ i, Sum.elim μ ν i (x i) : ℝ) : ℂ) * H x) =
      ∑ l : I → P, ((∏ i, μ i (l i) : ℝ) : ℂ) *
        ∑ r : J → P, ((∏ i, ν i (r i) : ℝ) : ℂ) * H (Sum.elim l r) := by
  rw [← (Equiv.sumArrowEquivProdArrow I J P).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Complex.ofReal_mul, mul_assoc]
  rfl

theorem initial_retained_average {P : Type*} [Fintype P] (b r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (H : (InitialRetainedSlot b r ⊕ InitialRetainedSlot b r → P) → ℂ) :
    let ν := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
    (∑ yl : InitialRetainedSlot b r → P, ((∏ i, ν i (yl i) : ℝ) : ℂ) *
      ∑ yr : InitialRetainedSlot b r → P, ((∏ i, ν i (yr i) : ℝ) : ℂ) * H (Sum.elim yl yr)) =
    ∑ z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) i (z i) : ℝ) : ℂ) *
        H (z ∘ initialRetainedIndexEquiv b r) := by
  intro ν
  have hs := initial_sum_prior_split ν ν H
  simp only [finite_univ_canonical] at hs ⊢
  rw [← hs]
  have he := finite_prior_reindex (initialRetainedIndexEquiv b r).symm (Sum.elim ν ν) H
  simp only [Equiv.symm_symm, finite_univ_canonical] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro z _
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have h := initial_retained_prior b r μg μb μc ((initialRetainedIndexEquiv b r).symm i)
  rw [Equiv.apply_symm_apply] at h
  exact congrFun h (z i)

private def initialGiantAssignment (P : Type*) : P × P ≃ (Bool → P) where
  toFun x b := if b then x.1 else x.2
  invFun x := (x true, x false)
  left_inv := by intro x; rfl
  right_inv := by intro x; funext b; cases b <;> rfl

private theorem initial_bool_prior_average {P : Type*} [Fintype P]
    (μ : P → ℝ) (H : (Bool → P) → ℂ) :
    (∑ x : Bool → P, ((∏ b, μ (x b) : ℝ) : ℂ) * H x) =
      ∑ L : P, (μ L : ℂ) * ∑ R : P, (μ R : ℂ) * H (fun b => if b then L else R) := by
  rw [← (initialGiantAssignment P).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro L _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  simp only [initialGiantAssignment, Equiv.coe_fn_mk, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, ite_true, Complex.ofReal_mul]
  ring

theorem initialFrozenAmplitude_movingOrder (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) :
    initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr =
      ∑ z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P,
        ((∏ i, Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) i (z i) : ℝ) : ℂ) *
          let x := Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm
          w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0 := by
  have h := initial_retained_average b r μg μb μc (fun z =>
    let x := Fin.append (initialHalfAssemble b d r sl (z ∘ Sum.inl))
      (initialHalfAssemble b d r sr (z ∘ Sum.inr))
    w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0)
  change initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  have hx := initial_reassembled_moving_tuple b d r sl sr z
  simp only [Function.comp_assoc] at hx ⊢
  rw [hx]

/-- Both original giants and all regular marginals keep their exact laws. -/
theorem initialFrozenAmplitude_moving (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) :
    initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr =
      ∑ XL : P, (μg XL : ℂ) * ∑ XR : P, (μg XR : ℂ) *
        ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
          ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) *
            let x := initialMovingTuple b d r sl sr XL XR y
            w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0 := by
  rw [initialFrozenAmplitude_movingOrder]
  let K := fun z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P =>
    let x := Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm
    w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0
  have hs := initial_sum_prior_split (fun _ : Bool => μg)
    (initialMovingRegularPrior b r μb μc) K
  simp only [finite_univ_canonical] at hs ⊢
  rw [hs]
  have hb := initial_bool_prior_average μg (fun z =>
    ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) * K (Sum.elim z y))
  simp only [finite_univ_canonical] at hb
  rw [hb]
  rfl

end Ostmann

end OAI
