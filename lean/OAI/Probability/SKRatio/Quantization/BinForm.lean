import Mathlib
import OAI.Probability.SKRatio.Quantization.BinFunctional

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

def siteMoment (p f : Fin n → ℝ) : ℝ := (∑ i, p i*f i)/sqrt (n:ℝ)

lemma siteMoment_bin {σ : Fin n → α} (hcount : ∀ a, 0<count σ a)
    (z : Parameters α) (u : Directions σ) (f : α → ℝ) :
    siteMoment (vectorOf z u) (fun i => f (σ i)) = moment (binT σ) (paramB z) f := by
  simpa only [siteMoment,Fintype.card_fin] using vectorOf_moment hcount z u f

lemma momentProduct (p f q k : Fin n → ℝ) :
    siteMoment p f*siteMoment q k=(∑ i, p i*f i)*(∑ i, q i*k i)/(n:ℝ) := by
  unfold siteMoment
  rw [div_mul_div_comm,←pow_two,sq_sqrt (Nat.cast_nonneg n)]

def correctedForm (β : ℝ) (H p : Fin n → ℝ) : ℝ :=
  siteMoment p H*siteMoment p (fun i => v (H i))+
  siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
  β^2*siteMoment p (fun _ => 1)*siteMoment p (fun i => v (H i))+
  2*β^2*siteMoment p (fun _ => 1)*siteMoment p (fun i => m (H i)*v (H i))+
  diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p+
  weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p

lemma deterministic_corrected (β : ℝ) (H p : Fin n → ℝ) :
    deterministicForm β H p = correctedForm β H p+
      (β^2-(∑ i, H i)/(n:ℝ))*siteMoment p (fun _ => 1)*siteMoment p (fun i => v (H i)) := by
  unfold deterministicForm correctedForm rankForm
  simp only [mul_assoc]
  simp only [←mul_assoc,momentProduct,mul_one,Finset.sum_mul]
  ring

lemma diagonalForm_bin {σ : Fin n → α} (hcount : ∀ a, 0<count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF
        (fun i => compactWeight (h (σ i))) (vectorOf z u) =
      β^2*(∑ a, ∑ d, binT σ d^2*(v (h d)^2/(w (h a)+w (h d)))*
        ((paramB z a)^2+(paramR z a)^2)) := by
  let p := vectorOf z u
  let K : α → α → ℝ := fun a d => v (h d)^2/(w (h a)+w (h d))
  have he : diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF
      (fun i => compactWeight (h (σ i))) p =
      β^2/(n:ℝ)*(∑ i, ∑ j, p i^2*(1:ℝ)*K (σ i) (σ j)) := by
    simp only [diagonalForm,compactF_weight,Finset.sum_mul,Finset.mul_sum,K,mul_one]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,double_weighted σ (fun i => p i^2) (fun _ => 1) K]
  simp only [p,vectorOf_sq_sum hcount,sum_const_bin σ (fun _ => 1),mul_one,
    binT_sq,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  dsimp [K]
  ring

lemma weightedForm_bin {σ : Fin n → α} (hcount : ∀ a, 0<count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK
        (fun i => compactWeight (h (σ i))) (vectorOf z u) =
      β^2*(∑ a, ∑ d, binT σ a*paramB z a*kernel (h a) (h d)*(binT σ d*paramB z d)) := by
  let p := vectorOf z u
  have he : weightedForm (fun _ _ => β^2/(n:ℝ)) compactK
      (fun i => compactWeight (h (σ i))) p =
      β^2/(n:ℝ)*(∑ i, ∑ j, p i*p j*kernel (h (σ i)) (h (σ j))) := by
    simp only [weightedForm,quadratic,compactK_weight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,double_weighted σ p p (fun a d => kernel (h a) (h d))]
  simp only [p,vectorOf_sum hcount,binT,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [show sqrt (count σ a:ℝ)/sqrt (n:ℝ)*paramB z a*kernel (h a) (h d)*
      (sqrt (count σ d:ℝ)/sqrt (n:ℝ)*paramB z d) =
    (sqrt (count σ a:ℝ)*paramB z a*sqrt (count σ d:ℝ)*paramB z d*kernel (h a) (h d))/
      (sqrt (n:ℝ))^2 by ring,
    sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem correctedForm_bin {σ : Fin n → α} (hcount : ∀ a, 0<count σ a)
    (β : ℝ) (h : α → ℝ) (z : Parameters α) (u : Directions σ) :
    correctedForm β (fun i => h (σ i)) (vectorOf z u) = finiteA β (binT σ) h z := by
  unfold correctedForm
  rw [diagonalForm_bin hcount,weightedForm_bin hcount]
  simp only [siteMoment_bin hcount z u h,siteMoment_bin hcount z u (fun a => v (h a)),
    siteMoment_bin hcount z u (fun _ => 1),siteMoment_bin hcount z u (fun a => h a*v (h a)),
    siteMoment_bin hcount z u (fun a => m (h a)*v (h a))]
  rfl

end SKRatio.Bins

end

end OAI
