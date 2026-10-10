import OAI.Combinatorics.BooleanFunctions.FiniteCLT
import OAI.Combinatorics.BooleanFunctions.Projection
import OAI.Combinatorics.BooleanFunctions.SoftEvent

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

abbrev EventSpace (α ι : Type*) := α × (ι → α)
abbrev FullSpace (α ι : Type*) := EventSpace α ι × α

def oldSum (T : α → ℝ) (x : EventSpace α ι) : ℝ := T x.1 + ∑ i, T (x.2 i)
def totalSum (T : α → ℝ) (x : FullSpace α ι) : ℝ := oldSum T x.1 + T x.2
def oldLabels (F : α → β) (x : EventSpace α ι) : EventSpace β ι :=
  (F x.1,fun i => F (x.2 i))
def observation (F : α → β) (A : EventSpace β ι → Prop) (x : FullSpace α ι) :
    EventSpace β ι ⊕ β :=
  if A (oldLabels F x.1) then Sum.inr (F x.2) else Sum.inl (oldLabels F x.1)
def predictor (t : β → ℝ) (b : ℝ) : EventSpace β ι ⊕ β → ℝ :=
  Sum.elim (oldSum t) (fun y => b+t y)

omit [Fintype β] [Fintype ι] in
theorem average_prod_add_sq {δ : Type*} [Fintype δ] [Nonempty δ]
    (f : α → ℝ) (g : δ → ℝ) :
    average (fun x : α × δ => (f x.1+g x.2)^2) =
      average (fun x => (f x)^2)+2*average f*average g+average (fun y => (g y)^2) := by
  have he : (fun x : α × δ => (f x.1+g x.2)^2) =
      fun x => (f x.1)^2+2*f x.1*g x.2+(g x.2)^2 := by funext x; ring
  rw [he,average_prod]
  simp only [average_add,average_const,average_const_mul,average_mul_const]

omit [Fintype β] in
theorem oldSum_zero (T : α → ℝ) (h0 : average T = 0) :
    average (oldSum (ι := ι) T) = 0 := by
  have hi (j : ι) : average (fun x : ι → α => T (x j)) = average T := by
    convert average_pi_eval j T using 1
    congr 1
    exact Subsingleton.elim _ _
  unfold oldSum
  rw [average_prod]
  simp only [average_add,average_const,average_sum,hi,h0,Finset.sum_const_zero,add_zero]

omit [Fintype β] in
theorem oldSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : EventSpace α ι => (oldSum T x)^2) = Fintype.card ι+1 := by
  have h := FiniteMoments.normalized_product_centered_sq
    (fun (_ : ι) (_ : α) => (1:ℝ)) (fun _ => average_const 1)
    (fun _ => T) (by simpa using fun (_ : ι) => h0)
  simp only [Finset.prod_const_one,one_mul,h1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  have h' : average (fun x : ι → α => (∑ i, T (x i))^2) = (Fintype.card ι : ℝ) := by
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _
  simp only [oldSum]
  rw [average_prod_add_sq T (fun z : ι → α => ∑ i, T (z i)),h0,h1,h']
  ring

omit [Fintype β] in
theorem totalSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : FullSpace α ι => (totalSum T x)^2) = Fintype.card ι+2 := by
  simp only [totalSum]
  rw [average_prod_add_sq,oldSum_sq T h0 h1,h0,h1]
  ring

omit [Fintype β] in
theorem prediction_error (F : α → β) (A : EventSpace β ι → Prop)
    (T : α → ℝ) (t : β → ℝ) (ht : ∀ a, t (F a) = T a) (b : ℝ)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : FullSpace α ι => (totalSum T x-predictor t b (observation F A x))^2) =
      1-SoftEvent.deficit T b (fun z => if A (oldLabels F z) then 1 else 0) := by
  have he (z : EventSpace α ι) (w : α) :
      (totalSum T (z,w)-predictor t b (observation F A (z,w)))^2 =
      if A (oldLabels F z) then (oldSum T z-b)^2 else (T w)^2 := by
    by_cases ha : A (oldLabels F z)
    · have ho : observation F A (z,w) = Sum.inr (F w) := ite_eq_left ha
      rw [ho,ite_eq_left ha]
      simp only [predictor,Sum.elim_inr,totalSum,ht]
      congr 1; ring
    · have ho : observation F A (z,w) = Sum.inl (oldLabels F z) := ite_eq_right ha
      rw [ho,ite_eq_right ha]
      simp only [predictor,Sum.elim_inl,totalSum,oldSum,oldLabels,ht]
      congr 1; ring
  rw [average_prod]
  simp_rw [he]
  have hi (z : EventSpace α ι) :
      average (fun w : α => if A (oldLabels F z) then (oldSum T z-b)^2 else (T w)^2) =
      1-(if A (oldLabels F z) then 1 else 0)*(1-(oldSum T z-b)^2) := by
    by_cases ha : A (oldLabels F z) <;> simp [ha,average_const,h1]
  simp_rw [hi]
  rw [average_sub,average_const]
  unfold SoftEvent.deficit
  congr 1
  congr 1
  exact Subsingleton.elim _ _

theorem retained_gain (F : α → β) (A : EventSpace β ι → Prop)
    (T : α → ℝ) (t : β → ℝ) (ht : ∀ a, t (F a) = T a) (b c : ℝ)
    (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1)
    (hc : c < SoftEvent.deficit T b (fun z => if A (oldLabels F z) then 1 else 0)) :
    Fintype.card ι+1+c < average (fun x => (conditionalAverage (observation F A) (totalSum T) x)^2) := by
  have h := conditionalAverage_lower_bound (observation F A) (totalSum T) (predictor t b)
  rw [totalSum_sq T h0 h1,prediction_error F A T t ht b h1] at h
  linarith

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι]

abbrev Slots (ι : Type*) := Option (Option ι)

def fullEquiv (α ι : Type*) : (Slots ι → α) ≃ FullSpace α ι where
  toFun f := ((f (some none), fun i => f (some (some i))),f none)
  invFun x j := match j with
    | none => x.2
    | some none => x.1.1
    | some (some i) => x.1.2 i
  left_inv f := by funext j; cases j with | none => rfl | some j => cases j <;> rfl
  right_inv _ := rfl

omit [Fintype α] [Nonempty α] [Fintype β] in
theorem sum_full (T : α → ℝ) (x : Slots ι → α) :
    (∑ j, T (x j)) = totalSum T (fullEquiv α ι x) := by
  simp only [Fintype.sum_option,totalSum,oldSum,fullEquiv,Equiv.coe_fn_mk]
  ring

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

theorem full_conditional_sum (F : α → β) (A : EventSpace β ι → Prop) (g : α → ℝ) :
    conditionalAverage (observation F A) (totalSum g) =
      conditionalAverage (observation F A) (totalSum (conditionalAverage F g)) := by
  let e := fullEquiv α ι
  let H : (Slots ι → β) → EventSpace β ι ⊕ β := observation id A ∘ fullEquiv β ι
  have hp := Projection.pi_conditional_sum (κ := Slots ι) F H g
  have he : (fun x : Slots ι → α => H (fun j => F (x j))) = observation F A ∘ e := rfl
  have hg : (fun x : Slots ι → α => ∑ j, g (x j)) = totalSum g ∘ e := by
    funext x; exact sum_full g x
  have hg' : (fun x : Slots ι → α => ∑ j, conditionalAverage F g (x j)) =
      totalSum (conditionalAverage F g) ∘ e := by
    funext x; exact sum_full _ x
  rw [he,hg,hg',Projection.conditional_equiv e,Projection.conditional_equiv e] at hp
  funext x
  have hx := congrFun hp (e.symm x)
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hx

end Switching
end SquareRootDegree

end

end OAI
