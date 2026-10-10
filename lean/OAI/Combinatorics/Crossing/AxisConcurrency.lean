import OAI.Combinatorics.Crossing.AxisSegments
import OAI.Combinatorics.Crossing.GenericPolynomialBox

namespace OAI

noncomputable section
namespace Zarankiewicz
open MvPolynomial
variable {m n : ℕ}

def axisConcurrency (a b c d e f : ℝ) : ℝ :=
  a*d*e*f+b*c*d*e+a*b*c*f-a*b*d*e-b*c*e*f-a*c*d*f

theorem axisSegmentPoint_line_equation (a b t : ℝ) :
    a*(axisSegmentPoint a b t).1+b*(axisSegmentPoint a b t).2=a*b := by
  rw [axisSegmentPoint_coordinates]
  ring

theorem axisConcurrency_zero_of_meeting (a b c d e f : ℝ) (z : Plane)
    (h₀ : a*z.1+b*z.2=a*b) (h₁ : c*z.1+d*z.2=c*d) (h₂ : e*z.1+f*z.2=e*f) :
    axisConcurrency a b c d e f=0 := by
  unfold axisConcurrency
  linear_combination -(c*f-d*e)*h₀-(b*e-a*f)*h₁-(a*d-b*c)*h₂

def axisConcurrencyPolynomial (e f g : BipartiteEdge m n) : MvPolynomial (BipartiteVertex m n) ℝ :=
  let a := X (Sum.inl e.1); let b := X (Sum.inr e.2)
  let c := X (Sum.inl f.1); let d := X (Sum.inr f.2)
  let u := X (Sum.inl g.1); let v := X (Sum.inr g.2)
  a*d*u*v+b*c*d*u+a*b*c*v-a*b*d*u-b*c*u*v-a*c*d*v

theorem axisConcurrencyPolynomial_eval (e f g : BipartiteEdge m n) (x : BipartiteVertex m n → ℝ) :
    eval x (axisConcurrencyPolynomial e f g)=
      axisConcurrency (x (Sum.inl e.1)) (x (Sum.inr e.2)) (x (Sum.inl f.1)) (x (Sum.inr f.2))
        (x (Sum.inl g.1)) (x (Sum.inr g.2)) := by
  simp [axisConcurrencyPolynomial,axisConcurrency]

theorem axisConcurrencyPolynomial_ne_zero (e f g : BipartiteEdge m n)
    (hef : e.1 ≠ f.1) (hgf : g.1 ≠ f.1) (hfe : f.2 ≠ e.2) (hge : g.2 ≠ e.2) :
    axisConcurrencyPolynomial e f g ≠ 0 := by
  let x : BipartiteVertex m n → ℝ
    | .inl i => if i=f.1 then 0 else 1
    | .inr p => if p=e.2 then 0 else 1
  intro h
  have hh := congrArg (eval x) h
  rw [axisConcurrencyPolynomial_eval] at hh
  norm_num [x,axisConcurrency,hef,hgf,hfe,hge] at hh

end Zarankiewicz

end

end OAI
