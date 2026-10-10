import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosBoundaryLoss
noncomputable def loss2Kernel (t x : ℝ) : ℝ :=
  ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
noncomputable def loss3Kernel (t u x : ℝ) : ℝ :=
  ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
noncomputable def L1 : ℝ := ∫ x : ℝ in 1..2,2*x/3
noncomputable def L2 : ℝ := ∫ t : ℝ in 1..2,∫ x : ℝ in t..2,
  ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
noncomputable def L3 : ℝ := ∫ t : ℝ in 1..2,∫ u : ℝ in t..2,∫ x : ℝ in u..2,
  ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

noncomputable def inner2Primitive (t x : ℝ) : ℝ :=
  x
  + ((-1:ℝ) * x * (t^2)⁻¹)
  + ((-2:ℝ) * (t^1)⁻¹ * (Real.log x))
  + ((1/4:ℝ) * (t^1)⁻¹ * (x^2))
  + ((1/36:ℝ) * (t^2)⁻¹ * (x^3))
  + ((2/3:ℝ) * t * (Real.log x))
  + ((4/3:ℝ) * (t^2)⁻¹ * (Real.log x))

theorem inner2Primitive_deriv (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => inner2Primitive t x) (loss2Kernel t x) x := by
  unfold inner2Primitive loss2Kernel
  have h0 := (hasDerivAt_id x)
  have h1 := (((hasDerivAt_const x (-1:ℝ)).mul (hasDerivAt_id x)).mul (hasDerivAt_const x (t^2)⁻¹))
  have h2 := (((hasDerivAt_const x (-2:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h3 := (((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h4 := (((hasDerivAt_const x (1/36:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).pow 3))
  have h5 := (((hasDerivAt_const x (2/3:ℝ)).mul (hasDerivAt_const x t)).mul ((hasDerivAt_id x).log (by positivity)))
  have h6 := (((hasDerivAt_const x (4/3:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have hd := ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6)
  convert! hd using 1
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

noncomputable def middle3Kernel (t u : ℝ) : ℝ :=
  (-1:ℝ)
  + ((1/2:ℝ) * (t^2)⁻¹)
  + ((-1:ℝ) * (Real.log u))
  + ((2:ℝ) * (t^1)⁻¹)
  + ((2:ℝ) * (u^1)⁻¹)
  + ((t^1)⁻¹ * (u^1)⁻¹)
  + ((1/2:ℝ) * u * (t^2)⁻¹)
  + ((-14/9:ℝ) * (t^2)⁻¹ * (u^1)⁻¹)
  + ((-13/72:ℝ) * (t^2)⁻¹ * (u^2))
  + ((-5/4:ℝ) * u * (t^1)⁻¹)
  + ((1/2:ℝ) * u * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-2/3:ℝ) * t * (u^1)⁻¹ * (Real.log u))
  + ((-1/2:ℝ) * u * (t^1)⁻¹ * (Real.log u))
  + ((-1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log u))
  + ((1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log (2:ℝ)))
  + ((2/3:ℝ) * t * (u^1)⁻¹ * (Real.log (2:ℝ)))
  + (Real.log (2:ℝ))

noncomputable def inner3Primitive (t u x : ℝ) : ℝ :=
  (x * (t^1)⁻¹)
  + (x * (u^1)⁻¹)
  + ((1/8:ℝ) * (t^2)⁻¹ * (x^2))
  + ((1/2:ℝ) * u * (t^1)⁻¹ * (Real.log x))
  + ((-7/36:ℝ) * (t^2)⁻¹ * (u^1)⁻¹ * (x^3))
  + ((1/4:ℝ) * u * x * (t^2)⁻¹)
  + ((1/4:ℝ) * (t^1)⁻¹ * (u^1)⁻¹ * (x^2))
  + ((1/12:ℝ) * (t^2)⁻¹ * (u^2) * (Real.log x))
  + ((2/3:ℝ) * t * (u^1)⁻¹ * (Real.log x))
  + (Real.log x)

theorem inner3Primitive_deriv (t u x : ℝ) (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => inner3Primitive t u x) (loss3Kernel t u x) x := by
  unfold inner3Primitive loss3Kernel
  have h0 := ((hasDerivAt_id x).mul (hasDerivAt_const x (t^1)⁻¹))
  have h1 := ((hasDerivAt_id x).mul (hasDerivAt_const x (u^1)⁻¹))
  have h2 := (((hasDerivAt_const x (1/8:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h3 := ((((hasDerivAt_const x (1/2:ℝ)).mul (hasDerivAt_const x u)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h4 := ((((hasDerivAt_const x (-7/36:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).pow 3))
  have h5 := ((((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x u)).mul (hasDerivAt_id x)).mul (hasDerivAt_const x (t^2)⁻¹))
  have h6 := ((((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h7 := ((((hasDerivAt_const x (1/12:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul (hasDerivAt_const x (u^2))).mul ((hasDerivAt_id x).log (by positivity)))
  have h8 := ((((hasDerivAt_const x (2/3:ℝ)).mul (hasDerivAt_const x t)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h9 := ((hasDerivAt_id x).log (by positivity))
  have hd := (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9)
  convert! hd using 1
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

noncomputable def middle3Primitive (t u : ℝ) : ℝ :=
  ((2:ℝ) * (Real.log u))
  + (u * (Real.log (2:ℝ)))
  + ((t^1)⁻¹ * (Real.log u))
  + ((1/2:ℝ) * u * (t^2)⁻¹)
  + ((-1:ℝ) * u * (Real.log u))
  + ((2:ℝ) * u * (t^1)⁻¹)
  + ((-14/9:ℝ) * (t^2)⁻¹ * (Real.log u))
  + ((-11/216:ℝ) * (t^2)⁻¹ * (u^3))
  + ((-1/2:ℝ) * (t^1)⁻¹ * (u^2))
  + ((-1/3:ℝ) * t * ((Real.log u)^2))
  + ((1/4:ℝ) * (t^2)⁻¹ * (u^2))
  + ((-1/4:ℝ) * (t^1)⁻¹ * (u^2) * (Real.log u))
  + ((-1/36:ℝ) * (t^2)⁻¹ * (u^3) * (Real.log u))
  + ((1/4:ℝ) * (t^1)⁻¹ * (u^2) * (Real.log (2:ℝ)))
  + ((1/36:ℝ) * (t^2)⁻¹ * (u^3) * (Real.log (2:ℝ)))
  + ((2/3:ℝ) * t * (Real.log (2:ℝ)) * (Real.log u))

theorem middle3Primitive_deriv (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => middle3Primitive t u) (middle3Kernel t u) u := by
  unfold middle3Primitive middle3Kernel
  have h0 := ((hasDerivAt_const u (2:ℝ)).mul ((hasDerivAt_id u).log (by positivity)))
  have h1 := ((hasDerivAt_id u).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h2 := ((hasDerivAt_const u (t^1)⁻¹).mul ((hasDerivAt_id u).log (by positivity)))
  have h3 := (((hasDerivAt_const u (1/2:ℝ)).mul (hasDerivAt_id u)).mul (hasDerivAt_const u (t^2)⁻¹))
  have h4 := (((hasDerivAt_const u (-1:ℝ)).mul (hasDerivAt_id u)).mul ((hasDerivAt_id u).log (by positivity)))
  have h5 := (((hasDerivAt_const u (2:ℝ)).mul (hasDerivAt_id u)).mul (hasDerivAt_const u (t^1)⁻¹))
  have h6 := (((hasDerivAt_const u (-14/9:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).log (by positivity)))
  have h7 := (((hasDerivAt_const u (-11/216:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3))
  have h8 := (((hasDerivAt_const u (-1/2:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2))
  have h9 := (((hasDerivAt_const u (-1/3:ℝ)).mul (hasDerivAt_const u t)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h10 := (((hasDerivAt_const u (1/4:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 2))
  have h11 := ((((hasDerivAt_const u (-1/4:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul ((hasDerivAt_id u).log (by positivity)))
  have h12 := ((((hasDerivAt_const u (-1/36:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3)).mul ((hasDerivAt_id u).log (by positivity)))
  have h13 := ((((hasDerivAt_const u (1/4:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h14 := ((((hasDerivAt_const u (1/36:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3)).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h15 := ((((hasDerivAt_const u (2/3:ℝ)).mul (hasDerivAt_const u t)).mul (hasDerivAt_const u (Real.log (2:ℝ)))).mul ((hasDerivAt_id u).log (by positivity)))
  have hd := (((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15)
  convert! hd using 1
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

noncomputable def reduced2 (t : ℝ) : ℝ :=
  (2:ℝ)
  + ((2:ℝ) * (t^1)⁻¹)
  + ((-23/18:ℝ) * t)
  + ((-16/9:ℝ) * (t^2)⁻¹)
  + ((-2:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((2:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((-4/3:ℝ) * (t^2)⁻¹ * (Real.log t))
  + ((-2/3:ℝ) * t * (Real.log t))
  + ((2/3:ℝ) * t * (Real.log (2:ℝ)))
  + ((4/3:ℝ) * (t^2)⁻¹ * (Real.log (2:ℝ)))

noncomputable def reduced3 (t : ℝ) : ℝ :=
  (-9/4:ℝ)
  + ((-2:ℝ) * (Real.log t))
  + ((2:ℝ) * (Real.log (2:ℝ)))
  + ((3/2:ℝ) * (t^1)⁻¹)
  + ((43/27:ℝ) * (t^2)⁻¹)
  + ((119/216:ℝ) * t)
  + ((t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-1:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((-23/18:ℝ) * t * (Real.log (2:ℝ)))
  + ((-14/9:ℝ) * (t^2)⁻¹ * (Real.log (2:ℝ)))
  + ((1/3:ℝ) * t * ((Real.log (2:ℝ))^2))
  + ((1/3:ℝ) * t * ((Real.log t)^2))
  + ((14/9:ℝ) * (t^2)⁻¹ * (Real.log t))
  + ((23/18:ℝ) * t * (Real.log t))
  + ((-2/3:ℝ) * t * (Real.log (2:ℝ)) * (Real.log t))

noncomputable def outer2Primitive (t : ℝ) : ℝ :=
  ((Real.log t)^2)
  + ((2:ℝ) * t)
  + ((2:ℝ) * (Real.log t))
  + ((-17/36:ℝ) * (t^2))
  + ((28/9:ℝ) * (t^1)⁻¹)
  + ((-2:ℝ) * (Real.log (2:ℝ)) * (Real.log t))
  + ((-4/3:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((-1/3:ℝ) * (t^2) * (Real.log t))
  + ((1/3:ℝ) * (t^2) * (Real.log (2:ℝ)))
  + ((4/3:ℝ) * (t^1)⁻¹ * (Real.log t))

theorem outer2Primitive_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => outer2Primitive t) (reduced2 t) t := by
  unfold outer2Primitive reduced2
  have h0 := (((hasDerivAt_id t).log (by positivity)).pow 2)
  have h1 := ((hasDerivAt_const t (2:ℝ)).mul (hasDerivAt_id t))
  have h2 := ((hasDerivAt_const t (2:ℝ)).mul ((hasDerivAt_id t).log (by positivity)))
  have h3 := ((hasDerivAt_const t (-17/36:ℝ)).mul ((hasDerivAt_id t).pow 2))
  have h4 := ((hasDerivAt_const t (28/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h5 := (((hasDerivAt_const t (-2:ℝ)).mul (hasDerivAt_const t (Real.log (2:ℝ)))).mul ((hasDerivAt_id t).log (by positivity)))
  have h6 := (((hasDerivAt_const t (-4/3:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h7 := (((hasDerivAt_const t (-1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul ((hasDerivAt_id t).log (by positivity)))
  have h8 := (((hasDerivAt_const t (1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h9 := (((hasDerivAt_const t (4/3:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul ((hasDerivAt_id t).log (by positivity)))
  have hd := (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9)
  convert! hd using 1
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Pi.inv_apply]
  field_simp
  ring

noncomputable def outer3Primitive (t : ℝ) : ℝ :=
  ((-85/27:ℝ) * (t^1)⁻¹)
  + ((-1/2:ℝ) * ((Real.log t)^2))
  + ((-1/4:ℝ) * t)
  + ((3/2:ℝ) * (Real.log t))
  + ((17/432:ℝ) * (t^2))
  + ((Real.log (2:ℝ)) * (Real.log t))
  + ((-2:ℝ) * t * (Real.log t))
  + ((2:ℝ) * t * (Real.log (2:ℝ)))
  + ((-17/36:ℝ) * (t^2) * (Real.log (2:ℝ)))
  + ((-14/9:ℝ) * (t^1)⁻¹ * (Real.log t))
  + ((1/6:ℝ) * (t^2) * ((Real.log (2:ℝ))^2))
  + ((1/6:ℝ) * (t^2) * ((Real.log t)^2))
  + ((14/9:ℝ) * (t^1)⁻¹ * (Real.log (2:ℝ)))
  + ((17/36:ℝ) * (t^2) * (Real.log t))
  + ((-1/3:ℝ) * (t^2) * (Real.log (2:ℝ)) * (Real.log t))

theorem outer3Primitive_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => outer3Primitive t) (reduced3 t) t := by
  unfold outer3Primitive reduced3
  have h0 := ((hasDerivAt_const t (-85/27:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h1 := ((hasDerivAt_const t (-1/2:ℝ)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h2 := ((hasDerivAt_const t (-1/4:ℝ)).mul (hasDerivAt_id t))
  have h3 := ((hasDerivAt_const t (3/2:ℝ)).mul ((hasDerivAt_id t).log (by positivity)))
  have h4 := ((hasDerivAt_const t (17/432:ℝ)).mul ((hasDerivAt_id t).pow 2))
  have h5 := ((hasDerivAt_const t (Real.log (2:ℝ))).mul ((hasDerivAt_id t).log (by positivity)))
  have h6 := (((hasDerivAt_const t (-2:ℝ)).mul (hasDerivAt_id t)).mul ((hasDerivAt_id t).log (by positivity)))
  have h7 := (((hasDerivAt_const t (2:ℝ)).mul (hasDerivAt_id t)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h8 := (((hasDerivAt_const t (-17/36:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h9 := (((hasDerivAt_const t (-14/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul ((hasDerivAt_id t).log (by positivity)))
  have h10 := (((hasDerivAt_const t (1/6:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t ((Real.log (2:ℝ))^2)))
  have h11 := (((hasDerivAt_const t (1/6:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h12 := (((hasDerivAt_const t (14/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h13 := (((hasDerivAt_const t (17/36:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul ((hasDerivAt_id t).log (by positivity)))
  have h14 := ((((hasDerivAt_const t (-1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ)))).mul ((hasDerivAt_id t).log (by positivity)))
  have hd := ((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14)
  convert! hd using 1
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Pi.inv_apply]
  field_simp
  ring

end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

theorem loss2_inner_integrable {t : ℝ} (ht : t ∈ Icc 1 2) :
    IntervalIntegrable (loss2Kernel t) volume t 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.2]
  intro x hx
  have hx0 : x ≠ 0 := by have := ht.1; have := hx.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold loss2Kernel
  fun_prop (disch := simp_all)

theorem loss2_inner_reduction {t : ℝ} (ht : t ∈ Icc 1 2) :
    (∫ x in t..2,loss2Kernel t x)=reduced2 t := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hd : ∀ x ∈ uIcc t 2, HasDerivAt (inner2Primitive t) (loss2Kernel t x) x := by
    intro x hx
    rw [uIcc_of_le ht.2] at hx
    exact inner2Primitive_deriv t x htpos (lt_of_lt_of_le htpos hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss2_inner_integrable ht)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  unfold inner2Primitive reduced2
  norm_num
  field_simp
  ring

theorem loss3_inner_integrable {t u : ℝ} (ht : t ∈ Icc 1 2) (hu : u ∈ Icc t 2) :
    IntervalIntegrable (loss3Kernel t u) volume u 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  have hu0 : u ≠ 0 := by have := ht.1; have := hu.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hu.2]
  intro x hx
  have hx0 : x ≠ 0 := by have := ht.1; have := hu.1; have := hx.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold loss3Kernel
  fun_prop (disch := simp_all)

theorem loss3_inner_reduction {t u : ℝ} (ht : t ∈ Icc 1 2) (hu : u ∈ Icc t 2) :
    (∫ x in u..2,loss3Kernel t u x)=middle3Kernel t u := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hupos : 0 < u := lt_of_lt_of_le htpos hu.1
  have hd : ∀ x ∈ uIcc u 2, HasDerivAt (inner3Primitive t u) (loss3Kernel t u x) x := by
    intro x hx
    rw [uIcc_of_le hu.2] at hx
    exact inner3Primitive_deriv t u x htpos hupos (lt_of_lt_of_le hupos hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss3_inner_integrable ht hu)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hu0 : u ≠ 0 := ne_of_gt hupos
  unfold inner3Primitive middle3Kernel
  norm_num
  field_simp
  ring

theorem loss3_middle_kernel_integrable {t : ℝ} (ht : t ∈ Icc 1 2) :
    IntervalIntegrable (middle3Kernel t) volume t 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.2]
  intro u hu
  have hu0 : u ≠ 0 := by have := ht.1; have := hu.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold middle3Kernel
  fun_prop (disch := simp_all)

theorem loss3_middle_reduction {t : ℝ} (ht : t ∈ Icc 1 2) :
    (∫ u in t..2,∫ x in u..2,loss3Kernel t u x)=reduced3 t := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hi : (∫ u in t..2,∫ x in u..2,loss3Kernel t u x)=∫ u in t..2,middle3Kernel t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact loss3_inner_reduction ht hu
  rw [hi]
  have hd : ∀ u ∈ uIcc t 2, HasDerivAt (middle3Primitive t) (middle3Kernel t u) u := by
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact middle3Primitive_deriv t u htpos (lt_of_lt_of_le htpos hu.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss3_middle_kernel_integrable ht)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  unfold middle3Primitive reduced3
  norm_num
  field_simp
  ring

end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

theorem reduced2_integrable : IntervalIntegrable reduced2 volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  intro t ht
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold reduced2
  fun_prop (disch := simp_all)

theorem reduced3_integrable : IntervalIntegrable reduced3 volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  intro t ht
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold reduced3
  fun_prop (disch := simp_all)

theorem loss3_middle_integrable {t : ℝ} (ht : t ∈ Icc 1 2) :
    IntervalIntegrable (fun u : ℝ => ∫ x in u..2,loss3Kernel t u x) volume t 2 := by
  apply (loss3_middle_kernel_integrable ht).congr_uIoo
  intro u hu
  rw [uIoo_of_le ht.2] at hu
  exact (loss3_inner_reduction ht ⟨hu.1.le,hu.2.le⟩).symm

theorem loss2_outer_integrable :
    IntervalIntegrable (fun t : ℝ => ∫ x in t..2,loss2Kernel t x) volume 1 2 := by
  apply reduced2_integrable.congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
  exact (loss2_inner_reduction ⟨ht.1.le,ht.2.le⟩).symm

theorem loss3_outer_integrable :
    IntervalIntegrable (fun t : ℝ => ∫ u in t..2,∫ x in u..2,loss3Kernel t u x) volume 1 2 := by
  apply reduced3_integrable.congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
  exact (loss3_middle_reduction ⟨ht.1.le,ht.2.le⟩).symm

theorem L1_integrable : IntervalIntegrable (fun x : ℝ => 2*x/3) volume 1 2 := by
  exact (continuous_const.mul continuous_id |>.div_const 3).intervalIntegrable 1 2

theorem L1_eq : L1=1 := by
  unfold L1
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul]
  norm_num

theorem L2_eq : L2=-(35:ℝ)/36-(Real.log 2)^2+3*Real.log 2 := by
  have hi : L2=∫ t in (1:ℝ)..2,reduced2 t := by
    unfold L2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact loss2_inner_reduction ht
  rw [hi]
  have hd : ∀ t ∈ uIcc (1:ℝ) 2, HasDerivAt outer2Primitive (reduced2 t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact outer2Primitive_deriv t (by have := ht.1; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd reduced2_integrable]
  unfold outer2Primitive
  norm_num
  ring

theorem L3_eq : L3=(623:ℝ)/432-(19:ℝ)/12*Real.log 2+(1:ℝ)/3*(Real.log 2)^2 := by
  have hi : L3=∫ t in (1:ℝ)..2,reduced3 t := by
    unfold L3
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact loss3_middle_reduction ht
  rw [hi]
  have hd : ∀ t ∈ uIcc (1:ℝ) 2, HasDerivAt outer3Primitive (reduced3 t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact outer3Primitive_deriv t (by have := ht.1; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd reduced3_integrable]
  unfold outer3Primitive
  norm_num
  ring

end ErdosBoundaryLoss

end

section

namespace ErdosBoundaryLoss

theorem log_two_bounds : (69:ℝ)/100 < Real.log 2 ∧ Real.log 2 < (7:ℝ)/10 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

theorem L2_lt : L2 < (64:ℝ)/100 := by
  rw [L2_eq]
  have h := log_two_bounds
  have hp := mul_pos (sub_pos.mpr h.2)
    (show 0 < 3-(7:ℝ)/10-Real.log 2 by linarith)
  nlinarith

theorem L3_lt : L3 < (51:ℝ)/100 := by
  rw [L3_eq]
  have h := log_two_bounds
  have hp := mul_pos (sub_pos.mpr h.1)
    (show 0 < (19:ℝ)/12-(Real.log 2+(69:ℝ)/100)/3 by linarith)
  nlinarith

theorem first_three_loss_lt : L1+L2+L3 < (43:ℝ)/20 := by
  rw [L1_eq]
  linarith [L2_lt,L3_lt]

end ErdosBoundaryLoss

end

end Erdos970

end OAI
