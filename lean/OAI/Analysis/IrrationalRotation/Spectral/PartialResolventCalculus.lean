import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace Invariant233.PartialResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (H : E →ₗ.[ℂ] E) (R : E →L[ℂ] E)
variable (hD : ∀ x : E, R x ∈ H.domain)
variable (hHR : ∀ x : E, H ⟨R x, hD x⟩ = x - R x)
variable (hRH : ∀ x : H.domain, R ((x : E) + H x) = x)

include hD hHR

theorem injective : Function.Injective R := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change R x = 0 at hx
  have hz : (⟨R x, hD x⟩ : H.domain) = 0 := Subtype.ext hx
  have heq := hHR x
  rw [hz, H.map_zero, hx, sub_zero] at heq
  exact heq.symm

include hRH

omit hHR in

theorem domain_eq_range : H.domain = R.range := by
  ext x
  constructor
  · intro hx
    exact ⟨x + H ⟨x, hx⟩, hRH ⟨x, hx⟩⟩
  · rintro ⟨y, rfl⟩
    exact hD y

theorem range_one_sub : (1 - R).range = LinearMap.range H.toFun := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨R x, hD x⟩, hHR x⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(x : E) + H x, ?_⟩
    change (x : E) + H x - R ((x : E) + H x) = H x
    rw [hRH]
    exact add_sub_cancel_left _ _

omit hRH in

theorem injective_one_sub (hH : Function.Injective H) :
    Function.Injective (1 - R : E →L[ℂ] E) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hzero : H ⟨R x, hD x⟩ = H 0 := by
    rw [H.map_zero, hHR]
    exact hx
  have hRx : R x = 0 := congrArg Subtype.val (hH hzero)
  exact injective H R hD hHR (by simpa only [map_zero] using hRx)

omit hRH in

theorem one_sub_mem_inverse_domain (x : E) :
    (1 - R) x ∈ H.inverse.domain := by
  rw [LinearPMap.inverse_domain]
  exact ⟨⟨R x, hD x⟩, hHR x⟩

omit hRH in

theorem inverse_one_sub (hH : Function.Injective H) (x : E) :
    H.inverse ⟨(1 - R) x, one_sub_mem_inverse_domain H R hD hHR x⟩ = R x := by
  apply LinearPMap.inverse_apply_eq (LinearPMap.ker_eq_bot.mpr hH)
    (x := ⟨R x, hD x⟩)
  exact hHR x

theorem inverse_domain_eq_range : H.inverse.domain = (1 - R).range := by
  rw [LinearPMap.inverse_domain, range_one_sub H R hD hHR hRH]

omit hD hHR in

theorem one_sub_apply_add_inverse (hH : Function.Injective H)
    (y : H.inverse.domain) :
    (1 - R) ((y : E) + H.inverse y) = y := by
  have hy : (y : E) ∈ LinearMap.range H.toFun := by
    rw [← LinearPMap.inverse_domain]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  have hinv : H.inverse y = (x : E) :=
    LinearPMap.inverse_apply_eq (LinearPMap.ker_eq_bot.mpr hH) hx
  rw [hinv, ← hx]
  change H x + (x : E) - R (H x + (x : E)) = H x
  rw [add_comm (H x) (x : E), hRH]
  exact add_sub_cancel_left _ _

omit hRH in

theorem isSymmetric (hH : H.IsFormalAdjoint H) : R.toLinearMap.IsSymmetric := by
  intro x y
  have heq := hH ⟨R x, hD x⟩ ⟨R y, hD y⟩
  rw [hHR, hHR] at heq
  simp only [inner_sub_left, inner_sub_right] at heq
  exact (sub_left_inj.mp heq).symm

omit hRH in

theorem norm_sq_le_re_inner
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) (x : E) :
    ‖R x‖ ^ 2 ≤ (inner ℂ (R x) x).re := by
  have hp := hpos ⟨R x, hD x⟩
  rw [hHR] at hp
  change 0 ≤ (inner ℂ (R x) (x - R x)).re at hp
  rw [inner_sub_right, Complex.sub_re] at hp
  rw [show (inner ℂ (R x) (R x)).re = ‖R x‖ ^ 2 from
    inner_self_eq_norm_sq (𝕜 := ℂ) (R x)] at hp
  exact sub_nonneg.mp hp

omit hRH in

theorem one_sub_norm_sq_le_re_inner
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) (x : E) :
    ‖(1 - R) x‖ ^ 2 ≤ (inner ℂ ((1 - R) x) x).re := by
  have hp := hpos ⟨R x, hD x⟩
  rw [hHR] at hp
  have hx : R x = x - (1 - R) x := by
    change R x = x - (x - R x)
    rw [sub_sub_cancel]
  change 0 ≤ (inner ℂ (R x) ((1 - R) x)).re at hp
  rw [hx, inner_sub_left, Complex.sub_re] at hp
  rw [show (inner ℂ ((1 - R) x) ((1 - R) x)).re = ‖(1 - R) x‖ ^ 2 from
    inner_self_eq_norm_sq (𝕜 := ℂ) ((1 - R) x)] at hp
  rw [show (inner ℂ x ((1 - R) x)).re = (inner ℂ ((1 - R) x) x).re from
    inner_re_symm (𝕜 := ℂ) x ((1 - R) x)] at hp
  exact sub_nonneg.mp hp

omit hRH in

theorem isPositive (hH : H.IsFormalAdjoint H)
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) :
    R.IsPositive := by
  refine ⟨isSymmetric H R hD hHR hH, fun x => ?_⟩
  exact (sq_nonneg ‖R x‖).trans (norm_sq_le_re_inner H R hD hHR hpos x)

omit hRH in

theorem one_sub_isPositive (hH : H.IsFormalAdjoint H)
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) :
    (1 - R : E →L[ℂ] E).IsPositive := by
  refine ⟨?_, fun x => ?_⟩
  · intro x y
    change inner ℂ (x - R x) y = inner ℂ x (y - R y)
    rw [inner_sub_left, inner_sub_right]
    have hs := isSymmetric H R hD hHR hH x y
    change inner ℂ (R x) y = inner ℂ x (R y) at hs
    rw [hs]
  · exact (sq_nonneg ‖(1 - R) x‖).trans
      (one_sub_norm_sq_le_re_inner H R hD hHR hpos x)

omit hD hHR hRH in
private theorem norm_le_one_of_quadratic (T : E →L[ℂ] E)
    (hT : ∀ x, ‖T x‖ ^ 2 ≤ (inner ℂ (T x) x).re) : ‖T‖ ≤ 1 := by
  apply T.opNorm_le_bound (by norm_num)
  intro x
  rw [one_mul]
  have hinner := re_inner_le_norm (𝕜 := ℂ) (T x) x
  change (inner ℂ (T x) x).re ≤ ‖T x‖ * ‖x‖ at hinner
  have hquad := hT x
  have hnorm := norm_nonneg (T x)
  by_contra h
  have hstrict : ‖x‖ < ‖T x‖ := lt_of_not_ge h
  nlinarith [norm_nonneg x]

omit hRH in

theorem norm_le_one
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) : ‖R‖ ≤ 1 :=
  norm_le_one_of_quadratic R (norm_sq_le_re_inner H R hD hHR hpos)

omit hRH in

theorem one_sub_norm_le_one
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) :
    ‖(1 - R : E →L[ℂ] E)‖ ≤ 1 :=
  norm_le_one_of_quadratic (1 - R) (one_sub_norm_sq_le_re_inner H R hD hHR hpos)

variable [CompleteSpace E]

omit hRH in

theorem isSelfAdjoint (hH : H.IsFormalAdjoint H) : IsSelfAdjoint R :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric H R hD hHR hH)

omit hRH in

theorem one_sub_isSelfAdjoint (hH : H.IsFormalAdjoint H) :
    IsSelfAdjoint (1 - R : E →L[ℂ] E) :=
  by
  change star (1 - R) = 1 - R
  rw [star_sub, star_one, isSelfAdjoint H R hD hHR hH]

end Invariant233.PartialResolvent

end

end OAI
