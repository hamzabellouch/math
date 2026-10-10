import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAxisIntegral2

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped Topology ContDiff

noncomputable def outgoingPowerND (α : ℝ) (c : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (Complex.I*s)*c*(s^(-α) : ℝ)

lemma outgoingPowerND_hasDerivAt (α : ℝ) (c : ℂ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (outgoingPowerND α c)
      (outgoingPowerND α c s*(Complex.I-(α:ℂ)*(s:ℂ)⁻¹)) s := by
  have he := (((hasDerivAt_id s).ofReal_comp.const_mul Complex.I).cexp).mul_const c
  have hp := (Real.hasDerivAt_rpow_const (p := -α) (Or.inl hs.ne')).ofReal_comp
  convert he.mul hp using 1 <;> try rfl
  rw [Real.rpow_sub hs]
  simp only [Real.rpow_one,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,id_eq,
    Complex.ofReal_one]
  dsimp [outgoingPowerND]
  ring

noncomputable def outgoingProfileND (α : ℝ) (c : ℂ) (H : ℝ → ℂ) (s : ℝ) : ℂ :=
  outgoingPowerND α c s * H s⁻¹

lemma outgoingProfileND_hasDerivAt (α : ℝ) (c : ℂ) {H : ℝ → ℂ}
    {s : ℝ} (hs : 0 < s) {v : ℂ} (hv : HasDerivAt H v s⁻¹) :
    HasDerivAt (outgoingProfileND α c H)
      (outgoingPowerND α c s*((Complex.I-(α:ℂ)*(s:ℂ)⁻¹)*H s⁻¹ -
        (s:ℂ)⁻¹^2*v)) s := by
  have hi := hv.scomp s (hasDerivAt_inv hs.ne')
  convert (outgoingPowerND_hasDerivAt α c hs).mul hi using 1 <;> try rfl
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow]
  dsimp
  ring

lemma outgoingProfileND_deriv {α : ℝ} {c : ℂ} {H : ℝ → ℂ}
    (hH : Differentiable ℝ H) {s : ℝ} (hs : 0 < s) :
    deriv (outgoingProfileND α c H) s =
      outgoingPowerND α c s*((Complex.I-(α:ℂ)*(s:ℂ)⁻¹)*H s⁻¹ -
        (s:ℂ)⁻¹^2*deriv H s⁻¹) :=
  (outgoingProfileND_hasDerivAt α c hs (hH s⁻¹).hasDerivAt).deriv

lemma outgoingProfileND_deriv_hasDerivAt {α : ℝ} {c : ℂ} {H : ℝ → ℂ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H))
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv (outgoingProfileND α c H))
      (outgoingPowerND α c s *
        (((Complex.I-(α:ℂ)*(s:ℂ)⁻¹)^2+(α:ℂ)*(s:ℂ)⁻¹^2)*H s⁻¹ +
          (-2*(Complex.I-(α:ℂ)*(s:ℂ)⁻¹)*(s:ℂ)⁻¹^2+2*(s:ℂ)⁻¹^3)*deriv H s⁻¹ +
          (s:ℂ)⁻¹^4*deriv (deriv H) s⁻¹)) s := by
  have hi := hasDerivAt_inv hs.ne'
  have hiC := hi.ofReal_comp
  have hq := (hasDerivAt_const s Complex.I).sub (hiC.const_mul (α:ℂ))
  have h₀ := (hH s⁻¹).hasDerivAt.scomp s hi
  have h₁ := (hH' s⁻¹).hasDerivAt.scomp s hi
  have ht := (outgoingPowerND_hasDerivAt α c hs).mul
    ((hq.mul h₀).sub ((hiC.pow 2).mul h₁))
  have he : deriv (outgoingProfileND α c H) =ᶠ[nhds s]
      (fun x => outgoingPowerND α c x*((Complex.I-(α:ℂ)*(x⁻¹:ℝ))*H x⁻¹ -
        (x⁻¹:ℝ)^2*deriv H x⁻¹)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hs] with x hx
    simpa using outgoingProfileND_deriv hH hx
  apply HasDerivAt.congr_of_eventuallyEq (f := fun x => outgoingPowerND α c x*
      ((Complex.I-(α:ℂ)*(x⁻¹:ℝ))*H x⁻¹ - (x⁻¹:ℝ)^2*deriv H x⁻¹)) _ he
  convert ht using 1 <;> try rfl
  simp only [Function.comp_def,Complex.real_smul,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
  push_cast
  simp only [inv_pow]
  ring

lemma radialHelmholtz_outgoingProfileND {α : ℝ} {c : ℂ} {H : ℝ → ℂ}
    (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H))
    {s : ℝ} (hs : 0 < s) :
    -(s:ℂ)^2*(outgoingProfileND α c H s + deriv (deriv (outgoingProfileND α c H)) s) -
      2*(α:ℂ)*s*deriv (outgoingProfileND α c H) s =
      outgoingPowerND α c s *
        ((α:ℂ)*(α-1)*H s⁻¹ + 2*Complex.I*deriv H s⁻¹ -
          2*(s:ℂ)⁻¹*deriv H s⁻¹ - (s:ℂ)⁻¹^2*deriv (deriv H) s⁻¹) := by
  rw [outgoingProfileND_deriv hH hs,(outgoingProfileND_deriv_hasDerivAt hH hH' hs).deriv]
  unfold outgoingProfileND
  have hsC : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  field_simp [hsC]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff Topology

lemma nat_cast_le_inftyND (j : ℕ) : (j : WithTop ℕ∞) ≤ (↑(⊤:ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)

@[fun_prop] lemma complex_coordinate_contDiffND (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff

lemma smooth_deriv_complexND {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (deriv H) := by
  exact ContDiff.deriv' (by simpa using hH)

lemma complex_coordinate_jetsND (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => (t:ℂ)) 0 = if j=1 then 1 else 0 := by
  have hd : deriv (fun t : ℝ => (t:ℂ)) = fun _ => (1:ℂ) := by
    funext t
    simpa using (hasDerivAt_id t).ofReal_comp.deriv
  cases j with
  | zero => simp
  | succ j =>
    rw [iteratedDeriv_succ',hd]
    cases j <;> simp [iteratedDeriv_const]

lemma iteratedDeriv_coordinate_mulND {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    iteratedDeriv (j+1) (fun t : ℝ => (t:ℂ)*H t) 0 =
      (j+1:ℂ)*iteratedDeriv j H 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (hH.of_le (nat_cast_le_inftyND _)).contDiffAt]
  simp only [complex_coordinate_jetsND,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp [Nat.choose_one_right]

lemma iteratedDeriv_coordinate_derivND {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => (t:ℂ)*deriv H t) 0 =
      (j:ℂ)*iteratedDeriv j H 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [iteratedDeriv_coordinate_mulND (smooth_deriv_complexND hH) j,← iteratedDeriv_succ']
    push_cast
    rfl

lemma iteratedDeriv_coordinate_sq_derivND {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => (t:ℂ)^2*deriv (deriv H) t) 0 =
      (j:ℂ)*((j:ℂ)-1)*iteratedDeriv j H 0 := by
  have h₂ := smooth_deriv_complexND (smooth_deriv_complexND hH)
  have he : (fun t : ℝ => (t:ℂ)^2*deriv (deriv H) t) =
      fun t : ℝ => (t:ℂ)*((t:ℂ)*deriv (deriv H) t) := by funext t; ring
  rw [he]
  cases j with
  | zero => simp
  | succ j =>
    rw [iteratedDeriv_coordinate_mulND ((complex_coordinate_contDiffND ∞).mul h₂) j]
    rw [iteratedDeriv_coordinate_derivND (smooth_deriv_complexND hH),← iteratedDeriv_succ']
    push_cast
    ring

lemma iteratedDeriv_eq_of_eqOn_positiveND {H G : ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (h : EqOn H G (Ioi 0)) (j : ℕ) : iteratedDeriv j H 0 = iteratedDeriv j G 0 := by
  have he := (h.iteratedDeriv_of_isOpen isOpen_Ioi j).closure
    (hH.continuous_iteratedDeriv j (nat_cast_le_inftyND _)) (hG.continuous_iteratedDeriv j (nat_cast_le_inftyND _))
  apply he
  simp

lemma helmholtz_profile_jetsND {H G : ℝ → ℂ} (hH : ContDiff ℝ ∞ H)
    (hG : ContDiff ℝ ∞ G) (α : ℂ)
    (h : ∀ t : ℝ, 0 < t → G t = α*(α-1)*H t + 2*Complex.I*deriv H t -
      2*(t:ℂ)*deriv H t - (t:ℂ)^2*deriv (deriv H) t) (j : ℕ) :
    2*Complex.I*iteratedDeriv (j+1) H 0 = iteratedDeriv j G 0 +
      ((j:ℂ)*(j+1)-α*(α-1))*iteratedDeriv j H 0 := by
  have hH₁ := smooth_deriv_complexND hH
  have hH₂ := smooth_deriv_complexND hH₁
  have hR : ContDiff ℝ ∞ (fun t : ℝ => α*(α-1)*H t + 2*Complex.I*deriv H t -
      2*(t:ℂ)*deriv H t - (t:ℂ)^2*deriv (deriv H) t) := by fun_prop
  have he := iteratedDeriv_eq_of_eqOn_positiveND hG hR (fun t ht => h t ht) j
  have hl₀ : ContDiffAt ℝ (j:WithTop ℕ∞) (fun t : ℝ => α*(α-1)*H t) 0 :=
    (contDiff_const.mul hH).contDiffAt.of_le (nat_cast_le_inftyND _)
  have hl₁ : ContDiffAt ℝ (j:WithTop ℕ∞) (fun t : ℝ => 2*Complex.I*deriv H t) 0 :=
    (contDiff_const.mul hH₁).contDiffAt.of_le (nat_cast_le_inftyND _)
  have hl₂ : ContDiffAt ℝ (j:WithTop ℕ∞) (fun t : ℝ => 2*(t:ℂ)*deriv H t) 0 :=
    ((by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => 2*(t:ℂ))).mul hH₁).contDiffAt.of_le (nat_cast_le_inftyND _)
  have hl₃ : ContDiffAt ℝ (j:WithTop ℕ∞) (fun t : ℝ => (t:ℂ)^2*deriv (deriv H) t) 0 :=
    ((by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)^2)).mul hH₂).contDiffAt.of_le (nat_cast_le_inftyND _)
  rw [iteratedDeriv_fun_sub ((hl₀.add hl₁).sub hl₂) hl₃,
    iteratedDeriv_fun_sub (hl₀.add hl₁) hl₂,iteratedDeriv_fun_add hl₀ hl₁] at he
  have hm : (fun t : ℝ => 2*(t:ℂ)*deriv H t) = fun t : ℝ => 2*((t:ℂ)*deriv H t) := by
    funext t; ring
  rw [hm,iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field,iteratedDeriv_coordinate_derivND hH,
    iteratedDeriv_coordinate_sq_derivND hH,← iteratedDeriv_succ'] at he
  linear_combination -he

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
