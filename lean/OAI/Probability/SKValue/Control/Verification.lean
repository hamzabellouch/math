import Mathlib
import OAI.Probability.SKValue.Equations.InitialMax
import OAI.Probability.SKValue.Equations.ValueStrip

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal
namespace SKValue

lemma value_bounded_drift_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z r G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L) (hr : |r|≤G)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hsmooth : ContDiff ℝ 3 (V t))
    (ha : |deriv (deriv (V t)) x|≤K)
    (hthird : ∀ y, |iteratedDeriv 3 (V t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |(1/2 : ℝ)*(deriv (V s) y)^2|≤K)
    (haLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|))
    (haint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ))
    (hPDE : ∀ y, V (t+δ) y-V t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) y+γ s*((1/2 : ℝ)*(deriv (V s) y)^2))) :
    let d := Real.sqrt δ*z+δ*r
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K ((1/2+G)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*r
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x) =
        (V (t+δ) (x+d)-V t (x+d))+
          δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq, hPDE]
    convert htm using 1
    · rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
        abs_neg]
    · simp only [add_sub_cancel_left]
  have hs : |(V t (x+d)-V t x+1)-1-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder (v := 1) (c := r)
    hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    hr (by norm_num) ha (by simpa only [mul_one] using hs)
    (by simpa only [mul_one] using ht)
  convert hh using 1 <;> dsimp only [cubicEnvelope, d]
  all_goals congr 1
  all_goals ring

lemma control_completion_square {γ α : ℝ → ℝ} {a b p : ℝ}
    (hab : a≤b) (hγ : ∀ s∈Icc a b, 0≤γ s)
    (hi : IntervalIntegrable γ volume a b)
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume a b)
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume a b) :
    p*(∫ s in a..b, γ s*α s)-(1/2 : ℝ)*(∫ s in a..b, γ s*(α s)^2) ≤
      ((1/2 : ℝ)*p^2)*(∫ s in a..b, γ s) := by
  have hpw : ∀ s∈Icc a b,
      p*(γ s*α s)-(1/2 : ℝ)*(γ s*(α s)^2) ≤ ((1/2 : ℝ)*p^2)*γ s := by
    intro s hs
    nlinarith [mul_nonneg (hγ s hs) (sq_nonneg (α s-p))]
  have hh := intervalIntegral.integral_mono_on hab
    ((hi₁.const_mul p).sub (hi₂.const_mul (1/2))) (hi.const_mul ((1/2 : ℝ)*p^2)) hpw
  simpa only [intervalIntegral.integral_sub (hi₁.const_mul p) (hi₂.const_mul (1/2)),
    intervalIntegral.integral_const_mul] using hh

lemma ValueStrip.control_one_step {T K L t δ x z : ℝ} {γ α : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    (ht : 0≤t) (hδ : 0<δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hα : ∀ s∈Icc t (t+δ), |α s|≤1)
    (hi : IntervalIntegrable γ volume t (t+δ))
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume t (t+δ))
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume t (t+δ)) :
    V (t+δ) (x+Real.sqrt δ*z+(∫ s in t..(t+δ), γ s*α s))-
      (1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-V t x-
      deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1) ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+
        2*δ*K*(γ (t+δ)-γ t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ.le).trans htδ
  have hT : 0≤T := ht.trans htT
  have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hTm : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG := h.gamma_nonneg T hTm
  have hγm := h.gamma_mono.mono hsub
  have hγn : ∀ s∈Icc t (t+δ), 0≤γ s := fun s hs ↦ h.gamma_nonneg s (hsub hs)
  have hγb : ∀ s∈Icc t (t+δ), γ s≤γ T :=
    fun s hs ↦ h.gamma_mono (hsub hs) hTm (hs.2.trans htδ)
  let D := ∫ s in t..(t+δ), γ s*α s
  let r := D/δ
  have hD : |D|≤δ*(γ T) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t+δ) (f := fun s ↦ γ s*α s) (C := γ T) (fun s hs ↦ by
        rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
        have hs' : s∈Icc t (t+δ) := ⟨hs.1.le,hs.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hγn s hs')]
        exact (mul_le_mul_of_nonneg_left (hα s hs') (hγn s hs')).trans
          (by simpa only [mul_one] using hγb s hs'))
    simpa only [Real.norm_eq_abs, show t+δ-t=δ by ring,
      abs_of_nonneg hδ.le, mul_comm (γ T) δ] using hh
  have hr : |r|≤γ T := by
    dsimp only [r]
    rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    simpa only [mul_comm] using hD
  have hdr : δ*r=D := by dsimp [r]; field_simp
  have hbint (y : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hpint (y : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hh := value_bounded_drift_one_step (V := V) (γ := γ) (x := x) (z := z)
    hδ.le hδ1 hG h.K_nonneg h.L_nonneg hr hγm (h.gamma_nonneg t htm)
    (h.gamma_mono htm hTm htT) (h.smooth t htm) (h.second_bound t htm x)
    (h.third_bound t htm) (fun s hs ↦ h.product_bound s (hsub hs))
    (fun s hs y ↦ h.second_lipschitz t htm s (hsub hs) x y)
    (fun s hs y ↦ h.product_lipschitz t htm s (hsub hs) x y)
    hbint hpint (fun y ↦ h.pde t htm (t+δ) hem y)
  dsimp only at hh
  rw [hdr, ←add_assoc] at hh
  have hcomp := control_completion_square (p := deriv (V t) x)
    (by linarith : t≤t+δ) hγn hi hi₁ hi₂
  have hγint : (∫ s in t..(t+δ), γ s)≤δ*γ (t+δ) := by
    have hc := intervalIntegral.integral_mono_on (by linarith : t≤t+δ) hi
      (intervalIntegrable_const (c := γ (t+δ)))
      (fun s hs ↦ h.gamma_mono (hsub hs) hem hs.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, show t+δ-t=δ by ring] using hc
  have hp0 : 0≤(1/2 : ℝ)*(deriv (V t) x)^2 := by positivity
  have hpK : (1/2 : ℝ)*(deriv (V t) x)^2≤K :=
    (le_abs_self _).trans (h.product_bound t htm x)
  have hgap : 0≤γ (t+δ)-γ t := sub_nonneg.mpr (h.gamma_mono htm hem (by linarith))
  have hdiff : (1/2 : ℝ)*(deriv (V t) x)^2*(∫ s in t..(t+δ), γ s)-
      δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) ≤ δ*K*(γ (t+δ)-γ t) := by
    calc
      _ ≤ (1/2 : ℝ)*(deriv (V t) x)^2*(δ*γ (t+δ))-
          δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) := by gcongr
      _ = δ*((1/2 : ℝ)*(deriv (V t) x)^2)*(γ (t+δ)-γ t) := by ring
      _ ≤ _ := by gcongr
  have hhu := (le_abs_self _).trans hh
  have hcomp' : deriv (V t) x*D-(1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-
      δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) ≤ δ*K*(γ (t+δ)-γ t) := by
    dsimp only [D]
    linarith
  have heq : δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2) =
      deriv (V t) x*D-δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) := by rw [mul_sub, mul_left_comm δ, hdr]
  rw [heq] at hhu
  dsimp only [D] at hhu hcomp'
  linarith

end SKValue

namespace SKValue

lemma ValueStrip.control_mesh_bound {T K L x : ℝ} {N : ℕ} {γ α W X : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {Z : Fin N → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (h : ValueStrip T γ V K L)
    (hα : ∀ s∈Icc (0 : ℝ) T, |α s|≤1)
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume 0 T)
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=x+W t+∫ s in (0 : ℝ)..t, γ s*α s)
    (hZ : ∀ i : Fin N, Real.sqrt (stepSize T N)*Z i=
      W (meshTime T N (i+1))-W (meshTime T N i)) :
    V T (X T)-V 0 (X 0)-(1/2 : ℝ)*(∫ s in (0 : ℝ)..T, γ s*(α s)^2)-
      (∑ i : Fin N, deriv (V (meshTime T N i)) (X (meshTime T N i))*
        (W (meshTime T N (i+1))-W (meshTime T N i)))-
      (1/2 : ℝ)*(∑ i : Fin N, deriv (deriv (V (meshTime T N i))) (X (meshTime T N i))*
        ((W (meshTime T N (i+1))-W (meshTime T N i))^2-stepSize T N)) ≤
    stepSize T N*Real.sqrt (stepSize T N)*
      (∑ i : Fin N, cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i))+
      2*stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0<δ := div_pos hT hNr
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ.le hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime,δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime,Nat.cast_zero,zero_mul]
  let C := fun t ↦ (1/2 : ℝ)*(∫ s in (0 : ℝ)..t, γ s*(α s)^2)
  let P := fun j ↦ V (meshTime T N j) (X (meshTime T N j))-C (meshTime T N j)
  let D := fun i : Fin N ↦ W (meshTime T N (i+1))-W (meshTime T N i)
  let R := fun i : Fin N ↦ P (i+1)-P i-
    deriv (V (meshTime T N i)) (X (meshTime T N i))*D i-
    (1/2 : ℝ)*deriv (deriv (V (meshTime T N i))) (X (meshTime T N i))*(D i^2-δ)
  have hiγ : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact h.gamma_mono
  have hlocal (i : Fin N) : R i≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      2*δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [←hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hh := h.control_one_step (x := X t) (z := Z i) ht.1 hδ hδ1 ht'.2
      (fun s hs ↦ hα s (hsub hs)) (intervalIntegrable_substrip hT.le hiγ ht ht')
      (intervalIntegrable_substrip hT.le hi₁ ht ht')
      (intervalIntegrable_substrip hT.le hi₂ ht ht')
    have hD : Real.sqrt δ*Z i=D i := hZ i
    have hXinc : X (t+δ)=X t+D i+(∫ s in t..(t+δ), γ s*α s) := by
      have hi0 := intervalIntegrable_substrip hT.le hi₁ ⟨le_rfl,hT.le⟩ ht
      have hinc := intervalIntegral.integral_add_adjacent_intervals hi0
        (intervalIntegrable_substrip hT.le hi₁ ht ht')
      rw [hX (t+δ) ht',hX t ht]
      dsimp only [D,t]
      rw [hsucc]
      linarith
    have hCinc : C (t+δ)-C t=(1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2) := by
      have hi0 := intervalIntegrable_substrip hT.le hi₂ ⟨le_rfl,hT.le⟩ ht
      have hinc := intervalIntegral.integral_add_adjacent_intervals hi0
        (intervalIntegrable_substrip hT.le hi₂ ht ht')
      dsimp only [C]
      linarith
    have hQ : D i^2=δ*(Z i)^2 := by rw [←hD,mul_pow,Real.sq_sqrt hδ.le]
    have hReq : R i=V (t+δ) (X t+Real.sqrt δ*Z i+
        (∫ s in t..(t+δ), γ s*α s))-
        (1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-V t (X t)-
        deriv (V t) (X t)*Real.sqrt δ*Z i-
        (1/2 : ℝ)*δ*deriv (deriv (V t)) (X t)*((Z i)^2-1) := by
      rw [hD,←hXinc]
      dsimp only [R,P]
      rw [hsucc]
      rw [show V (t+δ) (X (t+δ))-C (t+δ)-(V t (X t)-C t) =
        V (t+δ) (X (t+δ))-V t (X t)-(C (t+δ)-C t) by ring,hCinc,hQ,←hD]
      ring
    rw [hReq]
    simpa only [t,←hsucc] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hlocal i)
  dsimp only [R] at hsum
  rw [sum_local_residual] at hsum
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  rw [sum_steps_sub (fun j ↦ γ (meshTime T N j)),hlast,hzero] at hsum
  dsimp only [P,C,D] at hsum
  rw [hlast,hzero,intervalIntegral.integral_same,mul_zero,sub_zero] at hsum
  simp_rw [mul_assoc] at hsum
  rw [←Finset.mul_sum] at hsum
  dsimp only [δ] at hsum
  linarith

end SKValue

end

end OAI
