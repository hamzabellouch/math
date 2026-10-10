import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.StationaryScaleFactor2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereCutoffB

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Metric MeasureTheory
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}

theorem sphere_inverse_arbitrary_powerND (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n))
      (R A Λ : ℝ) (e : SphereAmbientND n),
      1 ≤ R → 1 ≤ A → R^κ ≤ Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) → ‖e‖=1 →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖Complex.exp (Complex.I*Λ)*b.1 e -
        ((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ e (sphereCutoffBAtND e b j))‖ ≤ D*R^(-T) := by
  obtain ⟨J,hJ⟩ := stationary_arbitrary_powerND κ T hκ (n+3)
  obtain ⟨D,hD,hDb⟩ := sphere_inverse_rotatedND (n := n) J C hC
  refine ⟨J,D,hD,?_⟩
  intro b R A Λ e hR hA hΛ hup hratio he hb
  have hΛp : 0 < Λ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) κ).trans_le hΛ
  rw [norm_sub_rev]
  apply (hDb b A Λ e hA hΛp he hb).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [Nat.add_assoc] using hJ R A Λ hR hA hΛp hup hratio) hD

theorem sphere_full_arbitrary_powerND (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SphereAmbientND n → ℂ)
      (R A Λ : ℝ) (e : SphereAmbientND n), ContDiff ℝ ∞ b →
      1 ≤ R → 1 ≤ A → R^κ ≤ Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) → ‖e‖=1 →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖ ≤ C*A^k) →
      ‖((Λ^((n:ℝ)/2):ℝ):ℂ)*sphereAxisIntegralND Λ e b -
        (Complex.exp (Complex.I*Λ) *
          ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ))*sphereLND n j b e +
        Complex.exp (-(Complex.I*Λ)) *
          ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ))*sphereLMinusND n j b (-e))‖
        ≤ D*R^(-T) := by
  obtain ⟨J,hJ⟩ := stationary_arbitrary_powerND κ T hκ (n+3)
  obtain ⟨D,hD,hDb⟩ := sphere_global_rotatedND (n := n) C hC J
  refine ⟨J,D,hD,?_⟩
  intro b R A Λ e hb hR hA hΛ hup hratio he hderiv
  have hΛp : 0 < Λ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) κ).trans_le hΛ
  let S : ℂ := Complex.exp (Complex.I*Λ) *
          ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ))*sphereLND n j b e +
        Complex.exp (-(Complex.I*Λ)) *
          ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ))*sphereLMinusND n j b (-e)
  have hc : ((Λ^((n:ℝ)/2):ℝ):ℂ) * ((Λ^(-(n:ℝ)/2):ℝ):ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.rpow_add hΛp,show (n:ℝ)/2+(-(n:ℝ)/2)=0 by ring,
      Real.rpow_zero,Complex.ofReal_one]
  have hf : ((Λ^((n:ℝ)/2):ℝ):ℂ)*sphereAxisIntegralND Λ e b - S =
      ((Λ^((n:ℝ)/2):ℝ):ℂ) *
        (sphereAxisIntegralND Λ e b - ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*S) := by
    rw [mul_sub,← mul_assoc,hc,one_mul]
  change ‖((Λ^((n:ℝ)/2):ℝ):ℂ)*sphereAxisIntegralND Λ e b-S‖ ≤ _
  rw [hf,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛp _)]
  have hs := hDb b A Λ e hb hA hΛp he hderiv
  have hscale : Λ^((n:ℝ)/2)*Λ^(-(n:ℝ)/2-(J+1:ℕ)) = Λ^(-((J+1:ℕ):ℝ)) := by
    rw [← Real.rpow_add hΛp]
    congr 1
    ring
  calc
    _ ≤ Λ^((n:ℝ)/2)*(D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)) :=
      by simpa only [neg_div,S] using
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hΛp.le ((n:ℝ)/2))
    _ = D*(Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3)) := by rw [← hscale]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa [Nat.add_assoc] using hJ R A Λ hR hA hΛp hup hratio) hD

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
open Set Metric MeasureTheory
open scoped ContDiff Topology
variable {n : ℕ}

lemma sphereLND_eventuallyEq (j : ℕ) {b c : SphereAmbientND n → ℂ}
    {w : SphereAmbientND n} (h : b =ᶠ[𝓝 w] c) : sphereLND n j b w = sphereLND n j c w := by
  simp only [sphereLND,(sphereJetPolynomialND_eventuallyEq j h).eq_of_nhds]

lemma sphereLND_zero (j : ℕ) : sphereLND n j (fun _ => 0) = fun _ => 0 := by
  simpa only [zero_mul] using sphereLND_const_mul (n := n) j (b := fun _ => 1) contDiff_const 0

lemma sphereLMinusND_zero_at {b : SphereAmbientND n → ℂ} {w : SphereAmbientND n}
    (h : b =ᶠ[𝓝 w] (fun _ => 0)) (j : ℕ) : sphereLMinusND n j b w = 0 := by
  have he : (fun x => star (b x)) =ᶠ[𝓝 w] (fun _ => 0) := by
    filter_upwards [h] with x hx
    simp only [hx,star_zero]
  rw [sphereLMinusND,sphereLND_eventuallyEq j he,sphereLND_zero,star_zero]

noncomputable def sphereFixedRemainderND (ψ : SphereAmbientND n → ℂ)
    (J : ℕ) (Λ : ℝ) (e : SphereAmbientND n) (b : SphereAmbientND n → ℂ) : ℂ :=
  sphereAxisIntegralND Λ e (fun w => ψ w*b w) -
    ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*
      ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ))*sphereLND n j b e

theorem sphere_fixed_directND (ψ : SphereAmbientND n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SphereAmbientND n → ℂ) (A Λ : ℝ)
      (e : SphereAmbientND n), ContDiff ℝ ∞ b → 1 ≤ A → 0 < Λ → ‖e‖=1 →
      ψ =ᶠ[𝓝 e] (fun _ => 1) → ψ =ᶠ[𝓝 (-e)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖ ≤ C*A^k) →
      ‖sphereFixedRemainderND ψ J Λ e b‖ ≤
        D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) := by
  obtain ⟨C',hC',hprod⟩ := compact_multiplier_derivative_bound
    (isCompact_sphere (0:SphereAmbientND n) 1) hψ (2*(J+1)+n+3) C hC
  obtain ⟨D,hD,hDb⟩ := sphere_global_rotatedND (n := n) C' hC' J
  refine ⟨D,hD,?_⟩
  intro b A Λ e hb hA hΛ he hplus hminus hderiv
  have hp (j : ℕ) : sphereLND n j (fun w => ψ w*b w) e = sphereLND n j b e := by
    apply sphereLND_eventuallyEq
    filter_upwards [hplus] with w hw
    simp only [hw,one_mul]
  have hm (j : ℕ) : sphereLMinusND n j (fun w => ψ w*b w) (-e) = 0 := by
    apply sphereLMinusND_zero_at
    filter_upwards [hminus] with w hw
    simp only [hw,zero_mul]
  have hh := hDb (fun w => ψ w*b w) A Λ e (hψ.mul hb) hA hΛ he (by
    intro k hk w hw
    exact hprod b A hb hA (by simpa only [mem_sphere_zero_iff_norm] using hderiv)
      k hk w (by simpa only [mem_sphere_zero_iff_norm] using hw))
  simpa only [sphereFixedRemainderND,hp,hm,mul_zero,Finset.sum_const_zero,add_zero,
    mul_assoc,neg_div] using hh

lemma sphereFixedRemainderND_const_mul (ψ : SphereAmbientND n → ℂ) (J : ℕ) (Λ : ℝ)
    (e : SphereAmbientND n) {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) (c : ℂ) :
    sphereFixedRemainderND ψ J Λ e (fun w => c*b w) = c*sphereFixedRemainderND ψ J Λ e b := by
  simp only [sphereFixedRemainderND,mul_left_comm (ψ _) c,sphereAxisIntegralND_const_mul,
    sphereLND_const_mul _ hb,mul_left_comm _ c,← Finset.mul_sum]
  ring

theorem sphere_fixed_direct_shiftND (ψ : SphereAmbientND n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SphereAmbientND n → ℂ) (A Λ : ℝ) (s : ℕ)
      (e : SphereAmbientND n), ContDiff ℝ ∞ b → 1 ≤ A → 0 < Λ → ‖e‖=1 →
      ψ =ᶠ[𝓝 e] (fun _ => 1) → ψ =ᶠ[𝓝 (-e)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖ ≤ C*A^(k+s)) →
      ‖sphereFixedRemainderND ψ J Λ e b‖ ≤
        D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3+s) := by
  obtain ⟨D,hD,hDb⟩ := sphere_fixed_directND ψ hψ C hC J
  refine ⟨D,hD,?_⟩
  intro b A Λ s e hb hA hΛ he hplus hminus hderiv
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let c : ℂ := ((A^s:ℝ):ℂ)⁻¹
  have hcnorm : ‖c‖ = (A^s)⁻¹ := by simp [c,Complex.norm_real,abs_of_pos hAp]
  have hh := hDb (fun w => c*b w) A Λ e (contDiff_const.mul hb) hA hΛ he hplus hminus (by
    intro j hj w hw
    change ‖iteratedFDeriv ℝ j (fun w => c • b w) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hb.of_le
      (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt),norm_smul,hcnorm]
    calc
      _ ≤ (A^s)⁻¹*(C*A^(j+s)) := mul_le_mul_of_nonneg_left (hderiv j hj w hw) (by positivity)
      _ = C*A^j := by rw [pow_add]; field_simp)
  rw [sphereFixedRemainderND_const_mul ψ J Λ e hb,norm_mul,hcnorm] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg hAp.le s)
  have hcA : A^s ≠ 0 := ne_of_gt (pow_pos hAp s)
  have hleft : A^s*((A^s)⁻¹*‖sphereFixedRemainderND ψ J Λ e b‖) =
      ‖sphereFixedRemainderND ψ J Λ e b‖ := by rw [← mul_assoc,mul_inv_cancel₀ hcA,one_mul]
  have hright : A^s*(D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)) =
      D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3+s) := by rw [pow_add]; ring
  rwa [hleft,hright] at hmul

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
open Set Metric MeasureTheory
open scoped ContDiff Topology
variable {n : ℕ}

lemma sphere_inverse_series_atND (J : ℕ) (Λ : ℝ)
    (b : SmoothFunctionND (SphereAmbientND n)) (e : SphereAmbientND n) :
    (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
      ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) *
        sphereLND n h (sphereBND j b).1 e) = b.1 e := by
  refine Eq.trans ?_ (sphere_inverse_triangleND J ((Λ:ℂ)⁻¹) b e)
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
  rw [Finset.mul_sum,show J-j+1=J+1-j by omega]
  apply Finset.sum_congr rfl
  intro h _
  simp only [zpow_neg,zpow_natCast,inv_pow,pow_add]
  ring

lemma sphere_inverse_fixed_errorND (ψ : SphereAmbientND n → ℂ) (J : ℕ) {Λ : ℝ}
    (hΛ : 0 < Λ) (e : SphereAmbientND n) (b : SmoothFunctionND (SphereAmbientND n)) :
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
        (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
          sphereAxisIntegralND Λ e (fun w => ψ w*(sphereBND j b).1 w)) -
      Complex.exp (Complex.I*Λ)*b.1 e =
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
        sphereFixedRemainderND ψ (J-j) Λ e (sphereBND j b).1) := by
  have hs := sphere_inverse_series_atND J Λ b e
  have hs' :
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
        (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*
          ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ))*sphereLND n h (sphereBND j b).1 e)) =
      ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*b.1 e := by
    calc
      _ = (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) * sphereLND n h (sphereBND j b).1 e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs]
  simp only [sphereFixedRemainderND,mul_sub,Finset.sum_sub_distrib,mul_sub]
  rw [hs']
  have hc := sphere_half_cancelND hΛ n
  linear_combination congrArg (fun z : ℂ => z*Complex.exp (Complex.I*Λ)*b.1 e) hc

theorem sphere_inverse_fixed_remainderND (ψ : SphereAmbientND n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A Λ : ℝ)
      (e : SphereAmbientND n), 1 ≤ A → 0 < Λ → ‖e‖=1 →
      ψ =ᶠ[𝓝 e] (fun _ => 1) → ψ =ᶠ[𝓝 (-e)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ e (fun w => ψ w*(sphereBND j b).1 w)) -
        Complex.exp (Complex.I*Λ)*b.1 e‖ ≤
      D*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
  have hbound (j : ℕ) := sphereBND_bound (n := n) j (2*(J-j+1)+n+3) C hC
  choose B hB hBb using hbound
  have hstationary (j : ℕ) := sphere_fixed_direct_shiftND ψ hψ (B j) (hB j) (J-j)
  choose D hD hDb using hstationary
  refine ⟨∑ j ∈ Finset.range (J+1), D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro b A Λ e hA hΛ he hplus hminus hb
  rw [sphere_inverse_fixed_errorND ψ J hΛ e b,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  calc
    _ ≤ Λ^((n:ℝ)/2) * ∑ j ∈ Finset.range (J+1),
        ‖(Λ:ℂ)^(-(j:ℤ)) * sphereFixedRemainderND ψ (J-j) Λ e (sphereBND j b).1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hΛ.le _)
    _ = ∑ j ∈ Finset.range (J+1), Λ^((n:ℝ)/2) *
        (‖(Λ:ℂ)^(-(j:ℤ))‖ * ‖sphereFixedRemainderND ψ (J-j) Λ e (sphereBND j b).1‖) := by
      rw [Finset.mul_sum]
      simp only [norm_mul]
    _ ≤ ∑ j ∈ Finset.range (J+1), D j*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hexp : 2*(J-j+1)+n+3+2*j=2*(J+1)+n+3 := by omega
      have hh := hDb j (sphereBND j b).1 A Λ (2*j) e (sphereBND j b).2 hA hΛ he hplus hminus
        (hBb j b A hA (fun k hk w hw => hb k (by omega) w hw))
      have hm := mul_le_mul_of_nonneg_left hh
        (mul_nonneg (Real.rpow_nonneg hΛ.le ((n:ℝ)/2)) (norm_nonneg ((Λ:ℂ)^(-(j:ℤ)))))
      calc
        _ ≤ (Λ^((n:ℝ)/2)*‖(Λ:ℂ)^(-(j:ℤ))‖) *
            (D j*Λ^(-(n:ℝ)/2-((J-j+1:ℕ):ℝ))*A^(2*(J-j+1)+n+3+2*j)) := by
          simpa only [mul_assoc] using hm
        _ = D j*(Λ^((n:ℝ)/2)*‖(Λ:ℂ)^(-(j:ℤ))‖*Λ^(-(n:ℝ)/2-((J-j+1:ℕ):ℝ))) *
            A^(2*(J+1)+n+3) := by rw [hexp]; ring
        _ = _ := by rw [inverse_stationary_weightND n J j hj' hΛ]
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]

theorem sphere_inverse_fixed_arbitrary_powerND (ψ : SphereAmbientND n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n))
      (R A Λ : ℝ) (e : SphereAmbientND n),
      1 ≤ R → 1 ≤ A → R^κ ≤ Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) → ‖e‖=1 →
      ψ =ᶠ[𝓝 e] (fun _ => 1) → ψ =ᶠ[𝓝 (-e)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖Complex.exp (Complex.I*Λ)*b.1 e -
        ((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ e (fun w => ψ w*(sphereBND j b).1 w))‖ ≤ D*R^(-T) := by
  obtain ⟨J,hJ⟩ := stationary_arbitrary_powerND κ T hκ (n+3)
  obtain ⟨D,hD,hDb⟩ := sphere_inverse_fixed_remainderND ψ hψ J C hC
  refine ⟨J,D,hD,?_⟩
  intro b R A Λ e hR hA hΛ hup hratio he hplus hminus hb
  have hΛp : 0 < Λ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) κ).trans_le hΛ
  rw [norm_sub_rev]
  apply (hDb b A Λ e hA hΛp he hplus hminus hb).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [Nat.add_assoc] using hJ R A Λ hR hA hΛp hup hratio) hD

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
