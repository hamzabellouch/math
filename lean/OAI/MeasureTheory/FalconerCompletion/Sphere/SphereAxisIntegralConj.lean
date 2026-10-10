import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.RadialCutoffMemOfNeZero

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate RealInnerProductSpace
variable {n : ℕ}

lemma sphereAxisIntegralND_conj (Λ : ℝ) (z : SphereAmbientND n) (b : SphereAmbientND n → ℂ) :
    conj (sphereAxisIntegralND Λ z b) =
      sphereAxisIntegralND Λ (-z) (fun w => conj (b w)) := by
  unfold sphereAxisIntegralND
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [map_mul,← Complex.exp_conj,inner_neg_right,Complex.ofReal_neg,
    Complex.conj_I,Complex.conj_ofReal]
  congr 2
  ring

lemma radial_sphere_integrableND {f : ℝ → ℂ} (hf : Continuous f) (hfi : Integrable f)
    {b : SphereAmbientND n → ℂ} (hb : Continuous b) {B : ℝ}
    (hbound : ∀ w, ‖w‖=1 → ‖b w‖≤B) (α Μ : ℝ) (z : SphereAmbientND n) :
    Integrable (fun u : ℝ => Complex.exp (Complex.I*(α:ℂ)*(u:ℂ))*f u*
      conj (sphereAxisIntegralND (Μ*u) z b)) := by
  have hc : Continuous (fun u : ℝ => Complex.exp (Complex.I*(α:ℂ)*(u:ℂ))*f u*
      conj (sphereAxisIntegralND (Μ*u) z b)) := by
    apply Continuous.mul
    · fun_prop
    · exact Complex.conjCLE.continuous.comp (sphereAxisIntegralND_continuous hb z Μ)
  apply (hfi.norm.mul_const (B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with u
  have hex : ‖Complex.exp (Complex.I*(α:ℂ)*(u:ℂ))‖=1 := by
    simp [Complex.norm_exp,Complex.mul_re]
  simp only [norm_mul,Complex.norm_conj,hex,one_mul]
  exact mul_le_mul_of_nonneg_left (sphereAxisIntegralND_norm_bound (Μ*u) z hbound) (norm_nonneg _)

theorem noncomparable_conj_sphereND {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ Icc (1/4:ℝ) 4)
    {b : SphereAmbientND n → ℂ} (hb : Continuous b)
    {B C Λ Μ s : ℝ} (hC : 0≤C) (hΛ : 0<Λ) (hΜ : 0≤Μ)
    (hsep : 2*Μ≤Λ) (hs : s=1 ∨ s=-1) (z : SphereAmbientND n) (hz : ‖z‖=1)
    (hbound : ∀ w, ‖w‖=1 → ‖b w‖≤B) (k : ℕ)
    (hd : ∀ u, ‖iteratedDeriv k f u‖≤C) :
    ‖∫ u : ℝ, Complex.exp (Complex.I*(((s*Λ):ℝ):ℂ)*(u:ℂ))*f u*conj (sphereAxisIntegralND (Μ*u) z b)‖≤
      ((15/4:ℝ)*C/(Λ/2)^k)*B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ := by
  simp_rw [sphereAxisIntegralND_conj]
  exact noncomparable_radial_sphereND hf hsupp (Complex.conjCLE.continuous.comp hb)
    hC hΛ hΜ hsep hs (-z) (by simpa using hz)
    (fun w hw => by simpa only [Function.comp_def,Complex.conjCLE_apply,Complex.norm_conj] using hbound w hw) k hd

lemma pole_exact_sphere_integralND {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (J : ℕ) (Λ Μ : ℝ)
    (c : PoleIndexND J → ℂ) {b : SphereAmbientND n → ℂ} (hb : Continuous b)
    {B : ℝ} (hbound : ∀ w, ‖w‖=1 → ‖b w‖≤B) (z : SphereAmbientND n) :
    (∫ u : ℝ, (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (sphereAxisIntegralND (Μ*u) z b)) =
      ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*∑ i : PoleIndexND J, c i *
        ∫ u : ℝ, Complex.exp (Complex.I*(((poleSignND i.1*Λ):ℝ):ℂ)*(u:ℂ))*
          radialStationaryProfile Ψ (-(n:ℝ)/2-(i.2:ℕ)) u * conj (sphereAxisIntegralND (Μ*u) z b) := by
  have hi (i : PoleIndexND J) : Integrable (fun u : ℝ => c i *
      (Complex.exp (Complex.I*(((poleSignND i.1*Λ):ℝ):ℂ)*(u:ℂ))*
        radialStationaryProfile Ψ (-(n:ℝ)/2-(i.2:ℕ)) u * conj (sphereAxisIntegralND (Μ*u) z b))) := by
    have hf := radialStationaryProfile_contDiff hΨ hs (-(n:ℝ)/2-(i.2:ℕ))
    have hsp := radialStationaryProfile_tsupport hs (-(n:ℝ)/2-(i.2:ℕ))
    have hfi : Integrable (radialStationaryProfile Ψ (-(n:ℝ)/2-(i.2:ℕ))) :=
      hf.continuous.integrable_of_hasCompactSupport (isCompact_Icc.of_isClosed_subset
        (isClosed_tsupport _) hsp)
    exact (radial_sphere_integrableND hf.continuous hfi hb hbound (poleSignND i.1*Λ) Μ z).const_mul _
  have he (u : ℝ) : (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (sphereAxisIntegralND (Μ*u) z b) =
      ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*∑ i : PoleIndexND J, c i *
        (Complex.exp (Complex.I*(((poleSignND i.1*Λ):ℝ):ℂ)*(u:ℂ))*
          radialStationaryProfile Ψ (-(n:ℝ)/2-(i.2:ℕ)) u * conj (sphereAxisIntegralND (Μ*u) z b)) := by
    unfold radialPoleSumND radialStationaryProfile
    simp only [Finset.mul_sum,Finset.sum_mul,Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_const_mul]

theorem pole_noncomparable_kernelND {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (J k : ℕ) :
    ∃ H : ℝ, 0≤H ∧ ∀ (Λ Μ B D : ℝ) (c : PoleIndexND J → ℂ)
      (b : SphereAmbientND n → ℂ) (z : SphereAmbientND n),
      0<Λ → 0≤Μ → 2*Μ≤Λ → 0≤B → 0≤D → Continuous b → ‖z‖=1 →
      (∀ w, ‖w‖=1 → ‖b w‖≤B) → (∀ i, ‖c i‖≤D) →
      ‖∫ u : ℝ, (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (sphereAxisIntegralND (Μ*u) z b)‖≤
        H*Λ^(-(n:ℝ)/2)*D*B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ/(Λ/2)^k := by
  have hex (i : PoleIndexND J) := radialStationaryProfile_derivatives hΨ hs (-(n:ℝ)/2-(i.2:ℕ)) k
  choose C hC hCd using hex
  refine ⟨(15/4:ℝ)*∑ i, C i,mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hC i)),?_⟩
  intro Λ Μ B D c b z hΛ hΜ hsep hB hD hb hz hbb hcc
  rw [pole_exact_sphere_integralND hΨ hs J Λ Μ c hb hbb z,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  have hh (i : PoleIndexND J) : ‖c i *
      ∫ u : ℝ, Complex.exp (Complex.I*(((poleSignND i.1*Λ):ℝ):ℂ)*(u:ℂ))*
        radialStationaryProfile Ψ (-(n:ℝ)/2-(i.2:ℕ)) u * conj (sphereAxisIntegralND (Μ*u) z b)‖≤
      D*((15/4:ℝ)*C i/(Λ/2)^k*B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ) := by
    rw [norm_mul]
    exact mul_le_mul (hcc i) (noncomparable_conj_sphereND
      (radialStationaryProfile_contDiff hΨ hs _) (radialStationaryProfile_tsupport hs _)
      hb (hC i) hΛ hΜ hsep (poleSignND_cases i.1) z hz hbb k (hCd i k le_rfl))
      (norm_nonneg _) hD
  calc
    _ ≤ Λ^(-(n:ℝ)/2)*∑ i : PoleIndexND J,
        D*((15/4:ℝ)*C i/(Λ/2)^k*B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hh i))
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem sphere_noncomparable_kernelND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C) (J k : ℕ) :
    ∃ H E : ℝ, 0≤H ∧ 0≤E ∧
      ∀ (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → Continuous c → ‖e‖=1 → ‖z‖=1 →
      1≤A → 0<Λ → 0≤Μ → 2*Μ≤Λ → A^2≤Λ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ w, ‖w‖=1 → ‖c w‖≤C) →
      ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤
        H*Λ^(-(n:ℝ)/2)/(Λ/2)^k + E*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) := by
  obtain ⟨H,hH,hkernel⟩ := pole_noncomparable_kernelND (n := n) hΨ hs J k
  obtain ⟨D,hD,hrem⟩ := sphere_radial_remainderND (n := n) C hC J
  obtain ⟨K,hK,hcoeff⟩ := spherePoleCoefficientND_bound (n := n) J C hC
  obtain ⟨P,hP,hPb⟩ := radialStationaryProfile_derivatives hΨ hs 0 0
  have hcut : ∀ u, |Ψ u|≤P := by
    simpa only [iteratedDeriv_zero,radialStationaryProfile,Real.rpow_zero,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using hPb 0 le_rfl
  let S := (canonicalSphereMeasureND (SphereAmbientND n)).real univ
  let B := C*S
  have hB : 0≤B := mul_nonneg hC ENNReal.toReal_nonneg
  refine ⟨H*K*C*S,(15/4:ℝ)*P*D*B,by positivity,by positivity,?_⟩
  intro b c e z A Λ Μ hb hc he hz hA hΛ hΜ hsep hscale hbd hcd
  have hb0 : ∀ w, ‖w‖=1 → ‖b w‖≤C := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hbd 0 (by omega) w hw
  have hcomp := radial_pair_comparisonND hΨ.continuous hs
    (sphereAxisIntegralND_continuous hb.continuous e Λ).continuousOn
    (sphereAxisIntegralND_continuous hc z Μ).continuousOn
    (radialPoleSumND_continuousOn n J Λ (spherePoleCoefficientND J Λ b e))
    (sphereAxisIntegralND_continuous hc z Μ).continuousOn
    hP hB (show 0≤D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) by positivity)
    hcut
    (fun u _ => sphereAxisIntegralND_norm_bound (Λ*u) e hb0)
    (fun u _ => sphereAxisIntegralND_norm_bound (Μ*u) z hcd)
    (hrem b e A Λ hb he hA hΛ hbd)
    (show ∀ u∈Icc (1/4:ℝ) 4, ‖sphereAxisIntegralND (Μ*u) z c-sphereAxisIntegralND (Μ*u) z c‖≤(0:ℝ) by simp)
  simp only [mul_zero,add_zero] at hcomp
  apply hcomp.trans
  have hk := hkernel Λ Μ C K (spherePoleCoefficientND J Λ b e) c z
    hΛ hΜ hsep hC hK hc hz hcd
    (hcoeff b e A Λ hb he hA hΛ hscale (fun j hj w hw => hbd j (by omega) w hw))
  calc
    _ ≤ H*Λ^(-(n:ℝ)/2)*K*C*S/(Λ/2)^k +
        (15/4:ℝ)*P*(D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)*B) :=
      add_le_add hk le_rfl
    _ = _ := by ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
