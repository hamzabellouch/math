import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePoleCoefficient

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

lemma radial_cutoff_mem_of_ne_zero {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) {u : ℝ} (hu : u∉Icc (1/4:ℝ) 4) : Ψ u=0 := by
  by_contra hz
  exact hu (Ioo_subset_Icc_self (hs u hz))

lemma radial_cutoff_integrable {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (1/4:ℝ) 4)) :
    Integrable (fun u : ℝ => (Ψ u:ℂ)*f u) := by
  have hc : ContinuousOn (fun u : ℝ => (Ψ u:ℂ)*f u) (Icc (1/4:ℝ) 4) :=
    (Complex.continuous_ofReal.comp hΨ).continuousOn.mul hf
  exact hc.integrableOn_Icc.integrable_of_forall_notMem_eq_zero (fun u hu => by
    simp [radial_cutoff_mem_of_ne_zero hs hu])

lemma radial_cutoff_integral_bound {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) {f : ℝ → ℂ} {P E : ℝ}
    (hP : 0≤P) (hΨ : ∀ u, |Ψ u|≤P)
    (hf : ∀ u∈Icc (1/4:ℝ) 4, ‖f u‖≤E) :
    ‖∫ u : ℝ, (Ψ u:ℂ)*f u‖ ≤ (15/4:ℝ)*P*E := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1/4:ℝ) 4)
    (fun u hu => by simp [radial_cutoff_mem_of_ne_zero hs hu])]
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (1/4:ℝ) 4))
    (C := P*E) (f := fun u : ℝ => (Ψ u:ℂ)*f u) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (hΨ u) (hf u hu) (norm_nonneg _) hP)
  have hm : (volume.restrict (Icc (1/4:ℝ) 4)).real univ = (15/4:ℝ) := by
    simp [Measure.real, Real.volume_Icc]
    norm_num
  rw [hm] at hh
  nlinarith

lemma norm_pair_remainderND (f g p q : ℂ) {B E F : ℝ}
    (hB : 0≤B) (hE : 0≤E)
    (hf : ‖f‖≤B) (hg : ‖g‖≤B) (he : ‖f-p‖≤E) (he' : ‖g-q‖≤F) :
    ‖f*conj g-p*conj q‖≤E*B+(B+E)*F := by
  have hp : ‖p‖≤B+E := by
    calc
      ‖p‖ = ‖f-(f-p)‖ := by congr 1; ring
      _ ≤ ‖f‖+‖f-p‖ := norm_sub_le _ _
      _ ≤ B+E := add_le_add hf he
  have hid : f*conj g-p*conj q = (f-p)*conj g+p*conj (g-q) := by
    rw [map_sub]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_conj]
  exact add_le_add (mul_le_mul he hg (norm_nonneg _) hE)
    (mul_le_mul hp he' (norm_nonneg _) (add_nonneg hB hE))

lemma sphereAxisIntegralND_norm_bound {n : ℕ} (Λ : ℝ) (e : SphereAmbientND n)
    {b : SphereAmbientND n → ℂ} {C : ℝ} (hb : ∀ w, ‖w‖=1 → ‖b w‖≤C) :
    ‖sphereAxisIntegralND Λ e b‖≤C*(canonicalSphereMeasureND (SphereAmbientND n)).real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
  change ‖spherePlaneWaveND Λ e w*b w‖≤C
  simpa only [norm_mul,spherePlaneWaveND_norm,one_mul] using hb w hw

lemma sphereAxisIntegralND_continuous {n : ℕ} {b : SphereAmbientND n → ℂ}
    (hb : Continuous b) (e : SphereAmbientND n) (Λ : ℝ) :
    Continuous (fun u : ℝ => sphereAxisIntegralND (Λ*u) e b) := by
  have hc : Continuous (fun s => sphereAxisIntegralND s e b) :=
    continuous_iff_continuousAt.mpr (fun s => (sphereAxisIntegralND_hasDerivAt hb s e).continuousAt)
  exact hc.comp (continuous_const.mul continuous_id)

lemma radialPoleSumND_continuousOn (n J : ℕ) (Λ : ℝ) (c : PoleIndexND J → ℂ) :
    ContinuousOn (radialPoleSumND n J Λ c) (Icc (1/4:ℝ) 4) := by
  unfold radialPoleSumND
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.mul
  · exact (show Continuous (fun u : ℝ => Complex.exp (Complex.I*((poleSignND i.1*Λ):ℂ)*(u:ℂ))*c i) by fun_prop).continuousOn
  · exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1))))

theorem sphere_radial_remainderND {n : ℕ} (C : ℝ) (hC : 0≤C) (J : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ (b : SphereAmbientND n → ℂ) (e : SphereAmbientND n) (A Λ : ℝ),
      ContDiff ℝ ∞ b → ‖e‖=1 → 1≤A → 0<Λ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      ∀ u∈Icc (1/4:ℝ) 4,
        ‖sphereAxisIntegralND (Λ*u) e b-
          radialPoleSumND n J Λ (spherePoleCoefficientND J Λ b e) u‖≤
            D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) := by
  obtain ⟨D,hD,hDb⟩ := sphere_global_rotatedND (n := n) C hC J
  refine ⟨D*(1/4:ℝ)^(-(n:ℝ)/2-(J+1:ℕ)), by positivity, ?_⟩
  intro b e A Λ hb he hA hΛ hd u hu
  have hup : 0<u := lt_of_lt_of_le (by norm_num) hu.1
  rw [radialPoleSumND_coefficients J Λ u hΛ hup]
  have hh := hDb b A (Λ*u) e hb hA (mul_pos hΛ hup) he hd
  rw [← neg_div] at hh
  apply hh.trans
  rw [Real.mul_rpow hΛ.le hup.le]
  have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1/4) hu.1
    (show -(n:ℝ)/2-(J+1:ℕ)≤0 by
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      have hJ : (0:ℝ)≤(J+1:ℕ) := Nat.cast_nonneg _
      linarith)
  calc
    _ ≤ D*(Λ^(-(n:ℝ)/2-(J+1:ℕ))*(1/4:ℝ)^(-(n:ℝ)/2-(J+1:ℕ)))*A^(2*(J+1)+n+3) := by
      gcongr
    _ = _ := by ring

lemma radial_pair_comparisonND {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) {f g p q : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (1/4:ℝ) 4)) (hg : ContinuousOn g (Icc (1/4:ℝ) 4))
    (hp : ContinuousOn p (Icc (1/4:ℝ) 4)) (hq : ContinuousOn q (Icc (1/4:ℝ) 4))
    {P B E F : ℝ} (hP : 0≤P) (hB : 0≤B) (hE : 0≤E)
    (hcut : ∀ u, |Ψ u|≤P)
    (hfb : ∀ u∈Icc (1/4:ℝ) 4, ‖f u‖≤B)
    (hgb : ∀ u∈Icc (1/4:ℝ) 4, ‖g u‖≤B)
    (he : ∀ u∈Icc (1/4:ℝ) 4, ‖f u-p u‖≤E)
    (he' : ∀ u∈Icc (1/4:ℝ) 4, ‖g u-q u‖≤F) :
    ‖∫ u : ℝ, (Ψ u:ℂ)*f u*conj (g u)‖ ≤
      ‖∫ u : ℝ, (Ψ u:ℂ)*p u*conj (q u)‖ + (15/4:ℝ)*P*(E*B+(B+E)*F) := by
  have hg' : ContinuousOn (fun u => conj (g u)) (Icc (1/4:ℝ) 4) :=
    Complex.conjCLE.continuous.comp_continuousOn hg
  have hq' : ContinuousOn (fun u => conj (q u)) (Icc (1/4:ℝ) 4) :=
    Complex.conjCLE.continuous.comp_continuousOn hq
  have hi := radial_cutoff_integrable hΨ hs (hf.mul hg')
  have hj := radial_cutoff_integrable hΨ hs (hp.mul hq')
  simp only [Pi.mul_apply] at hi hj
  have herr := radial_cutoff_integral_bound hs hP hcut (fun u hu => norm_pair_remainderND (f u) (g u) (p u) (q u) hB hE
      (hfb u hu) (hgb u hu) (he u hu) (he' u hu))
  simp_rw [mul_sub] at herr
  rw [integral_sub hi hj] at herr
  simp_rw [← mul_assoc] at herr
  have htri := norm_add_le (∫ u : ℝ, (Ψ u:ℂ)*p u*conj (q u))
    ((∫ u : ℝ, (Ψ u:ℂ)*f u*conj (g u))-(∫ u : ℝ, (Ψ u:ℂ)*p u*conj (q u)))
  rw [← add_sub_assoc,add_sub_cancel_left] at htri
  exact htri.trans (add_le_add le_rfl herr)

theorem sphere_pair_far_kernelND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C) (J : ℕ) :
    ∃ H D P B : ℝ, 0≤H ∧ 0≤D ∧ 0≤P ∧ 0≤B ∧
      ∀ (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c → ‖e‖=1 → ‖z‖=1 →
      1≤A → 0<Λ → 0<Μ → A^2≤Λ → A^2≤Μ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤
        H*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))/(1+|Λ-Μ|)^2 +
        P*((D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*B +
          (B+D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*
            (D*Μ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))) := by
  obtain ⟨H,hH,hkernel⟩ := pole_pair_kernelND hΨ hs n J
  obtain ⟨D,hD,hrem⟩ := sphere_radial_remainderND (n := n) C hC J
  obtain ⟨K,hK,hcoeff⟩ := spherePoleCoefficientND_bound (n := n) J C hC
  obtain ⟨P,hP,hPb⟩ := radialStationaryProfile_derivatives hΨ hs 0 0
  have hcut : ∀ u, |Ψ u|≤P := by
    simpa only [iteratedDeriv_zero,radialStationaryProfile,Real.rpow_zero,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using hPb 0 le_rfl
  let B := C*(canonicalSphereMeasureND (SphereAmbientND n)).real univ
  have hB : 0≤B := mul_nonneg hC ENNReal.toReal_nonneg
  refine ⟨H*K*K,D,(15/4:ℝ)*P,B,by positivity,hD,by positivity,hB,?_⟩
  intro b c e z A Λ Μ hb hc he hz hA hΛ hΜ hscaleΛ hscaleΜ hbd hcd
  have hb0 : ∀ w, ‖w‖=1 → ‖b w‖≤C := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hbd 0 (by omega) w hw
  have hc0 : ∀ w, ‖w‖=1 → ‖c w‖≤C := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hcd 0 (by omega) w hw
  have hcomp := radial_pair_comparisonND hΨ.continuous hs
    (sphereAxisIntegralND_continuous hb.continuous e Λ).continuousOn
    (sphereAxisIntegralND_continuous hc.continuous z Μ).continuousOn
    (radialPoleSumND_continuousOn n J Λ (spherePoleCoefficientND J Λ b e))
    (radialPoleSumND_continuousOn n J Μ (spherePoleCoefficientND J Μ c z))
    hP hB (show 0≤D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) by positivity)
    hcut
    (fun u _ => sphereAxisIntegralND_norm_bound (Λ*u) e hb0)
    (fun u _ => sphereAxisIntegralND_norm_bound (Μ*u) z hc0)
    (hrem b e A Λ hb he hA hΛ hbd) (hrem c z A Μ hc hz hA hΜ hcd)
  apply hcomp.trans
  apply add_le_add _ le_rfl
  exact hkernel Λ Μ K K _ _ hΛ hΜ hK hK
    (hcoeff b e A Λ hb he hA hΛ hscaleΛ (fun j hj w hw => hbd j (by omega) w hw))
    (hcoeff c z A Μ hc hz hA hΜ hscaleΜ (fun j hj w hw => hcd j (by omega) w hw))

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
open scoped ContDiff ComplexConjugate RealInnerProductSpace
variable {n : ℕ}

lemma radial_sphere_fubiniND {f : ℝ → ℂ} (hf : Continuous f) (hfi : Integrable f)
    {b : SphereAmbientND n → ℂ} (hb : Continuous b) {B : ℝ}
    (hbound : ∀ w, ‖w‖=1 → ‖b w‖≤B) (α Μ : ℝ) (z : SphereAmbientND n) :
    (∫ u : ℝ, Complex.exp (Complex.I*(α:ℂ)*(u:ℂ))*f u*sphereAxisIntegralND (Μ*u) z b) =
      ∫ w, radialPhaseIntegral f (α+Μ*inner ℝ w z)*b w
        ∂canonicalSphereMeasureND (SphereAmbientND n) := by
  let F (u : ℝ) (w : SphereAmbientND n) :=
    Complex.exp (Complex.I*(α:ℂ)*(u:ℂ))*f u*(spherePlaneWaveND (Μ*u) z w*b w)
  have hFc : Continuous (Function.uncurry F) := by
    unfold F spherePlaneWaveND Function.uncurry
    fun_prop
  have hmajor := (hfi.norm.comp_fst (canonicalSphereMeasureND (SphereAmbientND n))).mul_const B
  have hFi : Integrable (Function.uncurry F)
      (volume.prod (canonicalSphereMeasureND (SphereAmbientND n))) := by
    apply hmajor.mono' hFc.aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volume)
      (ν := canonicalSphereMeasureND (SphereAmbientND n))).tendsto_ae.eventually
      canonicalSphereMeasureND_ae_norm] with p hp
    simp only [F,Function.uncurry,norm_mul,spherePlaneWaveND_norm,one_mul]
    have hex : ‖Complex.exp (Complex.I*(α:ℂ)*(p.1:ℂ))‖=1 := by
      simp [Complex.norm_exp,Complex.mul_re]
    rw [hex,one_mul]
    exact mul_le_mul_of_nonneg_left (hbound p.2 hp) (norm_nonneg _)
  calc
    _ = ∫ u : ℝ, ∫ w, F u w ∂canonicalSphereMeasureND (SphereAmbientND n) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul]
      rfl
    _ = ∫ w, ∫ u : ℝ, F u w ∂volume ∂canonicalSphereMeasureND (SphereAmbientND n) :=
      integral_integral_swap hFi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold radialPhaseIntegral
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with u
      unfold F spherePlaneWaveND
      have he : Complex.I*(((α+Μ*inner ℝ w z):ℝ):ℂ)*(u:ℂ) =
          Complex.I*(α:ℂ)*(u:ℂ)+Complex.I*(((Μ*u):ℝ):ℂ)*((inner ℝ w z):ℂ) := by
        push_cast
        ring
      rw [he,Complex.exp_add]
      ring

theorem noncomparable_radial_sphereND {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ Icc (1/4:ℝ) 4)
    {b : SphereAmbientND n → ℂ} (hb : Continuous b)
    {B C Λ Μ s : ℝ} (hC : 0≤C) (hΛ : 0<Λ) (hΜ : 0≤Μ)
    (hsep : 2*Μ≤Λ) (hs : s=1 ∨ s=-1) (z : SphereAmbientND n) (hz : ‖z‖=1)
    (hbound : ∀ w, ‖w‖=1 → ‖b w‖≤B) (k : ℕ)
    (hd : ∀ u, ‖iteratedDeriv k f u‖≤C) :
    ‖∫ u : ℝ, Complex.exp (Complex.I*(((s*Λ):ℝ):ℂ)*(u:ℂ))*f u*sphereAxisIntegralND (Μ*u) z b‖≤
      ((15/4:ℝ)*C/(Λ/2)^k)*B*(canonicalSphereMeasureND (SphereAmbientND n)).real univ := by
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hsupp)
  rw [radial_sphere_fubiniND hf.continuous hfi hb hbound]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
  have hin : |inner ℝ w z|≤1 := by simpa [Real.norm_eq_abs,hw,hz] using norm_inner_le_norm (𝕜 := ℝ) w z
  have ht : |Μ*inner ℝ w z|≤Μ := by
    rw [abs_mul,abs_of_nonneg hΜ]
    nlinarith
  have hfreq := noncomparable_radial_frequency hsep ht hs
  have hnz : s*Λ+Μ*inner ℝ w z≠0 := by
    intro hzero
    rw [hzero,abs_zero] at hfreq
    linarith
  have hbnd := radialPhaseIntegral_nonzero hf hsupp (by norm_num) hnz k hd
  have hp : (Λ/2)^k≤|s*Λ+Μ*inner ℝ w z|^k := pow_le_pow_left₀ (by positivity) hfreq k
  have hden : 0<(Λ/2)^k := pow_pos (by positivity) k
  have hh : ‖radialPhaseIntegral f (s*Λ+Μ*inner ℝ w z)‖≤(15/4:ℝ)*C/(Λ/2)^k := by
    apply hbnd.trans
    have he : C*((4:ℝ)-1/4)=(15/4:ℝ)*C := by ring
    rw [he]
    exact div_le_div_of_nonneg_left (by positivity) hden hp
  rw [norm_mul]
  exact mul_le_mul hh (hbound w hw) (norm_nonneg _) (by positivity)

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
