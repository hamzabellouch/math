import OAI.Analysis.HenonEmden.Harmonic

namespace OAI

universe uE uE2 uE3 uE4

section NewtonPotential

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

noncomputable def rawPotential (g : E → ℝ) (x : E) : ℝ :=
  ∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y

omit [Nontrivial E] in
lemma measurable_kernel_source {g : E → ℝ} (hg : Measurable g) :
    Measurable (fun z : E × E => ‖z.1-z.2‖^(2-(Module.finrank ℝ E:ℝ))*g z.2) :=
  ((measurable_fst.sub measurable_snd).norm.pow_const _).mul (hg.comp measurable_snd)

omit [Nontrivial E] in
lemma measurable_rawPotential {g : E → ℝ} (hg : Measurable g) : Measurable (rawPotential g) :=
  (measurable_kernel_source hg).stronglyMeasurable.integral_prod_right'.measurable

omit [Nontrivial E] in
lemma rawPotential_nonneg {g : E → ℝ} (hg : ∀ x, 0 ≤ g x) (x : E) : 0 ≤ rawPotential g x :=
  integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hg y)

omit [Nontrivial E] in
lemma locallyIntegrable_rawPotential {g U : E → ℝ} (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hU : LocallyIntegrable U) (hbound : ∀ x, rawPotential g x ≤ U x) :
    LocallyIntegrable (rawPotential g) := by
  apply hU.mono (measurable_rawPotential hg).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (rawPotential_nonneg hgp x)]
  exact (hbound x).trans (le_abs_self _)

lemma integral_kernel_laplacian_translate (hn : 3 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (y : E) :
    (∫ x : E, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ y := by
  have hh := integral_kernel_laplacian hn (hφ.comp (contDiff_const.sub contDiff_id))
    (hφc.comp_homeomorph (Homeomorph.subLeft y))
  simp only [Function.comp_def,id_eq,sub_zero] at hh
  simp_rw [laplacian_reflect hφ] at hh
  have he := integral_sub_left_eq_self (μ := volume)
    (fun x : E => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) y
  simp only [sub_sub_cancel_left,norm_neg] at he
  exact he ▸ hh

lemma rawPotential_weak_equation (hn : 3 ≤ Module.finrank ℝ E) {g : E → ℝ}
    (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hP : LocallyIntegrable (rawPotential g)) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, rawPotential g x*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*(∫ x, g x*φ x) := by
  let F (z : E × E) := ‖z.1-z.2‖^(2-(Module.finrank ℝ E:ℝ))*g z.2*Laplacian.laplacian φ z.1
  have hFm : Measurable F := (measurable_kernel_source hg).mul ((continuous_laplacian hφ).measurable.comp measurable_fst)
  have hi : Integrable F (volume.prod volume) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun x => (hki x).mul_const (Laplacian.laplacian φ x),?_⟩
    have hpint := hP.integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ).norm
      (compactSupport_laplacian hφc).norm
    convert hpint using 1
    ext x
    simp only [F,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (x- _)) _),abs_of_nonneg (hgp _)]
    rw [integral_mul_const]
    rfl
  calc
    _ = ∫ x, ∫ y, F (x,y) := by simp only [F,integral_mul_const,rawPotential]
    _ = ∫ y, ∫ x, F (x,y) := integral_integral_swap hi
    _ = ∫ y, g y*(-((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hf : (fun x => F (x,y)) = fun x => g y*(‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) := by ext x; dsimp [F]; ring
      rw [hf,integral_const_mul,integral_kernel_laplacian_translate hn hφ hφc]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma convolve_assoc {f g k : E → ℝ} (hf : LocallyIntegrable f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    convolve (convolve f g) k = convolve f (convolve g k) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  ext x
  apply convolution_assoc L L L L (fun a b c => mul_assoc a b c)
    hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hgc.convolutionExists_right L hf hg)
  · exact Eventually.of_forall (hkc.norm.convolutionExists_right L hg.norm.locallyIntegrable hk.norm)
  · exact (hgc.norm.convolution L hkc.norm).convolutionExists_right L (fun x => (hf x).norm)
      (hkc.norm.continuous_convolution_right L hg.norm.locallyIntegrable hk.norm) x

lemma convolve_const (c : ℝ) (g : E → ℝ) (x : E) :
    convolve (fun _ => c) g x = c*(∫ y, g y) := by
  rw [convolve_def,integral_const_mul,integral_sub_left_eq_self]

lemma convolve_const_right (f : E → ℝ) (c : ℝ) (x : E) :
    convolve f (fun _ => c) x = (∫ y, f y)*c := by
  rw [convolve_def,integral_mul_const]
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma harmonic_distribution_nonneg_constant (hn : 2 ≤ Module.finrank ℝ E) {h : E → ℝ}
    (hi : LocallyIntegrable h) (hp : ∀ x, 0 ≤ h x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, h y*Laplacian.laplacian φ y) = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, h x = c := by
  let ξ (j : ℕ) := (standardBump (E := E) j).normed volume
  let c := convolve h (ξ 0) 0
  have hξ (j : ℕ) : ContDiff ℝ 2 (ξ j) := (standardBump j).contDiff_normed
  have hξc (j : ℕ) : HasCompactSupport (ξ j) := (standardBump j).hasCompactSupport_normed
  have hξp (j : ℕ) (y : E) : 0 ≤ ξ j y := (standardBump j).nonneg_normed y
  have hξint (j : ℕ) : (∫ y, ξ j y) = 1 := (standardBump j).integral_normed
  have hH (j : ℕ) : ContDiff ℝ 2 (convolve h (ξ j)) := contDiff_convolve hi (hξ j) (hξc j)
  have hHeq (j : ℕ) (x : E) : Laplacian.laplacian (convolve h (ξ j)) x = 0 := by
    have hh := convolve_weak_equation hi (hξ j) (hξc j) (g := fun _ => 0)
      (fun φ hφ hφc => by simpa using heq φ hφ hφc) x
    simpa [convolve_def] using hh
  have hHc (j : ℕ) : convolve h (ξ j) = fun _ => convolve h (ξ j) 0 := by
    ext x
    exact SphereCalculus.harmonic_nonnegative_constant hn (hH j) (hHeq j)
      (convolve_nonneg hp (hξp j)) x 0
  have hsame (j : ℕ) : convolve h (ξ j) 0 = c := by
    have hh : convolve (convolve h (ξ j)) (ξ 0) = convolve (convolve h (ξ 0)) (ξ j) := by
      rw [convolve_assoc hi (hξ j).continuous (hξc j) (hξ 0).continuous (hξc 0),
        convolve_assoc hi (hξ 0).continuous (hξc 0) (hξ j).continuous (hξc j),convolve_comm (ξ j) (ξ 0)]
    rw [hHc j,hHc 0] at hh
    have hv := congrFun hh (0:E)
    simpa only [convolve_const,hξint,mul_one] using hv
  have htest (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (x : E) :
      convolve h φ x = c*(∫ y, φ y) := by
    have hcφ : Continuous (convolve h φ) := (contDiff_convolve hi hφ hφc).continuous
    have ht := convolve_normed_tendsto standardBump_tendsto hcφ.aestronglyMeasurable (hcφ.continuousAt (x := x))
    have hx (j : ℕ) : convolve (convolve h φ) (ξ j) x = c*(∫ y, φ y) := by
      have hh : convolve (convolve h φ) (ξ j) = convolve (convolve h (ξ j)) φ := by
        rw [convolve_assoc hi hφ.continuous hφc (hξ j).continuous (hξc j),
          convolve_assoc hi (hξ j).continuous (hξc j) hφ.continuous hφc,convolve_comm φ (ξ j)]
      rw [hh,hHc j,hsame j,convolve_const]
    exact tendsto_nhds_unique ht (by simpa only [ξ,← funext hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c*(∫ y, φ y)) atTop (𝓝 (c*(∫ y, φ y)))))
  refine ⟨c,convolve_nonneg hp (hξp 0) 0,?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hi (continuous_const.locallyIntegrable)
  intro φ hφ hφc
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hh := htest (fun y => φ (-y)) (hφ2.comp contDiff_neg) (hφc.comp_homeomorph (Homeomorph.neg E)) (0:E)
  simp only [convolve_def,zero_sub,neg_neg,integral_neg_eq_self] at hh
  simpa only [smul_eq_mul,integral_mul_const,mul_comm] using hh
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma potential_constant (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : Measurable g) (hgp : ∀ x, 0 ≤ g x)
    (hki : ∀ x, Integrable (fun y => ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y))
    (hlower : ∀ x, rawPotential g x ≤ ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x, ((Module.finrank ℝ E:ℝ)-2)*
      ((volume : Measure E).toSphere univ).toReal*u x = rawPotential g x+c := by
  let D := ((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal
  have hP : LocallyIntegrable (rawPotential g) :=
    locallyIntegrable_rawPotential hg hgp (hu.const_mul D).locallyIntegrable hlower
  let h (x : E) := D*u x-rawPotential g x
  have hh : LocallyIntegrable h := (hu.const_mul D).locallyIntegrable.sub hP
  have hharm (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      (∫ x, h x*Laplacian.laplacian φ x) = 0 := by
    have h1 := (hu.locallyIntegrable (μ := volume)).integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ)
      (compactSupport_laplacian hφc)
    have h2 := hP.integrable_smul_right_of_hasCompactSupport (continuous_laplacian hφ)
      (compactSupport_laplacian hφc)
    simp only [smul_eq_mul] at h1 h2
    have hf : (fun x => h x*Laplacian.laplacian φ x) =
        fun x => D*(u x*Laplacian.laplacian φ x)-rawPotential g x*Laplacian.laplacian φ x := by ext x; dsimp [h]; ring
    rw [hf,integral_sub (h1.const_mul D) h2,integral_const_mul,heq φ hφ hφc,
      rawPotential_weak_equation hn hg hgp hki hP hφ hφc]
    dsimp [D]; ring
  obtain ⟨c,hc,hceq⟩ := harmonic_distribution_nonneg_constant (by omega) hh
    (fun x => sub_nonneg.mpr (hlower x)) hharm
  refine ⟨c,hc,?_⟩
  filter_upwards [hceq] with x hx
  change D*u x-rawPotential g x = c at hx
  change D*u x = rawPotential g x+c
  exact sub_eq_iff_eq_add'.mp hx
end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
