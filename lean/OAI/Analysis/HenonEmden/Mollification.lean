import OAI.Analysis.HenonEmden.WeakOrigin

namespace OAI

universe uE uE2 uι uE3

section Mollification

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
noncomputable section


open scoped Convolution
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def convolve (f g : E → ℝ) : E → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ] g

lemma convolve_def (f g : E → ℝ) (x : E) : convolve f g x = ∫ y, f y*g (x-y) := rfl

lemma contDiff_convolve {f g : E → ℝ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) : ContDiff ℝ 2 (convolve f g) :=
  hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg

lemma dir_convolve {f g : E → ℝ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (e x : E) :
    dir (convolve f g) e x = convolve f (dir g e) x := by
  unfold dir convolve
  rw [(hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hgc.fderiv ℝ)
    (hg.continuous_fderiv one_ne_zero) x e

lemma laplacian_convolve {f g : E → ℝ} (hf : LocallyIntegrable f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (x : E) :
    Laplacian.laplacian (convolve f g) x = convolve f (Laplacian.laplacian g) x := by
  have hfg := contDiff_convolve hf hg hgc
  have hdir (e : E) : dir (convolve f g) e = convolve f (dir g e) := by
    ext y; exact dir_convolve hf (hg.of_le (by norm_num)) hgc e y
  have hgdir (e : E) : ContDiff ℝ 1 (dir g e) :=
    contDiffOn_univ.mp (contDiffOn_dir hg.contDiffOn isOpen_univ e)
  have hi (e : E) : Integrable (fun y => f y*dir (dir g e) e (x-y)) := by
    exact (compactSupport_dir (compactSupport_dir hgc e) e).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hf
      (contDiffOn_univ.mp (contDiffOn_dir (k := 0) (hgdir e).contDiffOn isOpen_univ e)).continuous x
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,convolve_def]
  have hleft (i : Fin (Module.finrank ℝ E)) :
      iteratedFDeriv ℝ 2 (convolve f g) x ![stdOrthonormalBasis ℝ E i,stdOrthonormalBasis ℝ E i] =
      ∫ y, f y*dir (dir g (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) (x-y) := by
    rw [← dir_dir hfg.contDiffOn isOpen_univ (mem_univ x),hdir,
      dir_convolve hf (hgdir _) (compactSupport_dir hgc _)]
    rfl
  simp_rw [hleft,← dir_dir hg.contDiffOn isOpen_univ (mem_univ _),Finset.mul_sum]
  exact (integral_finsetSum _ (fun i _ => hi (stdOrthonormalBasis ℝ E i))).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_translate (f : E → ℝ) (a x : E) :
    Laplacian.laplacian (fun y => f (a+y)) x = Laplacian.laplacian f (a+x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_reflect {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a x : E) :
    Laplacian.laplacian (fun y => f (a-y)) x = Laplacian.laplacian f (a-x) := by
  have hh : (fun y => f (a-y)) = (fun y => (fun z => f (a+z)) ((-1:ℝ) • y)) := by
    ext y; simp [sub_eq_add_neg]
  have hfa : ContDiff ℝ 2 (fun z => f (a+z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [hh,laplacian_dilation hfa,laplacian_translate]
  simp [sub_eq_add_neg]
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma convolve_nonneg {f g : E → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : E) :
    0 ≤ convolve f g x := integral_nonneg fun y => mul_nonneg (hf y) (hg (x-y))

lemma convolve_comm (f g : E → ℝ) : convolve f g = convolve g f := by
  have hL : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    exact ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => mul_comm y x
  have hh := convolution_flip (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (f := f) (g := g)
  rw [hL] at hh
  exact hh.symm

lemma convolve_weak_equation {u g ξ : E → ℝ} (hu : LocallyIntegrable u)
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) (x : E) :
    Laplacian.laplacian (convolve u ξ) x = -convolve g ξ x := by
  rw [laplacian_convolve hu hξ hξc,convolve_def,convolve_def]
  have ht : ContDiff ℝ 2 (fun y => ξ (x-y)) := hξ.comp (contDiff_const.sub contDiff_id)
  have hs : HasCompactSupport (fun y => ξ (x-y)) := hξc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := heq _ ht hs
  simp_rw [laplacian_reflect hξ] at hh
  exact hh

lemma convolve_normed_tendsto {ι : Type uι} {l : Filter ι} {ξ : ι → ContDiffBump (0 : E)}
    (hξ : Tendsto (fun i => (ξ i).rOut) l (𝓝 0)) {f : E → ℝ}
    (hf : AEStronglyMeasurable f) {x : E} (hfx : ContinuousAt f x) :
    Tendsto (fun i => convolve f ((ξ i).normed volume) x) l (𝓝 (f x)) := by
  have he (i : ι) : convolve f ((ξ i).normed volume) x =
      (((ξ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x := by
    rw [convolve_comm,convolve_def,convolution_def]
    rfl
  simp_rw [he]
  exact ContDiffBump.convolution_tendsto_right hξ (Eventually.of_forall fun _ => hf)
    (hfx.tendsto.comp tendsto_snd) tendsto_const_nhds
end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma smooth_newton_lower (hn : 3 ≤ Module.finrank ℝ E) {u w : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : Continuous w) (hp : ∀ x, 0 ≤ u x) (hwp : ∀ x, 0 ≤ w x)
    (hEq : ∀ x, -Laplacian.laplacian u x = w x) (x : E) :
    (∫⁻ y : E, ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*w y)) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*
        ((volume : Measure E).toSphere univ).toReal*u x) := by
  have hh := SphereCalculus.smooth_newton_lower_at_zero hn
    (hu.comp (contDiff_const.sub contDiff_id)) (hw.comp (continuous_const.sub continuous_id))
    (fun y => hp (x-y)) (fun y => hwp (x-y))
    (fun y => by change -Laplacian.laplacian (fun z => u (x-z)) y = w (x-y); rw [laplacian_reflect hu]; exact hEq (x-y))
  simp only [Function.comp_def,Pi.sub_apply,id_eq,sub_zero] at hh
  have he := lintegral_sub_left_eq_self (μ := volume)
    (fun y : E => ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*w y)) x
  simp only [sub_sub_cancel] at he
  exact he ▸ hh

noncomputable def standardBump (j : ℕ) : ContDiffBump (0:E) :=
  ⟨1/((j:ℝ)+1),2/((j:ℝ)+1),by positivity,by
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<j+1)).mpr
    norm_num⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
lemma standardBump_tendsto : Tendsto (fun j : ℕ => (standardBump (E := E) j).rOut) atTop (𝓝 0) := by
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [standardBump, ← mul_div_assoc,mul_one,mul_zero] using hh

lemma weak_newton_lower (hn : 3 ≤ Module.finrank ℝ E) {u g : E → ℝ}
    (hu : Continuous u) (hg : LocallyIntegrable g)
    (hgc : ContinuousOn g ({0}ᶜ : Set E)) (hp : ∀ x, 0 ≤ u x) (hgp : ∀ x, 0 ≤ g x)
    (heq : ∀ (φ : E → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, u y*Laplacian.laplacian φ y) = -(∫ y, g y*φ y)) (x : E) :
    (∫⁻ y : E, ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*
        ((volume : Measure E).toSphere univ).toReal*u x) := by
  let ξ (j : ℕ) := (standardBump (E := E) j).normed volume
  let U (j : ℕ) := convolve u (ξ j)
  let G (j : ℕ) := convolve g (ξ j)
  have hξ (j : ℕ) : ContDiff ℝ 2 (ξ j) := (standardBump j).contDiff_normed
  have hξc (j : ℕ) : HasCompactSupport (ξ j) := (standardBump j).hasCompactSupport_normed
  have hξp (j : ℕ) (y : E) : 0 ≤ ξ j y := (standardBump j).nonneg_normed y
  have hU (j : ℕ) : ContDiff ℝ 2 (U j) := contDiff_convolve hu.locallyIntegrable (hξ j) (hξc j)
  have hG (j : ℕ) : ContDiff ℝ 2 (G j) := contDiff_convolve hg (hξ j) (hξc j)
  have hUlim : Tendsto (fun j => U j x) atTop (𝓝 (u x)) :=
    convolve_normed_tendsto standardBump_tendsto hu.aestronglyMeasurable hu.continuousAt
  have hGlim : ∀ᵐ y : E, Tendsto (fun j => G j y) atTop (𝓝 (g y)) := by
    filter_upwards [ae_iff.mpr (show volume {y : E | ¬ y ≠ 0} = 0 by simp)] with y hy
    exact convolve_normed_tendsto standardBump_tendsto hg.aestronglyMeasurable
      (hgc.continuousAt (isOpen_compl_singleton.mem_nhds hy))
  let F (j : ℕ) (y : E) := ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*G j y)
  have hFm (j : ℕ) : Measurable (F j) := by
    dsimp [F]
    exact (((continuous_const.sub continuous_id).norm.measurable.pow_const _).mul
      (hG j).continuous.measurable).ennreal_ofReal
  have hFint (j : ℕ) : (∫⁻ y, F j y) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*U j x) :=
    smooth_newton_lower hn (hU j) (hG j).continuous
      (convolve_nonneg hp (hξp j)) (convolve_nonneg hgp (hξp j))
      (fun y => by dsimp [U,G]; rw [convolve_weak_equation hu.locallyIntegrable (hξ j) (hξc j) heq]; ring) x
  have hFeq : (∫⁻ y, ENNReal.ofReal (‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y)) =
      ∫⁻ y, liminf (fun j => F j y) atTop := by
    apply lintegral_congr_ae
    filter_upwards [hGlim] with y hy
    exact (ENNReal.tendsto_ofReal (hy.const_mul _)).liminf_eq.symm
  rw [hFeq]
  apply (lintegral_liminf_le hFm).trans
  calc
    _ ≤ liminf (fun j => ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*
        ((volume : Measure E).toSphere univ).toReal*U j x)) atTop :=
      liminf_le_liminf (Eventually.of_forall hFint)
    _ = _ := (ENNReal.tendsto_ofReal (hUlim.const_mul _)).liminf_eq
end HenonLaneEmden.WeakPDE

end
end Mollification

end OAI
