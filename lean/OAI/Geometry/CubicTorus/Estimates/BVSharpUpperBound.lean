import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVFlatBlowupRegular

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_normal_rescaled_equicontinuity {μ : FiniteMeasure NormalBundle}
    {N : Torus → Cover} (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (S : ℕ → Set Cover) (ν : ℕ → Cover → Cover) (center : ℕ → Cover)
    (scale : ℕ → ℝ) (hscale : ∀ j, 0 < scale j)
    {c : ℝ} (hc : 0 < c) (r e : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (he : ∀ i, 0 ≤ e i) (helim : Tendsto e atTop (𝓝 0))
    (hm : ∀ j a, a ∈ S j → ∀ i, c*(scale j*r i)^2 ≤
      (spatialNormalMeasure μ : Measure Torus).real
        (Metric.ball (quotientMap (center j+scale j • a)) (scale j*r i)))
    (ht : ∀ j a, a ∈ S j → ∀ i,
      (∫ x in Metric.closedBall (quotientMap (center j+scale j • a)) (2*(scale j*r i)),
        ‖N x-ν j a‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
          (scale j*r i)^2*(e i)^2) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ j a, a ∈ S j → ∀ b, b ∈ S j → dist a b < δ → dist (ν j a) (ν j b) < ε := by
  intro ε hε
  have hl : Tendsto (fun i ↦ (2/Real.sqrt c)*e i) atTop (𝓝 0) := by
    simpa only [mul_zero] using helim.const_mul (2/Real.sqrt c)
  obtain ⟨i,hi⟩ := (hl.eventually (Iio_mem_nhds hε)).exists
  refine ⟨r i,hr i,?_⟩
  intro j a ha b hb hab
  have hdist : dist (quotientMap (center j+scale j • a))
      (quotientMap (center j+scale j • b)) ≤ scale j*r i := by
    rw [dist_eq_norm,← quotientMap_sub]
    apply (norm_quotientMap_le _).trans
    have heq : (center j+scale j • a)-(center j+scale j • b) = scale j • (a-b) := by
      module
    rw [heq,norm_smul,Real.norm_of_nonneg (hscale j).le,← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hab.le (hscale j).le
  have hh := polar_normal_nearby_centers hN hu
    (quotientMap (center j+scale j • a)) (quotientMap (center j+scale j • b))
    hc (mul_pos (hscale j) (hr i)) (he i) (hm j a ha i) hdist
    (ν j a) (ν j b) (ht j a ha i) (ht j b hb i)
  rw [dist_eq_norm]
  exact hh.trans_lt hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_singular_cone_obstruction {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (hsingular : ¬ C1RegularPoint (openRepresentative E) (quotientMap cubeCenter))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (θ : ℝ), MeasurableSet A ∧ 0 < θ ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      ¬ (∃ n : Cover, ‖n‖ = 1 ∧
        ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
          (x ∈ A ↔ x ∈ coverHalfspace n)) := by
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  have hc := cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ) < 1/2)
  obtain ⟨θ',hθ'0,hdens⟩ := exists_density_of_cmc_monotone (by norm_num : (0 : ℝ) < 1/4)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH cubeCenter hc)
  obtain ⟨A,ν,θ,φ,U,hA,hθ0,hφ,hU,hconv,hν,hm,hflux,hrad⟩ :=
    isMinimizerAt_paired_blowup hV hE hmin hμ hH cubeCenter
      (by norm_num : (0 : ℝ) < 1/4) hc r hr hrlim
  have hrl : Tendsto (fun i ↦ r (φ i)) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have heθ : θ'=θ := by
    have hh := blowup_limit_ball_mass cubeCenter (fun i ↦ r (φ i)) (fun i ↦ hr _)
      (hrl.mono_left hU) hdens hν (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    have hh' := hm 1 (by norm_num) (by norm_num)
    norm_num at hh hh'
    exact hh.symm.trans hh'
  subst θ'
  have hsp : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ) := by
    apply hdens.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with t ht
    change cellBallMass μ cubeCenter t / t^2 = _
    rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter t
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ht.le)).trans hc)]
  have heq (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) := isMinimizerAt_blowup_perimeter_eq
    hV hE hmin hμ hθ0 hsp (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hm
    (fun F hF hs ↦ (hflux F hF hs).2) hb hb1
  have hnonflat : ¬ ∃ n : Cover, ‖n‖ = 1 ∧
      ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ A ↔ x ∈ coverHalfspace n) := by
    rintro ⟨n,hn,hAn⟩
    have hθπ := flat_set_limit_density hA hn hAn hθ0
      (heq (1/2) (by norm_num) (by norm_num))
    have hnormal := flat_set_limit_normal hA hn hAn
      (by simpa only [hθπ] using hm (1/2) (by norm_num) (by norm_num))
      (fun F hF hs ↦ (hflux F hF hs).2)
    exact hsingular (isMinimizerAt_c1_of_flat_normal_blowup hV hE hmin hcenter hμ
      (fun i ↦ r (φ i)) (fun i ↦ hr _) (hrl.mono_left hU) hν hn hnormal)
  refine ⟨A,θ,hA,isMinimizerAt_density_pos hV hE hmin hμ hcenter hsp,heq,?_,?_,hnonflat⟩
  · intro B hB a b ha hab hb1 hAB
    exact isMinimizerAt_blowup_local_minimal hV hE hmin hμ hsp (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hB hconv ha hab (by linarith : b ≤ 2)
      (heq b (ha.trans hab) hb1) hAB
  · intro t ht
    exact radial_flux_cone_ae hA (fun ψ hψ hs ↦
      limit_set_radial_flux (fun F hF hFs ↦ (hflux F hF hFs).2) hrad hψ hs) ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma halfspace_line_invariance_orthogonal {B : Set Cover} {N n : Cover}
    (hn : ‖n‖ = 1)
    (hmodel : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ B ↔ x ∈ coverHalfspace N))
    (htrans : ∀ t : ℝ, |t| ≤ 1/4 → ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) (1/4) → (x+t • n ∈ B ↔ x ∈ B)) :
    ⟪N,n⟫ = 0 := by
  by_contra hne
  let U : Set Cover := {x | ‖x‖ < 1/4 ∧ ⟪N,x⟫ * ⟪N,x+(1/8 : ℝ) • n⟫ < 0}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_norm continuous_const
    · exact isOpen_lt (show Continuous (fun x : Cover ↦ ⟪N,x⟫ * ⟪N,x+(1/8 : ℝ) • n⟫) by fun_prop) continuous_const
  have hx : (-(1/16 : ℝ)) • n ∈ U := by
    constructor
    · rw [norm_smul,Real.norm_eq_abs,hn,mul_one]
      norm_num
    · rw [← add_smul,inner_smul_right,inner_smul_right]
      nlinarith [sq_pos_of_ne_zero hne]
  have hshift := (measurePreserving_add_right (volume : Measure Cover) ((1/8 : ℝ) • n)).quasiMeasurePreserving.ae hmodel
  have hzero : volume U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hmodel,hshift,htrans (1/8) (by norm_num)] with x hx hs ht hxu
    have hxsmall : x ∈ Metric.ball (0 : Cover) (1/4) := by
      simpa only [Metric.mem_ball,dist_zero_right] using hxu.1
    have hxlarge : x ∈ Metric.ball (0 : Cover) 1 :=
      Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hxsmall
    have hslarge : x+(1/8 : ℝ) • n ∈ Metric.ball (0 : Cover) 1 := by
      rw [Metric.mem_ball,dist_zero_right]
      have hh := norm_add_le x ((1/8 : ℝ) • n)
      rw [norm_smul,Real.norm_eq_abs,hn,mul_one] at hh
      norm_num at hh
      exact hh.trans_lt (by linarith [hxu.1])
    have he := (hs hslarge).symm.trans ((ht hxsmall).trans (hx hxlarge))
    change (⟪N,x+(1/8 : ℝ) • n⟫ < 0) ↔ (⟪N,x⟫ < 0) at he
    have hp : 0 ≤ ⟪N,x⟫ * ⟪N,x+(1/8 : ℝ) • n⟫ := by
      by_cases h : ⟪N,x⟫ < 0
      · exact mul_nonneg_of_nonpos_of_nonpos h.le (he.mpr h).le
      · exact mul_nonneg (le_of_not_gt h) (le_of_not_gt (mt he.mp h))
    exact (not_lt_of_ge hp) hxu.2
  exact hU.measure_ne_zero volume ⟨_,hx⟩ hzero

lemma radial_cone_secondary_halfspace_orthogonal {A B : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0)) {N : Cover}
    (hmodel : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ B ↔ x ∈ coverHalfspace N)) : ⟪N,p⟫ = 0 := by
  have hn : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]
  have hh := halfspace_line_invariance_orthogonal hn hmodel
    (radial_cone_secondary_unit_line hA hB hcone p hp hp0 r hr hrlim hconv)
  rw [inner_smul_right] at hh
  exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hp0))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_singular_dimension_reduction {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (hsingular : ¬ C1RegularPoint (openRepresentative E) (quotientMap cubeCenter))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (θ : ℝ), MeasurableSet A ∧ 0 < θ ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      ¬ (∃ n : Cover, ‖n‖ = 1 ∧
        ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
          (x ∈ A ↔ x ∈ coverHalfspace n)) ∧
      ∀ p : Cover, ‖p‖ < 1 → p ≠ 0 →
        (∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
          0 < volume.real (Aᶜ ∩ Metric.ball p δ)) →
        ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → (∀ i, s i ≤ 1) → Tendsto s atTop (𝓝 0) →
        ∃ (B : Set Cover) (ψ : ℕ → ℕ) (n : Cover),
          MeasurableSet B ∧ StrictMono ψ ∧ ‖n‖ = 1 ∧ ⟪n,p⟫ = 0 ∧
          Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
            |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (ψ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
            atTop (𝓝 0) ∧
          ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
            (x ∈ B ↔ x ∈ coverHalfspace n) := by
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  have hc := cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ) < 1/2)
  obtain ⟨θ',hθ'0,hdens⟩ := exists_density_of_cmc_monotone (by norm_num : (0 : ℝ) < 1/4)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH cubeCenter hc)
  obtain ⟨A,ν,θ,φ,U,hA,hθ0,hφ,hU,hconv,hν,hm,hflux,hrad⟩ :=
    isMinimizerAt_paired_blowup hV hE hmin hμ hH cubeCenter
      (by norm_num : (0 : ℝ) < 1/4) hc r hr hrlim
  have hrl : Tendsto (fun i ↦ r (φ i)) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have heθ : θ'=θ := by
    have hh := blowup_limit_ball_mass cubeCenter (fun i ↦ r (φ i)) (fun i ↦ hr _)
      (hrl.mono_left hU) hdens hν (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    have hh' := hm 1 (by norm_num) (by norm_num)
    norm_num at hh hh'
    exact hh.symm.trans hh'
  subst θ'
  have hsp : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ) := by
    apply hdens.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with t ht
    change cellBallMass μ cubeCenter t / t^2 = _
    rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter t
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ht.le)).trans hc)]
  have heq (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) := isMinimizerAt_blowup_perimeter_eq
    hV hE hmin hμ hθ0 hsp (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hm
    (fun F hF hs ↦ (hflux F hF hs).2) hb hb1
  have hnonflat : ¬ ∃ n : Cover, ‖n‖ = 1 ∧
      ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ A ↔ x ∈ coverHalfspace n) := by
    rintro ⟨n,hn,hAn⟩
    have hθπ := flat_set_limit_density hA hn hAn hθ0
      (heq (1/2) (by norm_num) (by norm_num))
    have hnormal := flat_set_limit_normal hA hn hAn
      (by simpa only [hθπ] using hm (1/2) (by norm_num) (by norm_num))
      (fun F hF hs ↦ (hflux F hF hs).2)
    exact hsingular (isMinimizerAt_c1_of_flat_normal_blowup hV hE hmin hcenter hμ
      (fun i ↦ r (φ i)) (fun i ↦ hr _) (hrl.mono_left hU) hν hn hnormal)
  have hcone (t : ℝ) (ht : 1 ≤ t) := radial_flux_cone_ae hA (fun ψ hψ hs ↦
    limit_set_radial_flux (fun F hF hFs ↦ (hflux F hF hFs).2) hrad hψ hs) ht
  refine ⟨A,θ,hA,isMinimizerAt_density_pos hV hE hmin hμ hcenter hsp,heq,?_,hcone,hnonflat,?_⟩
  · intro B hB a b ha hab hb1 hAB
    exact isMinimizerAt_blowup_local_minimal hV hE hmin hμ hsp (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hB hconv ha hab (by linarith : b ≤ 2)
      (heq b (ha.trans hab) hb1) hAB
  · intro p hp hp0 hboundary s hs hs1 hslim
    obtain ⟨B,ψ,n,hB,hψ,hn,hBc,hmodel,_,_,_⟩ := actual_secondary_halfspace hV hE hmin hμ hH
      (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hcone hflux p hp hp0 hboundary s hs hs1 hslim
    have horth := radial_cone_secondary_halfspace_orthogonal hA hB hcone p hp hp0
      (fun i ↦ s (ψ i)) (fun i ↦ hs _) (hslim.comp hψ.tendsto_atTop) hBc hmodel
    exact ⟨B,ψ,n,hB,hψ,hn,horth,hBc,hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

def fieldMove (F : Cover → Cover) (t : ℝ) (x : Cover) : Cover := x + t • F x

def fieldMoveDeriv (F : Cover → Cover) (t : ℝ) (x : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover + t • fderiv ℝ F x

def derivativeEntry (F : Cover → Cover) (x : Cover) (i j : Fin 3) : ℝ :=
  (fderiv ℝ F x (EuclideanSpace.single j 1)) i

def secondJacobian (F : Cover → Cover) (x : Cover) : ℝ :=
  derivativeEntry F x 0 0 * derivativeEntry F x 1 1 +
  derivativeEntry F x 0 0 * derivativeEntry F x 2 2 +
  derivativeEntry F x 1 1 * derivativeEntry F x 2 2 -
  derivativeEntry F x 0 1 * derivativeEntry F x 1 0 -
  derivativeEntry F x 0 2 * derivativeEntry F x 2 0 -
  derivativeEntry F x 1 2 * derivativeEntry F x 2 1

def thirdJacobian (F : Cover → Cover) (x : Cover) : ℝ :=
  Matrix.det (Matrix.of (derivativeEntry F x))

lemma fieldMove_hasFDerivAt {F : Cover → Cover} {x : Cover}
    (hf : DifferentiableAt ℝ F x) (t : ℝ) :
    HasFDerivAt (fieldMove F t) (fieldMoveDeriv F t x) x :=
  (hasFDerivAt_id x).add (hf.hasFDerivAt.const_smul t)

lemma fieldMoveDeriv_det (F : Cover → Cover) (t : ℝ) (x : Cover) :
    (fieldMoveDeriv F t x).det =
      1 + t * divergence F x + t ^ 2 * secondJacobian F x + t ^ 3 * thirdJacobian F x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (fieldMoveDeriv F t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) + t * derivativeEntry F x j k) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (fieldMoveDeriv F t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    simp [fieldMoveDeriv, derivativeEntry]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  simp [Matrix.det_fin_three, divergence, secondJacobian, thirdJacobian,
    derivativeEntry, Fin.sum_univ_succ]
  ring

lemma fieldMove_injective {F : Cover → Cover} (hf : Differentiable ℝ F)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M) {t : ℝ}
    (ht : |t| * M < 1) : Function.Injective (fieldMove F t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = (-t) • (F x - F y) := by
    calc
      x - y = fieldMove F t x - fieldMove F t y - t • (F x - F y) := by
        unfold fieldMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖F x - F y‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    calc
      ‖x - y‖ = |t| * ‖F x - F y‖ := hn
      _ ≤ |t| * ((M : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

lemma continuous_derivativeEntry {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) : Continuous (fun x ↦ derivativeEntry F x i j) := by
  exact (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma continuous_secondJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (secondJacobian F) := by
  unfold secondJacobian
  exact (((((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 1 1)).add
    ((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 2 2))).add
    ((continuous_derivativeEntry hf 1 1).mul (continuous_derivativeEntry hf 2 2))).sub
    ((continuous_derivativeEntry hf 0 1).mul (continuous_derivativeEntry hf 1 0))).sub
    ((continuous_derivativeEntry hf 0 2).mul (continuous_derivativeEntry hf 2 0)) |>.sub
    ((continuous_derivativeEntry hf 1 2).mul (continuous_derivativeEntry hf 2 1))

lemma continuous_thirdJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (thirdJacobian F) := by
  exact (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_derivativeEntry hf i j).matrix_det

lemma integral_det_fieldMove {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    {A : Set Cover} (hAc : IsCompact (closure A)) (t : ℝ) :
    (∫ x in A, (fieldMoveDeriv F t x).det) = volume.real A +
      t * (∫ x in A, divergence F x) + t ^ 2 * (∫ x in A, secondJacobian F x) +
      t ^ 3 * (∫ x in A, thirdJacobian F x) := by
  have h1 : IntegrableOn (divergence F) (closure A) volume :=
    (continuous_divergence hf).continuousOn.integrableOn_compact hAc
  have h2 : IntegrableOn (secondJacobian F) (closure A) volume :=
    (continuous_secondJacobian hf).continuousOn.integrableOn_compact hAc
  have h3 : IntegrableOn (thirdJacobian F) (closure A) volume :=
    (continuous_thirdJacobian hf).continuousOn.integrableOn_compact hAc
  have hμ : volume A < ⊤ := (measure_mono subset_closure).trans_lt hAc.measure_lt_top
  have hc : IntegrableOn (fun _ : Cover ↦ (1 : ℝ)) A :=
    integrableOn_const hμ.ne
  simp_rw [fieldMoveDeriv_det]
  rw [integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x + t^2 * secondJacobian F x)
      (g := fun x ↦ t^3 * thirdJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        ((hc.add ((h1.mono_set subset_closure).const_mul t)).add
          ((h2.mono_set subset_closure).const_mul (t^2))))
      ((h3.mono_set subset_closure).const_mul (t^3)),
    integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x)
      (g := fun x ↦ t^2 * secondJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        (hc.add ((h1.mono_set subset_closure).const_mul t)))
      ((h2.mono_set subset_closure).const_mul (t^2)),
    integral_add (μ := volume.restrict A) (f := fun _ : Cover ↦ (1 : ℝ)) (g := fun x ↦ t * divergence F x)
      hc ((h1.mono_set subset_closure).const_mul t)]
  simp only [integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma integral_det_fieldMove_le_volume {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {A : Set Cover} (hA : MeasurableSet A)
    (hAc : IsCompact (closure A)) :
    (∫ x in A, (fieldMoveDeriv F t x).det) ≤ volume.real (fieldMove F t '' A) := by
  have hdet : Continuous (fun x ↦ (fieldMoveDeriv F t x).det) :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add ((hf.continuous_fderiv (by simp)).const_smul t))
  have hi : IntegrableOn (fun x ↦ (fieldMoveDeriv F t x).det) A volume :=
    (hdet.continuousOn.integrableOn_compact hAc).mono_set subset_closure
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume hA
    (fun x (_ : x ∈ A) ↦
      (fieldMove_hasFDerivAt (hf.differentiable (by simp) x) t).hasFDerivWithinAt)
    (fieldMove_injective (hf.differentiable (by simp)) hM ht).injOn (fun _ ↦ (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hj
  rw [hj]
  exact integral_mono hi hi.abs (fun x ↦ le_abs_self _)

lemma realVolume_cover_ball (c : Cover) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball c r) = r ^ 3 * (Real.pi * 4 / 3) := by
  simp only [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.pi * 4 / 3)]

lemma fieldMove_ball_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (c : Cover) (r : ℝ) :
    fieldMove F t '' Metric.ball c r ⊆ Metric.ball c (r + t) := by
  rintro _ ⟨x, hx, rfl⟩
  have hh : ‖t • F x‖ ≤ t := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
      mul_le_mul_of_nonneg_left (hF x) ht
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  calc
    ‖fieldMove F t x - c‖ = ‖(x - c) + t • F x‖ := by congr 1; unfold fieldMove; abel
    _ ≤ ‖x - c‖ + ‖t • F x‖ := norm_add_le _ _
    _ < r + t := add_lt_add_of_lt_of_le hx hh

lemma flux_cover_ball_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (c : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball c r, divergence F x) ≤ 4 * Real.pi * r ^ 2 := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in Metric.ball c r, divergence F x
  let Q := ∫ x in Metric.ball c r, secondJacobian F x
  let R := ∫ x in Metric.ball c r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M + 1) →
      P + t * Q + t ^ 2 * R ≤
        4 * Real.pi * r ^ 2 + 4 * Real.pi * r * t + (Real.pi * 4 / 3) * t ^ 2 := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t * M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM (A := Metric.ball c r) Metric.isOpen_ball.measurableSet
      (Metric.isBounded_ball.isCompact_closure)
    have hv' : volume.real (fieldMove F t '' Metric.ball c r) ≤
        volume.real (Metric.ball c (r + t)) := by
      exact ENNReal.toReal_mono measure_ball_ne_top (measure_mono (fieldMove_ball_subset hF ht0.le c r))
    rw [integral_det_fieldMove hf Metric.isBounded_ball.isCompact_closure,
      realVolume_cover_ball c hr.le] at hv
    rw [realVolume_cover_ball c (by linarith)] at hv'
    have hh := hv.trans hv'
    change r^3 * (Real.pi*4/3) + t*P + t^2*Q + t^3*R ≤ _ at hh
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t * Q + t^2 * R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t * Q + t^2 * R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
      (Real.pi * 4 / 3) * t^2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Real.pi * r^2)) := by
    have hh : Continuous (fun t : ℝ ↦ 4 * Real.pi * r^2 + 4 * Real.pi * r * t +
        (Real.pi * 4 / 3) * t^2) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

def cubeCenter : Cover := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def cubeBall (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball cubeCenter r

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet (cubeBall r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 1 / 2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeBall r = Metric.ball cubeCenter r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball cubeCenter r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (cubeBall r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

lemma perimeter_cubeBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (cubeBall r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeBall_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_cover_ball_le hF.1 hF.2.1 hF.2.2 cubeCenter hr0)

lemma finitePerimeter_cubeBall {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    FinitePerimeter (cubeBall r) :=
  ⟨(measurableSet_cubeBall r).nullMeasurableSet,
    (perimeter_cubeBall_le hr0 hr1).trans_lt ENNReal.ofReal_lt_top⟩

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma centeredBall_eq_cubeBall_preimage (r : ℝ) :
    Metric.ball (0 : Torus) r =
      (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeBall r := by
  rw [cubeBall_eq_metricBall]
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

lemma volume_centeredBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    torusVolume (Metric.ball (0 : Torus) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [centeredBall_eq_cubeBall_preimage,
    volume_translation (measurableSet_cubeBall r).nullMeasurableSet, volume_cubeBall hr0 hr1]

lemma perimeter_centeredBall_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    perimeter (Metric.ball (0 : Torus) r) ≤ ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  rw [centeredBall_eq_cubeBall_preimage,
    perimeter_translation (measurableSet_cubeBall r).nullMeasurableSet]
  exact perimeter_cubeBall_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def discProjection : Cover →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ x i.succ)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

@[simp] lemma discProjection_apply (x : Cover) (i : Fin 2) :
    discProjection x i = x i.succ := rfl

lemma discProjection_norm_le (x : Cover) : ‖discProjection x‖ ≤ ‖x‖ := by
  have hh : ‖discProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [discProjection_apply, Fin.sum_univ_succ]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (discProjection x), norm_nonneg x]

def tubeSplit : Cover ≃ᵐ ℝ × Plane :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

@[simp] lemma tubeSplit_apply (x : Cover) : tubeSplit x = (x 0, discProjection x) := by
  rfl

@[simp] lemma tubeSplit_symm_zero (p : ℝ × Plane) : (tubeSplit.symm p) 0 = p.1 := by
  simp [tubeSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr]

@[simp] lemma tubeSplit_symm_succ (p : ℝ × Plane) (i : Fin 2) :
    (tubeSplit.symm p) i.succ = p.2 i := by
  simp [tubeSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr]

lemma continuous_tubeSplit : Continuous tubeSplit := by
  change Continuous (fun x : Cover ↦ (x 0, discProjection x))
  fun_prop

lemma continuous_tubeSplit_symm : Continuous tubeSplit.symm := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).continuous_symm.comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × Plane ↦ tubeSplit.symm p i)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [tubeSplit_symm_zero] using (continuous_fst : Continuous (fun p : ℝ × Plane ↦ p.1))
  · simp_rw [tubeSplit_symm_succ]
    fun_prop

lemma tubeSplit_measurePreserving : MeasurePreserving tubeSplit := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

def discCenter : Plane := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def coverTube (r : ℝ) : Set Cover :=
  tubeSplit ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)

lemma measurableSet_coverTube (r : ℝ) : MeasurableSet (coverTube r) :=
  (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).preimage tubeSplit.measurable

lemma isCompact_closure_coverTube (r : ℝ) : IsCompact (closure (coverTube r)) := by
  have hc : IsCompact (tubeSplit.symm '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall discCenter r)) :=
    (isCompact_Icc.prod (isCompact_closedBall discCenter r)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨tubeSplit x, ⟨⟨hx.1.1, hx.1.2.le⟩, Metric.ball_subset_closedBall hx.2⟩, ?_⟩
  exact tubeSplit.symm_apply_apply x

lemma volume_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume (coverTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [coverTube, tubeSplit_measurePreserving.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
      EuclideanSpace.volume_ball_fin_two]
    simp only [sub_zero, ENNReal.ofReal_one, one_mul]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr]
    ring
  · exact (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).nullMeasurableSet

lemma volumeReal_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coverTube r) = Real.pi * r^2 := by
  rw [Measure.real_def, volume_coverTube hr, ENNReal.toReal_ofReal (by positivity)]

def axialProjection : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover -
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1)

@[simp] lemma axialProjection_zero (x : Cover) : axialProjection x 0 = 0 := by
  simp [axialProjection]

@[simp] lemma axialProjection_succ (x : Cover) (i : Fin 2) :
    axialProjection x i.succ = x i.succ := by
  simp [axialProjection]

lemma axialProjection_norm_le (x : Cover) : ‖axialProjection x‖ ≤ ‖x‖ := by
  have hh : ‖axialProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_succ, axialProjection_zero, axialProjection_succ, norm_zero,
      zero_pow (by omega : 2 ≠ 0), zero_add]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (axialProjection x), norm_nonneg x]

lemma fieldMove_coverTube_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    (hF0 : ∀ x, F x 0 = 0) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    fieldMove F t '' coverTube r ⊆ coverTube (r+t) := by
  rintro _ ⟨x, hx, rfl⟩
  change (fieldMove F t x) 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (fieldMove F t x) ∈ Metric.ball discCenter (r+t)
  constructor
  · simpa [fieldMove, hF0 x] using hx.1
  · have hb : ‖discProjection (F x)‖ ≤ 1 := (discProjection_norm_le _).trans (hF x)
    have hh : ‖t • discProjection (F x)‖ ≤ t := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
        mul_le_mul_of_nonneg_left hb ht
    have hd : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      _ = ‖(discProjection x - discCenter) + t • discProjection (F x)‖ := by
        congr 1
        simp only [fieldMove, map_add, map_smul]
        abel
      _ ≤ ‖discProjection x - discCenter‖ + ‖t • discProjection (F x)‖ := norm_add_le _ _
      _ < r+t := add_lt_add_of_lt_of_le hd hh

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma tubeSplit_symm_line (u : ℝ) (y : Plane) :
    tubeSplit.symm (u,y) = tubeSplit.symm (0,y) + u • EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

lemma hasDerivAt_tubeLine (u : ℝ) (y : Plane) :
    HasDerivAt (fun t : ℝ ↦ tubeSplit.symm (t,y)) (EuclideanSpace.single 0 1) u := by
  have he : (fun t : ℝ ↦ tubeSplit.symm (t,y)) =
      (fun t : ℝ ↦ tubeSplit.symm (0,y) + t • EuclideanSpace.single 0 1) :=
    funext (fun t ↦ tubeSplit_symm_line t y)
  rw [he]
  simpa! only [Pi.add_def, zero_add, one_smul, id_eq] using
    (hasDerivAt_const u (tubeSplit.symm (0,y))).add
      ((hasDerivAt_id u).smul_const (EuclideanSpace.single 0 1))

lemma axial_integral_eq_zero {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (y : Plane) :
    (∫ u in Ico (0 : ℝ) 1, derivativeEntry F (tubeSplit.symm (u,y)) 0 0) = 0 := by
  have hd (u : ℝ) : HasDerivAt (fun u ↦ F (tubeSplit.symm (u,y)) 0)
      (derivativeEntry F (tubeSplit.symm (u,y)) 0 0) u := by
    exact (EuclideanSpace.proj 0).hasFDerivAt.comp_hasDerivAt u
      (((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt u
        (hasDerivAt_tubeLine u y))
  have hc : Continuous (fun u ↦ derivativeEntry F (tubeSplit.symm (u,y)) 0 0) :=
    (continuous_derivativeEntry hf 0 0).comp (continuous_tubeSplit_symm.comp (by fun_prop))
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u) (hc.intervalIntegrable 0 1)]
  have he : tubeSplit.symm (1,y) = tubeSplit.symm (0,y) + latticeVector (Pi.single 0 1) := by
    rw [tubeSplit_symm_line 1 y]
    congr 1
    ext i
    simp [latticeVector, Pi.single_apply]
  rw [he, hp]
  simp

lemma integral_axial_coverTube {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, derivativeEntry F x 0 0) = 0 := by
  let g : ℝ × Plane → ℝ := fun p ↦ derivativeEntry F (tubeSplit.symm p) 0 0
  have hint : IntegrableOn (fun x ↦ derivativeEntry F x 0 0) (coverTube r) :=
    ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g, Function.comp_def, tubeSplit.symm_apply_apply, coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  simp only [g, tubeSplit.symm_apply_apply] at he
  change (∫ x in coverTube r, derivativeEntry F x 0 0) = _ at he
  rw [he]
  change (∫ p in Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r, g p) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [integral_prod_symm g hi]
  simp only [g, axial_integral_eq_zero hf hp, integral_zero]

lemma divergence_axialProjection {x : Cover} {F : Cover → Cover} (hf : DifferentiableAt ℝ F x) :
    divergence (fun y ↦ axialProjection (F y)) x = divergence F x - derivativeEntry F x 0 0 := by
  have hc : HasFDerivAt (fun y ↦ axialProjection (F y))
      (axialProjection.comp (fderiv ℝ F x)) x :=
    axialProjection.hasFDerivAt.comp x hf.hasFDerivAt
  simp only [divergence, hc.fderiv, ContinuousLinearMap.comp_apply, Fin.sum_univ_succ,
    axialProjection_zero, axialProjection_succ, derivativeEntry]
  ring

lemma flux_axialProjection {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, divergence (fun y ↦ axialProjection (F y)) x) =
      ∫ x in coverTube r, divergence F x := by
  simp_rw [divergence_axialProjection ((hf.differentiable (by simp)).differentiableAt)]
  rw [integral_sub]
  · rw [integral_axial_coverTube hf hp, sub_zero]
  · exact ((continuous_divergence hf).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  · exact ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma flux_coverTube_axial_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : ∀ x, F x 0 = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in coverTube r, divergence F x
  let Q := ∫ x in coverTube r, secondJacobian F x
  let R := ∫ x in coverTube r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M+1) →
      P + t*Q + t^2*R ≤ 2 * Real.pi * r + Real.pi*t := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t*M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM
      (measurableSet_coverTube r) (isCompact_closure_coverTube r)
    have hfin : volume (coverTube (r+t)) ≠ ⊤ := by
      rw [volume_coverTube (by linarith)]
      exact ENNReal.ofReal_ne_top
    have hv' : volume.real (fieldMove F t '' coverTube r) ≤ volume.real (coverTube (r+t)) :=
      ENNReal.toReal_mono hfin (measure_mono (fieldMove_coverTube_subset hF hF0 ht0.le r))
    rw [integral_det_fieldMove hf (isCompact_closure_coverTube r)] at hv
    rw [volumeReal_coverTube (by linarith : 0 ≤ r+t)] at hv'
    rw [volumeReal_coverTube hr.le] at hv
    change Real.pi*r^2 + t*P + t^2*Q + t^3*R ≤ _ at hv
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith [hv.trans hv']
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t*Q + t^2*R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t*Q + t^2*R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*r)) := by
    have hh : Continuous (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1/(M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

lemma flux_coverTube_le {F : Cover → Cover} (hF : AdmissibleField F)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  rw [← flux_axialProjection hF.1 hF.2.1 r]
  apply flux_coverTube_axial_le (axialProjection.contDiff.comp hF.1)
  · intro n x
    change axialProjection (F (x + latticeVector n)) = axialProjection (F x)
    rw [hF.2.1]
  · intro x
    exact (axialProjection_norm_le _).trans (hF.2.2 x)
  · intro x
    exact axialProjection_zero (F x)
  · exact hr

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma representative_mem_cube (x : Torus) : representative x ∈ fundamentalCube := by
  intro i
  exact ⟨((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.1,
    by simpa! only [representative, PiLp.toLp_apply, zero_add] using
      ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.2⟩

lemma coverTube_subset_cube {r : ℝ} (hr : r ≤ 1/2) : coverTube r ⊆ fundamentalCube := by
  intro x hx i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hx.1
  · have hnorm : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    have hi := (PiLp.norm_apply_le (discProjection x - discCenter) j).trans_lt hnorm
    change |x j.succ - (1/2 : ℝ)| < r at hi
    rw [abs_lt] at hi
    constructor <;> linarith

def cubeTube (r : ℝ) : Set Torus := representative ⁻¹' coverTube r

lemma measurableSet_cubeTube (r : ℝ) : MeasurableSet (cubeTube r) :=
  (measurableSet_coverTube r).preimage measurable_representative

lemma cubeTube_lift {r : ℝ} (hr : r ≤ 1/2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeTube r = coverTube r := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    change representative (quotientMap x) ∈ coverTube r at ht
    rwa [representative_quotientMap_of_mem hx] at ht
  · intro ht
    have hx := coverTube_subset_cube hr ht
    refine ⟨hx, ?_⟩
    change representative (quotientMap x) ∈ coverTube r
    rwa [representative_quotientMap_of_mem hx]

lemma volume_cubeTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (cubeTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeTube r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeTube r)), inter_comm,
    cubeTube_lift hr1, volume_coverTube hr0]

lemma perimeter_cubeTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (cubeTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeTube_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_coverTube_le hF hr0)

lemma norm_representative_sub_half (x : Torus) (i : Fin 3) :
    ‖representative x i - (1/2 : ℝ)‖ = ‖x i - ((1/2 : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hi := representative_mem_cube x i
  have hb : |representative x i - (1/2 : ℝ)| ≤ |(1 : ℝ)|/2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hn : ‖((representative x i - (1/2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1/2 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hb
  have hxi : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i :=
    congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [map_sub, hxi, Real.norm_eq_abs] using hn.symm

def centeredTube (r : ℝ) : Set Torus := {x | ‖x 1‖^2 + ‖x 2‖^2 < r^2}

lemma mem_cubeTube_iff {r : ℝ} (hr : 0 ≤ r) (x : Torus) :
    x ∈ cubeTube r ↔ x - quotientMap cubeCenter ∈ centeredTube r := by
  change (representative x 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (representative x) ∈ Metric.ball discCenter r) ↔ _
  simp only [mem_Ico]
  rw [and_iff_right (representative_mem_cube x 0), Metric.mem_ball, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) hr, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, discProjection_apply, discCenter,
    norm_representative_sub_half]
  rfl

lemma centeredTube_eq_cubeTube_preimage {r : ℝ} (hr : 0 ≤ r) :
    centeredTube r = (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeTube r := by
  ext x
  simp only [mem_preimage, mem_cubeTube_iff hr, add_sub_cancel_right]

lemma measurableSet_centeredTube (r : ℝ) : MeasurableSet (centeredTube r) := by
  apply measurableSet_lt
  · fun_prop
  · fun_prop

lemma volume_centeredTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (centeredTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [centeredTube_eq_cubeTube_preimage hr0,
    volume_translation (measurableSet_cubeTube r).nullMeasurableSet,
    volume_cubeTube hr0 hr1]

lemma perimeter_centeredTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (centeredTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  rw [centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (measurableSet_cubeTube r).nullMeasurableSet]
  exact perimeter_cubeTube_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma cube_cuberoot (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

lemma cube_two_thirds (x : ℝ) (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma canonicalBall_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < (3*V/(4*Real.pi))^(1/3 : ℝ) ∧
    (3*V/(4*Real.pi))^(1/3 : ℝ) ≤ 1/2 ∧
    ((3*V/(4*Real.pi))^(1/3 : ℝ))^3 * (Real.pi*4/3) = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  have hv : 0 < 3*V/(4*Real.pi) := by positivity
  have hc := cube_cuberoot _ hv.le
  refine ⟨Real.rpow_pos_of_pos hv _, ?_, ?_⟩
  · have hbound : 3*V/(4*Real.pi) ≤ (1/2 : ℝ)^3 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
      nlinarith [Real.pi_gt_three, hV.2]
    have hp3 : Odd (3 : ℕ) := by decide
    apply hp3.strictMono_pow.le_iff_le.1
    rw [hc]
    exact hbound
  · rw [hc]
    field_simp

lemma ballArea_formula {V : ℝ} (hV : 0 ≤ V) :
    4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2 =
      (36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
  apply (show Odd (3 : ℕ) by decide).pow_injective
  have hc := cube_cuberoot (3*V/(4*Real.pi)) (by positivity)
  have hpc := cube_cuberoot (36*Real.pi) (by positivity)
  have hvc := cube_two_thirds V hV
  dsimp only
  calc
    (4*Real.pi*((3*V/(4*Real.pi))^(1/3 : ℝ))^2)^3 =
        (4*Real.pi)^3 * (((3*V/(4*Real.pi))^(1/3 : ℝ))^3)^2 := by ring
    _ = 36*Real.pi*V^2 := by rw [hc]; field_simp; ring
    _ = _ := by rw [mul_pow, hpc, hvc]

lemma volume_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalBall V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalBall_radius_properties hV
  change torusVolume (Metric.ball (0 : Torus) _) = _
  rw [volume_centeredBall hr0.le hr1, heq]

lemma perimeter_canonicalBall_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalBall V) ≤
      ENNReal.ofReal ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalBall_radius_properties hV
  exact (perimeter_centeredBall_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (ballArea_formula hV.1.le))

lemma finitePerimeter_canonicalBall {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalBall V) :=
  ⟨Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    (perimeter_canonicalBall_le hV).trans_lt ENNReal.ofReal_lt_top⟩

lemma canonicalTube_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < Real.sqrt (V/Real.pi) ∧ Real.sqrt (V/Real.pi) ≤ 1/2 ∧
    Real.pi * (Real.sqrt (V/Real.pi))^2 = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  refine ⟨Real.sqrt_pos.2 (div_pos hV.1 hp), ?_, ?_⟩
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_gt_three, hV.2]
  · rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma tubeArea_formula {V : ℝ} (hV : 0 ≤ V) :
    2*Real.pi*Real.sqrt (V/Real.pi) = 2*Real.sqrt (Real.pi*V) := by
  have hp := Real.pi_pos
  have heq : Real.pi*Real.sqrt (V/Real.pi) = Real.sqrt (Real.pi*V) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  calc
    _ = 2*(Real.pi*Real.sqrt (V/Real.pi)) := by ring
    _ = _ := by rw [heq]

lemma volume_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalTube V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalTube_radius_properties hV
  change torusVolume (centeredTube _) = _
  rw [volume_centeredTube hr0.le hr1, heq]

lemma perimeter_canonicalTube_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V) ≤ ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalTube_radius_properties hV
  exact (perimeter_centeredTube_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (tubeArea_formula hV.1.le))

lemma finitePerimeter_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalTube V) :=
  ⟨(measurableSet_centeredTube _).nullMeasurableSet,
    (perimeter_canonicalTube_le hV).trans_lt ENNReal.ofReal_lt_top⟩

theorem isMinimizerAt_perimeter_le_envelope {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal
      (min ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ))
        (min (2*Real.sqrt (Real.pi*V)) 2)) := by
  rw [ENNReal.ofReal_min, ENNReal.ofReal_min]
  refine le_min ?_ (le_min ?_ ?_)
  · exact (hE.2.2 _ (finitePerimeter_canonicalBall hV) (volume_canonicalBall hV)).trans
      (perimeter_canonicalBall_le hV)
  · exact (hE.2.2 _ (finitePerimeter_canonicalTube hV) (volume_canonicalTube hV)).trans
      (perimeter_canonicalTube_le hV)
  · have hVI : V ∈ Icc (0 : ℝ) 1 := ⟨hV.1.le, by linarith [hV.2]⟩
    simpa only [ENNReal.ofReal_ofNat] using
      (hE.2.2 _ (finitePerimeter_stripe hVI) (volume_stripe hVI)).trans (perimeter_stripe_le hVI)

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) := by
  by_cases hhalf : V ≤ 1/2
  · simpa only [candidateProfile, min_eq_left (by linarith : V ≤ 1-V)] using
      isMinimizerAt_perimeter_le_envelope ⟨hV.1, hhalf⟩ hE
  · have hvol : 1-V ∈ Ioc (0 : ℝ) (1/2) := ⟨by linarith [hV.2], by linarith⟩
    have hcompl := (isMinimizerAt_compl ⟨hV.1.le, hV.2.le⟩).2 hE
    have hh := isMinimizerAt_perimeter_le_envelope hvol hcompl
    simpa only [perimeter_compl hE.1.1, candidateProfile,
      min_eq_right (by linarith : 1-V ≤ V)] using hh

end CubicTorus.UpperComparison

namespace CubicTorus

theorem isMinimizerAt_perimeter_le_candidateProfile {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : IsMinimizerAt V E) :
    perimeter E ≤ ENNReal.ofReal (candidateProfile V) :=
  UpperComparison.isMinimizerAt_perimeter_le_candidateProfile hV hE

end CubicTorus

end
end

end

end OAI
