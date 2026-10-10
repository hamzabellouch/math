import Mathlib
import OAI.Geometry.SmoothYau.Estimates.NormalFamilyWaveLocalizedEstimates
import OAI.Geometry.SmoothYau.Limits.CompactNormalForwardBound
import OAI.Geometry.SmoothYau.Smoothness.CenteredNormalInverseFderiv
import OAI.Geometry.SmoothYau.Smoothness.FrameInverseApply

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem uniform_localized_physical_waves_with_coordinates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0,
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
        ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
        U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
            T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
            (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y) := by
  obtain ⟨A,b,hA,hb,rc,hrc,hcoeff⟩ := exists_normal_wave_pi_coefficients g hK
  obtain ⟨ri,hri,e,he,hi,hsource,ψ,hψ,hgerm⟩ := exists_normal_wave_chart_family g hK
  obtain ⟨rp,hrp,hpos⟩ := normalWaveMetric_common_positive g hK
  refine ⟨A,b,e,hA,hb,(fun q hq => (hcoeff q hq).1),
    (fun q hq => (hcoeff q hq).2.1),he,?_⟩
  intro B C κ hκ m D
  obtain ⟨rw,hrw,hest⟩ := normal_family_wave_localized_estimates g φ hφ hK A b hA hb
    (fun q hq => (hcoeff q hq).1) (fun q hq => (hcoeff q hq).2.1) B C hκ m D
  obtain ⟨Cf,hCf,hforward⟩ := compact_normal_forward_bound g hK hrw.le
  have hCfpos : 0 < Cf := lt_of_lt_of_le zero_lt_one hCf
  let c := (κ/2)/Cf^2
  have hc : 0 < c := div_pos (half_pos hκ) (sq_pos_of_pos hCfpos)
  let R := min ri (min rc rp)
  have hR : 0 < R := lt_min hri (lt_min hrc hrp)
  obtain ⟨δ,hδ,hδmap⟩ := Metric.continuousAt_iff.mp normalWaveEquiv.continuousAt R hR
  refine ⟨min rw δ,lt_min hrw hδ,?_,?_⟩
  · intro q hq x hx
    apply hsource q hq
    have hxδ : dist x 0 < δ := by simpa only [dist_zero_right] using hx.trans_le (min_le_right rw δ)
    have hxR : ‖normalWaveEquiv x‖ < R := by
      simpa only [map_zero,dist_zero_right] using hδmap hxδ
    simpa only [Metric.mem_closedBall,dist_zero_right] using hxR.le.trans (min_le_left ri (min rc rp))
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨T,hT,hTbound⟩ := hest ζ hζ hζ0
  let L : Set (NormalWaveParameter × NormalWaveSpace) :=
    normalFamilyTotal g '' (metricFrameSet g K ×ˢ Metric.closedBall 0 ri)
  have hL : IsCompact L := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall 0 ri)).image (normalFamilyTotal_smooth g).continuous
  let Ψ : NormalWaveParameter × NormalWaveSpace → (Fin 3 → ℝ) := fun w => normalWaveEquiv.symm (ψ w)
  have hΨ : ContDiff ℝ ∞ Ψ := normalWaveEquiv.symm.contDiff.comp hψ
  obtain ⟨F,hF,hFbound⟩ := compact_fiber_local_comp_bound Ψ hΨ hL m (V := ℂ)
  let U := fun q z Q n => normalChartWave (e q) (normalFamilyWave g φ A b q z Q ζ m D n)
  refine ⟨U,F*T,mul_pos hF hT,c,hc,?_,?_⟩
  · intro q z Q n x hx
    exact normalChartWave_apply (e q) _ hx
  intro q hq z Q hz hnQ hQ n hn hlin
  let f := normalFamilyWave g φ A b q z Q ζ m D n
  let u := U q z Q n
  let fR := fun x => waveCoordinateOperator (fun i => Pi.single i 1)
    (fun i j x => A (q,x) i j) (fun j x => b (q,x) j) f x + (n : ℂ)*((n : ℂ)+2)*f x
  let uR := fun y => complexLaplaceBeltrami g u y + (n : ℂ)*((n : ℂ)+2)*u y
  have hf : ContDiff ℝ ∞ f := contDiff_canonicalCutoffWave _ _ _ _ _ _ hζ _ _ _
  have hfc : HasCompactSupport f := canonicalCutoffWave_compact _ _ _ _ _ _ hcζ _ _ _
  have hfs : tsupport f ⊆ tsupport ζ := canonicalCutoffWave_tsupport _ _ _ _ _ _ _ _ _
  have hxw (x) (hx : x ∈ tsupport f) : x ∈ Metric.ball 0 rw :=
    Metric.ball_subset_ball (min_le_left _ _) (hsζ (hfs hx))
  have hxR (x) (hx : x ∈ tsupport f) : ‖normalWaveEquiv x‖ < R := by
    have hxδ := Metric.ball_subset_ball (min_le_right rw δ) (hsζ (hfs hx))
    simpa only [map_zero,dist_zero_right] using hδmap hxδ
  have hxri (x) (hx : x ∈ tsupport f) : normalWaveEquiv x ∈ Metric.closedBall 0 ri := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      le_trans (hxR x hx).le (min_le_left ri (min rc rp))
  have hxs (x) (hx : x ∈ tsupport f) : normalWaveEquiv x ∈ (e q).source := hsource q hq (hxri x hx)
  have hu : ContDiff ℝ ∞ u := contDiff_normalChartWave (e q) hf hfc hxs (hi q)
  have huc : HasCompactSupport u := normalChartWave_compact (e q) hfc hxs
  have hfR : ContDiff ℝ ∞ fR :=
    (contDiff_waveCoordinateOperator (fun i => Pi.single i 1) _ _
      (fun i j => ((contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)))
      (fun j => ((contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id))) f hf).add
      (contDiff_const.mul hf)
  have hcover (y) (hy : y ∈ tsupport u) : ∃ x ∈ tsupport f,
      y = e q (normalWaveEquiv x) ∧ Ψ (q,y) = x := by
    obtain ⟨x,hx,hxy⟩ := normalChartWave_tsupport (e q) hfc hxs hy
    refine ⟨x,hx,hxy.symm,?_⟩
    have hg := (hgerm q hq (normalWaveEquiv x) (hxri x hx)).eq_of_nhds
    rw [(e q).left_inv (hxs x hx)] at hg
    dsimp only [Ψ]
    rw [←hxy,←hg]
    exact normalWaveEquiv.symm_apply_apply x
  have hlocal (y) (hy : y ∈ tsupport u) : (q,y) ∈ L ∧
      u =ᶠ[𝓝 y] (fun w => f (Ψ (q,w))) ∧ uR =ᶠ[𝓝 y] (fun w => fR (Ψ (q,w))) := by
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hy
    have hgi := hgerm q hq (normalWaveEquiv x) (hxri x hx)
    have hgw : u =ᶠ[𝓝 (e q (normalWaveEquiv x))] (fun w => f (Ψ (q,w))) :=
      (normalChartWave_germ (e q) f ((e q).map_source (hxs x hx))).trans
        (hgi.fun_comp (fun v => f (normalWaveEquiv.symm v)))
    have hxr : ‖normalWaveEquiv x‖ < min rc rp := lt_of_lt_of_le (hxR x hx) (min_le_right _ _)
    have hgr := normalChartWave_residual_germ g q (e q) (he q) hf hfc hxs (hi q)
      (fun i j x => A (q,x) i j) (fun j x => b (q,x) j) ((n : ℂ)*((n : ℂ)+2))
      (fun v hv => hpos q hq v (lt_of_lt_of_le hv (min_le_right rc rp)))
      (fun x hx => ((hcoeff q hq).2.2.2 x (lt_of_lt_of_le hx (min_le_left rc rp))).1)
      (fun x hx => ((hcoeff q hq).2.2.2 x (lt_of_lt_of_le hx (min_le_left rc rp))).2)
      (hxs x hx) hxr
    refine ⟨?_,hgw,hgr.trans (hgi.fun_comp (fun v => fR (normalWaveEquiv.symm v)))⟩
    refine ⟨(q,normalWaveEquiv x),⟨hq,hxri x hx⟩,?_⟩
    change (q,normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
      (normalWaveEquiv x)) = (q,e q (normalWaveEquiv x))
    rw [he q]
  have hbwave : ∀ y ∈ tsupport u, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i f (Ψ (q,y))‖ ≤
        (T*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2))*n^i := by
    intro y hy i hi
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hy
    rw [hΨx]
    have h := (hTbound q hq z Q hz hnQ hQ n hn hlin x (hxw x hx) i hi).1
    have hxrw : ‖x‖ ≤ rw := by
      exact (show ‖x‖ < rw by simpa only [Metric.mem_ball,dist_zero_right] using hxw x hx).le
    have hd := hforward q hq x hxrw
    have hga := gaussian_coordinate_to_physical (half_pos hκ).le hCfpos
      (le_trans zero_le_one hn) (norm_nonneg x)
      (norm_nonneg (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1)) hd
    have h' := h.trans (mul_le_mul_of_nonneg_left hga
      (mul_nonneg (mul_nonneg hT.le (pow_nonneg (le_trans zero_le_one hn) _)) (Real.exp_pos _).le))
    rw [he q]
    change _ ≤ (T*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
      Real.exp (-c*n*‖normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1‖^2))*n^i
    convert h' using 1
    first | rfl | (unfold c; ring)
  have hbr : ∀ y ∈ tsupport uR, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i fR (Ψ (q,y))‖ ≤ (T*(n^(D+1))⁻¹*Real.exp (n*φ y))*1^i := by
    intro y hy i hi
    have hyu := complexLaplaceBeltrami_residual_tsupport g u ((n : ℂ)*((n : ℂ)+2)) hy
    obtain ⟨x,hx,rfl,hΨx⟩ := hcover y hyu
    rw [hΨx,one_pow,mul_one,he q]
    exact (hTbound q hq z Q hz hnQ hQ n hn hlin x (hxw x hx) i hi).2
  have hc0 : f 0 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) :=
    normalFamilyWave_at_zero g φ A b hA hb q (hcoeff q hq).1 (hcoeff q hq).2.1
      z Q hQ hnQ ζ hζ0 m D n
  have hu0 : u q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) := by
    have hs0 : normalWaveEquiv 0 ∈ (e q).source := by
      apply hsource q hq
      simp only [map_zero,Metric.mem_closedBall,dist_self]
      exact hri.le
    have hval := normalChartWave_apply (e q) f hs0
    simpa only [map_zero,he q,normalJetMap_zero,hc0] using hval
  refine ⟨hu,huc,hu0,?_⟩
  intro y k hk
  have hw := hFbound q u f hf (fun y hy => ⟨(hlocal y hy).1,(hlocal y hy).2.1⟩)
    n hn (fun y => T*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2))
    (fun y => mul_nonneg (mul_nonneg hT.le (Real.exp_pos _).le) (Real.exp_pos _).le)
    hbwave y k hk
  have hr := hFbound q uR fR hfR (fun y hy =>
    let h := hlocal y (complexLaplaceBeltrami_residual_tsupport g u ((n : ℂ)*((n : ℂ)+2)) hy)
    ⟨h.1,h.2.2⟩) 1 le_rfl (fun y => T*(n^(D+1))⁻¹*Real.exp (n*φ y))
    (fun y => mul_nonneg (mul_nonneg hT.le (inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hn) _)))
      (Real.exp_pos _).le) hbr y k hk
  constructor
  · convert hw using 1
    ring
  · convert hr using 1
    ring
end



open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem uniform_coordinate_packets_with_endpoint_ratios
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0, ∃ r₀ > 0, ∃ C₀ > 0,
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
      ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        (∀ n : ℝ, 1 ≤ n →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
          U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
              (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ∀ L : NormalWaveSpace →L[ℝ] ℂ, ‖normalPhaseCovector q z-L‖ ≤ δ → C₀*r+δ ≤ 1/2 →
          ‖U q z Q n y-Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖ ≤
            (10*(C₀*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_localized_physical_waves_with_coordinates g φ hφ hK
  refine ⟨A,b,e,hA,hb,hA0,hAd,he,?_⟩
  intro B C κ hκ m D
  obtain ⟨ρ,hρ,hsource,hfactory⟩ := hfactory B C hκ m D
  obtain ⟨ri,hri,ψ,hψ,hψ0,hψd,hnear⟩ := centered_inverse_for_normal_charts g hK e he hρ hsource
  refine ⟨ρ,hρ,hsource,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,hU,hUb⟩ := hfactory ζ hζ hcζ hsζ hζ0
  obtain ⟨re,hre,C₀,hC₀,hend⟩ := normal_family_composed_endpoint_ratio g φ hφ hK A b hA hb hA0 hAd
    ψ hψ hψ0 B C κ ζ hζ0 m D
  refine ⟨U,T,hT,c,hc,min ri re,lt_min hri hre,C₀,hC₀,hU,?_⟩
  intro q hq z Q hz hnQ hQ
  refine ⟨hUb q hq z Q hz hnQ hQ,?_⟩
  intro n r δ hn hr hrr hδ x y hx hy hsep L hL heps
  have hrri : r < ri := hrr.trans_le (min_le_left ri re)
  have hrre : r < re := hrr.trans_le (min_le_right ri re)
  have hEq (v : NormalWaveSpace) (hv : ‖v-q.1‖ ≤ r) :
      U q z Q n v = normalFamilyWave g φ A b q z Q ζ m D n
        (normalWaveEquiv.symm (ψ (q,v-q.1))) := by
    have ht : v-q.1 ∈ Metric.ball (0 : NormalWaveSpace) ri := by
      simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt hrri
    have hh := hnear q hq (v-q.1) ht
    have hu := hU q z Q n (normalWaveEquiv.symm (ψ (q,v-q.1)))
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh.1)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,hh.2.1,add_sub_cancel] using hu
  have hder := normalFamilyPhase_centered_fderiv g φ A hA hq (hA0 q hq) (hAd q hq)
    (fun t => ψ (q,t)) (hψ.comp (contDiff_const.prodMk contDiff_id)) (hψ0 q hq) (hψd q hq)
    z Q hnQ hQ m D
  have hbound := hend q hq z Q hz hnQ hQ n r δ hn hr hrre hδ (x-q.1) (y-q.1) hx hy
    (by simpa only [sub_sub_sub_cancel_right] using hsep) L (by rwa [hder]) heps
  simpa only [←hEq x hx,←hEq y hy,sub_sub_sub_cancel_right] using hbound

end YauCounterexamples
end

end OAI
