import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRelativeHessianBound
import OAI.Analysis.BiholderTransport.Calculus.ScalarInverseJet
import OAI.Analysis.BiholderTransport.Convexity.TranslatedMinorant

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalOuterJetBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_outer_chart_jet_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0≤cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m lmax : ℝ} (hm : 0 < m) (hlmax : 0 < lmax) :
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)),
      N∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a,L) ∧ ∃ C≥0,
      ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (c : Model n → ℝ) (l:ℝ),0 < l → l≤lmax →
      ContDiffAt ℝ 2 c z → (z,l⁻¹ • (-fderiv ℝ c z))∈N →
      (∀ d:Model n,2*m*l*‖d‖^2≤
        l*fderiv ℝ (fderiv ℝ (chartCost a
          (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z d d-
          fderiv ℝ (fderiv ℝ c) z d d) →
      ∀ φ:ℝ → ℝ,StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      HasDerivAt φ l (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z))≤0 →
      ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
      HasLowerSecondTaylor (fun h => φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h)))+
        c (z+h)) 0 H → ∀ d,H d d≤C*‖d‖^2 := by
  obtain ⟨N,hN,C,hC,HC⟩ := hmtw.exists_local_relative_hessian_bound hlam hcap a L hp hm
  refine ⟨N,hN,lmax*(C+m),mul_nonneg hlmax.le (add_nonneg hC hm.le),?_⟩
  intro x0 uv huv z c l hl hll hc hNq hbase φ hmono hφ hd hconc H hH hjet d
  let v : Model n → ℝ := fun w => uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)
  let A := fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z
  obtain ⟨q,hq,hq0,hqD,hqlo,hqH⟩ := hjet.exists_smooth_minorant_at (f := fun w => φ (v w)+c w) (x := z) (l := 0) (B := H) (mul_pos hm hl)
  let F : Model n → ℝ := fun w => q w-c w
  have hF : ContDiffAt ℝ 2 F z := hq.sub hc
  have hF0 : F z=φ (v z) := by
    dsimp only [F,v]
    rw [hq0]
    ring
  have hFlo : ∀ᶠ w in 𝓝 z,F w≤φ (v w) := by
    filter_upwards [hqlo] with w hw
    change q w≤φ (v w)+c w at hw
    dsimp only [F]
    linarith only [hw]
  have hFD : fderiv ℝ F z= -fderiv ℝ c z := by
    rw [show F=(fun w => q w-c w) from rfl,
      fderiv_fun_sub (hq.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
      hqD,zero_sub]
  obtain ⟨f,hf,hf0,hflo,hfD,hfH⟩ := scalar_inverse_lower_test (E := Model n) (v := v) (F := F) (x := z) hmono hφ hd hl.ne' hF hF0 hFlo
  have hfD' : fderiv ℝ f z=l⁻¹ • (-fderiv ℝ c z) := by rw [hfD,hFD]
  have Heq (e:Model n) : l*(fderiv ℝ (fderiv ℝ f) z e e+A e e)=
      H e e-(m*l)*‖e‖^2+(l*A e e-fderiv ℝ (fderiv ℝ c) z e e)-
        (iteratedDeriv 2 φ (v z)/l^2)*(fderiv ℝ F z e)^2 := by
    rw [hfH,show F=(fun w => q w-c w) from rfl,second_fderiv_sub hq hc,hqH]
    field_simp [hl.ne']
    ring
  have hscalar (e:Model n) :
      0≤ -(iteratedDeriv 2 φ (v z)/l^2)*(fderiv ℝ F z e)^2 :=
    mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (sq_nonneg l))) (sq_nonneg _)
  have hpos (e:Model n) : m*‖e‖^2≤fderiv ℝ (fderiv ℝ f) z e e+A e e := by
    apply (mul_le_mul_iff_right₀ hl).mp
    rw [Heq]
    have hb := hbase e
    change 2*m*l*‖e‖^2≤l*A e e-fderiv ℝ (fderiv ℝ c) z e e at hb
    nlinarith only [hb,hH e,hscalar e]
  have HB := HC x0 uv huv z f (by rwa [hfD']) hf hf0.symm hflo
    (by simpa only [hfD'] using hpos) d
  rw [hfD'] at HB
  change fderiv ℝ (fderiv ℝ f) z d d+A d d≤C*‖d‖^2 at HB
  have HB' := mul_le_mul_of_nonneg_left HB hl.le
  rw [Heq] at HB'
  have Hb := hbase d
  change 2*m*l*‖d‖^2≤l*A d d-fderiv ℝ (fderiv ℝ c) z d d at Hb
  have Hzero : 0≤2*m*l*‖d‖^2 := by positivity
  have HC' : l*(C+m)*‖d‖^2≤lmax*(C+m)*‖d‖^2 := by
    gcongr
  nlinarith only [HB',Hb,Hzero,hscalar d,HC']

end LocalOuterJetBound
end WeakMTWTransport

end

end

end

end OAI
