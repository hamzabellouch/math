import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ThreeDeterminantsClose
import OAI.Analysis.BiholderTransport.Regularity.FrameDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameDeterminantClosure
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.frame_determinant_closure (hmtw:WeakMTW (n:=n) (M:=M))
    {μ κ A χ K:ℝ} (hμ:0 < μ) (hκ:0 < κ) (hA:0 < A) (hχ:0 < χ) (hK:0 < K) :
    ∃B:ℝ,0 < B ∧ ∀(ι:Type) [Fintype ι] (a c:M)
      (r:ι → TangentSpace 𝓘(ℝ,Model n) a) (m:ι → ℝ) (q:TangentSpace 𝓘(ℝ,Model n) a),
      (∀j,0 ≤ m j) → (∑j,m j=1) → (∀j,r j∈minimizingVectors a) →
      (∑j,m j • r j=q) → ∀i (e:TangentSpace 𝓘(ℝ,Model n) a) (t D l lo:ℝ),
      μ ≤ m i → ‖e‖=1 → 0 < t → 0 < D → 0 < inner ℝ q e →
      κ*D ≤ (inner ℝ q e)^2 → ‖r i‖^2-‖q‖^2 ≤ A*D → r i=q+t • e →
      l∈Icc (1/2:ℝ) 1 → l<1 → lo∈Icc (1:ℝ) 2 → 1 < lo →
      ∀rc:TangentSpace 𝓘(ℝ,Model n) c,rc∈minimizingVectors c →
      reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ →
      ∀V W X:ℝ,0 < W → 0 < X →
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ ≤ expJacobian c rc*V →
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*W ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
          (expJacobian a (r i))^2 →
      X*V ≤ W → X ≤ B := by
  have hc0:0 < (1/2:ℝ)^n*χ:=mul_pos (by positivity) hχ
  have hC0:0 < (2:ℝ)^n*K:=mul_pos (by positivity) hK
  obtain ⟨B,hB,HB⟩:=hmtw.uniform_three_determinant_closure hμ hκ hA hc0
    (show (0:ℝ)<1 by norm_num) hC0
  refine ⟨B,hB,?_⟩
  intro ι _ a c r m q hmn hmt hr hbar i e t D l lo hmi he ht hD hqe hqD hgap hri
    hl hl1 hlo hlo1 rc hrc hrev V W X hW hX hdc hdo hXdet
  have hl0:0 < l:=lt_of_lt_of_le (by norm_num) hl.1
  have hlo0:0 < lo:=zero_lt_one.trans hlo1
  have hrev':reverseRay (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨c,l • rc⟩:=by
    rw [←hrev,reverseRay_reverseRay]
  have hcontract:=contracted_minimizer_mem_injectivityDomain hrc hl0 hl1
  have hqID:q∈injectivityDomain a:=by
    have H:=reverseRay_injectivityDomain (z:=⟨c,l • rc⟩) hcontract
    rwa [hrev] at H
  have hσ:=expJacobian_pos_of_injectivityDomain hqID
  have hσti:0 < expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
      (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2):=by
    apply expJacobian_pos_of_injectivityDomain
    exact contracted_minimizer_mem_injectivityDomain (reverseRay_minimizing (hr i))
      (inv_pos.mpr hlo0) ((inv_lt_one₀ hlo0).mpr hlo1)
  let f:ℝ:=(chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2
  have hf:0 < f:=sq_pos_of_pos (frameNormDet_pos (mem_extChartAt_target a))
  have hlpow:(1/2:ℝ)^n ≤ l^n:=pow_le_pow_left₀ (by norm_num) hl.1 n
  have hlopow:lo^n ≤ (2:ℝ)^n:=pow_le_pow_left₀ hlo0.le hlo.2 n
  have hσc:0 < expJacobian c rc:=by
    have hp:0 < f*l^n*(expJacobian a q)^2*χ:=by positivity
    have hV:0 < expJacobian c rc*V:=hp.trans_le hdc
    exact lt_of_le_of_ne (expJacobian_nonneg c rc) (by
      intro hzero
      rw [←hzero,zero_mul] at hV
      exact (lt_irrefl (0:ℝ)) hV)
  have hσi:0 < expJacobian a (r i):=by
    have hp:0 < expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
      (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*W:=mul_pos hσti hW
    have H:=hp.trans_le hdo
    exact lt_of_le_of_ne (expJacobian_nonneg a (r i)) (by
      intro hz
      rw [←hz,zero_pow (by decide),mul_zero] at H
      exact (lt_irrefl (0:ℝ)) H)
  have hlow:((1/2:ℝ)^n*χ)*(expJacobian a q)^2/expJacobian c rc ≤ V/f:=by
    apply (div_le_div_iff₀ hσc hf).mpr
    have H:=mul_le_mul_of_nonneg_right hlpow
      (show 0 ≤ f*(expJacobian a q)^2*χ by positivity)
    dsimp only [f] at H
    nlinarith only [H,hdc]
  have hupper:W/f≤((2:ℝ)^n*K)*(expJacobian a (r i))^2/
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2):=by
    apply (div_le_div_iff₀ hf hσti).mpr
    have H:=mul_le_mul_of_nonneg_right hlopow
      (show 0 ≤ f*K*(expJacobian a (r i))^2 by positivity)
    dsimp only [f] at H
    nlinarith only [H,hdo]
  have hratio:(1:ℝ)*X*(V/f)≤W/f:=by
    rw [one_mul,←mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hf).mpr hXdet
  refine HB ι a r m q hmn hmt hr hbar.symm i e t D hmi he ht hD hqe hqD hgap hri l hl lo hlo
    ?_ hσ hσi ?_ hσti (V/f) (W/f) X hX ?_ hupper hratio
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hrc
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hσc
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hlow

end FrameDeterminantClosure
end WeakMTWTransport

end
end

end OAI
