import OAI.Geometry.Relativity.CKS.TailEnergy

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma compactified_radial_source (j q : ℕ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hδR : 1/δ ≤ R) (θ : Angle) {F : ℝ → ℝ}
    (hF : ∀ s ∈ Icc 0 δ, ContDiffAt ℝ ∞ F s) :
    SourceRemainderOn j q (angularRadialTail R (Metric.ball θ 1))
      (fun y => F ((y 0)⁻¹) / (y 0)^q) := by
  let K : Set Point := (fun p : ℝ × Angle => slice p.1 p.2) '' (Icc 0 δ ×ˢ Metric.closedBall θ 1)
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall θ 1)).image (by apply continuous_pi; intro i; fin_cases i <;> simp [slice,injection] <;> fun_prop)
  have hFc : ∀ z ∈ K, ContDiffAt ℝ ∞ (fun z : Point => F (z 0)) z := by
    rintro z ⟨p,hp,rfl⟩
    have hh : ContDiffAt ℝ ∞ F (slice p.1 p.2 0) := by simpa [slice] using hF p.1 hp.1
    exact hh.comp (slice p.1 p.2)
      (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).contDiff.contDiffAt
  have h := FiniteLogDecay.weighted_compactified j (q : ℝ) hK hFc
  have he (x : Point) : radiusPower (-(q:ℝ)) x * F ((inverseLogRadiusChart x) 0) =
      F ((logRadiusChart x 0)⁻¹) / (logRadiusChart x 0)^q := by
    rw [radiusPower_neg_nat]
    simp only [inverseLogRadiusChart,logRadiusChart,ite_true,Real.exp_neg]
    ring
  have h' : FiniteLogDecay j (q : ℝ) (inverseLogRadiusChart ⁻¹' K)
      (fun x => F ((logRadiusChart x 0)⁻¹) / (logRadiusChart x 0)^q) :=
    h.congr (funext he)
  apply h'.source_of_log.mono
  intro y hy
  have hr : 0 < y 0 := lt_trans hR hy.1
  refine ⟨radialLogChart y,?_,logRadiusChart_radialLogChart hr⟩
  have hinv : (y 0)⁻¹ ≤ δ := by
    have hh : 1/δ < y 0 := lt_of_le_of_lt hδR hy.1
    exact (inv_le_comm₀ hr hδ).mpr (by simpa using hh.le)
  refine ⟨((y 0)⁻¹,angularProjection y),⟨⟨inv_nonneg.mpr hr.le,hinv⟩,Metric.mem_closedBall.mpr
    (Metric.mem_ball.mp hy.2).le⟩,?_⟩
  ext i
  cases i using Fin.cases <;> simp [slice,inverseLogRadiusChart,radialLogChart,
    angularProjection,Real.exp_neg,Real.exp_log hr]

lemma source_zero (j q : ℕ) (R : ℝ) (θ : Angle) (hR : 0 < R) :
    SourceRemainderOn j q (angularRadialTail R (Metric.ball θ 1)) (fun _ => 0) := by
  simpa only [zero_div] using compactified_radial_source j q (δ := 1/R)
    (one_div_pos.mpr hR) hR (by simp) θ (F := fun _ => 0) (fun _ _ => contDiffAt_const)

end CKSSchwarzschild

end

end OAI
