import Mathlib
import OAI.Analysis.AffineBernstein.AffineCapLIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual graph conormal expressed in an arbitrary fixed target space. -/
def targetGraphConormal {n : ℕ} (u : Space n → ℝ)
    (L : G ≃L[ℝ] (Space n × ℝ)) (x : Space n) : G →L[ℝ] ℝ :=
  ((ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)).comp L.toContinuousLinearMap

lemma targetGraphConormal_norm_le {n : ℕ} (u : Space n → ℝ)
    (L T : G ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    ‖targetGraphConormal u L x‖ ≤
      (‖T.toContinuousLinearMap‖+1)*‖affineGraphConormal u (L.symm.trans T) x‖ := by
  have he : targetGraphConormal u L x =
      (affineGraphConormal u (L.symm.trans T) x).comp T.toContinuousLinearMap := by
    ext z
    simp [targetGraphConormal,affineGraphConormal]
  rw [he]
  calc
    _ ≤ ‖affineGraphConormal u (L.symm.trans T) x‖ * ‖T.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖T.toContinuousLinearMap‖+1)*‖affineGraphConormal u (L.symm.trans T) x‖ := by
      nlinarith [norm_nonneg (affineGraphConormal u (L.symm.trans T) x)]

/-- The uniform cap producer in a fixed normed target. Choosing target coordinates costs
only constants depending on those fixed coordinates, never on the varying affine map.
The nonnegative integral is the exact original inverse second form with actual conormal norm. -/
theorem affineMaximal_uniform_target_cap_lintegral_bound (n : ℕ)
    (T : G ≃L[ℝ] (Space n × ℝ))
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : G ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L.symm ((o,c)-v)) r ⊆
        (fun p => L.symm (p-v)) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ‖L.symm ((x,u x)-v)‖ ≤ R) →
      ENNReal.ofReal (Real.rpow |(L.symm.trans T).toContinuousLinearMap.det|
        ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C := by
  let D := ‖T.toContinuousLinearMap‖+1
  let E := ‖T.symm.toContinuousLinearMap‖+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨C,hC,hcap⟩ := affineMaximal_uniform_affine_cap_lintegral_bound n hε
    (div_pos hr hE) (mul_nonneg hD.le hR) t₀ t₁ q₀
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR
  let M := L.symm.trans T
  let w := -T (L.symm v)
  have he (p : Space n × ℝ) : M p+w = T (L.symm (p-v)) := by
    simp [M,w,ContinuousLinearEquiv.trans_apply,sub_eq_add_neg]
  have hball' : Metric.closedBall (M (o,c)+w) (r/E) ⊆
      (fun p => M p+w) '' sourceEpigraph Ω u := by
    intro z hz
    have hdist : dist (T.symm z) (L.symm ((o,c)-v)) ≤ r := by
      have hz' : ‖z-T (L.symm ((o,c)-v))‖ ≤ r/E := by
        simpa only [Metric.mem_closedBall,dist_eq_norm,he] using hz
      calc
        _ = ‖T.symm (z-T (L.symm ((o,c)-v)))‖ := by
          simp only [map_sub,T.symm_apply_apply,dist_eq_norm]
        _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖z-T (L.symm ((o,c)-v))‖ :=
          T.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ E*(r/E) := mul_le_mul (by dsimp [E]; linarith) hz' (norm_nonneg _) hE.le
        _ = r := mul_div_cancel₀ r hE.ne'
    obtain ⟨p,hp,hep⟩ := hball hdist
    refine ⟨p,hp,?_⟩
    change M p+w = z
    rw [he,(show L.symm (p-v) = T.symm z from hep),T.apply_symm_apply]
  have hxR' (x : Space n) (hx : x ∈ K) : ‖M (x,u x)+w‖ ≤ D*R := by
    rw [he]
    exact (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul (by dsimp [D]; linarith) (hxR x hx) (norm_nonneg _) hD.le)
  have hbnd := hcap hΩ hcv hu hp hm M w o c a b d hball' hq₀ hK hKΩ hQ hQK hs hqK hqQ
    (fun x hx j => (le_trans (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (p := (2:ℝ≥0∞)) ((M (x,u x)+w).1) j))
      ((norm_fst_le _).trans (hxR' x hx))))
    (fun x hx => by simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans (hxR' x hx))
  have hlin : (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
      (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤
      ENNReal.ofReal D * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
        (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' hQ
    intro x hx
    rw [← ENNReal.ofReal_mul hD.le]
    apply ENNReal.ofReal_le_ofReal
    have hA : 0 ≤ affineAreaDensity u x := Real.rpow_nonneg (hp x (hKΩ (hQK hx))).det_pos.le _
    have hV := graphInverseMetric_nonneg (hp x (hKΩ (hQK hx))) a b d
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (targetGraphConormal_norm_le u L T x) hV) hA
    change _ ≤ D * _
    nlinarith only [hh]
  calc
    _ ≤ ENNReal.ofReal (Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))) *
        (ENNReal.ofReal D * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x)))) := mul_le_mul_right hlin _
    _ = ENNReal.ofReal D * (ENNReal.ofReal (Real.rpow |M.toContinuousLinearMap.det|
        ((n:ℝ)/((n:ℝ)+2))) * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x)))) := by ac_rfl
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal C := mul_le_mul_right hbnd _
    _ = ENNReal.ofReal (D*C) := (ENNReal.ofReal_mul hD.le).symm

end AffineBernstein
end

end OAI
