import OAI.Analysis.KLS.Spectral.BrascampLiebPerturbation
import OAI.Analysis.KLS.Spectral.BrascampLiebMoments
import OAI.Analysis.KLS.Convexity.PrekopaReal

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

theorem exp_neg_blPerturbation (V h q : Space n → ℝ) (t : ℝ) (x : Space n) :
    Real.exp (-blPerturbation V h q (t, x)) =
      Real.exp (-V x) * blWeight t (h x) (q x) := by
  rw [blWeight, ← Real.exp_add]
  congr 1
  dsimp [blPerturbation]
  ring

theorem blMoment_potentialMeasure (V h q : Space n → ℝ) (t : ℝ) :
    blMoment (potentialMeasure V) h q t =
      (∫ x, Real.exp (-blPerturbation V h q (t, x))) / potentialPartition V := by
  rw [blMoment, integral_potentialMeasure]
  simp_rw [exp_neg_blPerturbation]

theorem concaveOn_blLogMoment_of_convex {V h q : Space n → ℝ} {B ε : ℝ}
    (hV : Measurable V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) (hε1 : ε ≤ 1)
    (hc : ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
      (blPerturbation V h q)) :
    ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment (potentialMeasure V) h q) := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hint : ∀ t ∈ Ioo (-ε) ε, Integrable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t ht
    have hk : Integrable (fun x => blWeight t (h x) (q x)) (potentialMeasure V) :=
      boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [exp_neg_blPerturbation] using (integrable_potentialMeasure_iff hVint _).mp hk
  have hm : ∀ t ∈ Ioo (-ε) ε, Measurable (fun x => Real.exp (-blPerturbation V h q (t, x))) := by
    intro t _
    dsimp [blPerturbation]
    fun_prop
  have hp := concaveOn_log_integral_exp_neg (convex_Ioo (-ε) ε) (blPerturbation V h q) hc hm hint
  refine (hp.add_const (-Real.log (potentialPartition V))).congr ?_
  intro t ht
  rw [blLogMoment, blMoment_potentialMeasure,
    Real.log_div (integral_exp_pos (hint t ht)).ne' (potentialPartition_pos hVint).ne']
  simp only [Pi.add_apply]
  ring

theorem brascamp_lieb {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hpos : ∀ x, (hessianMatrix V x).PosDef) (hh : IsTestFunction h) :
    variance (potentialMeasure V) h ≤
      ∫ x, steinGamma V h h x ∂potentialMeasure V := by
  let : IsProbabilityMeasure (potentialMeasure V) := isProbabilityMeasure_potentialMeasure hVint
  have hq := contDiff_steinGamma_self hV hh.1 hpos
  have hqc := hasCompactSupport_steinGamma_self V hh
  have hqint : Integrable (steinGamma V h h) (potentialMeasure V) :=
    hq.continuous.integrable_of_hasCompactSupport hqc
  obtain ⟨Bh, hBh⟩ := hh.2.exists_bound_of_continuous hh.continuous
  obtain ⟨Bq, hBq⟩ := hqc.exists_bound_of_continuous hq.continuous
  apply le_of_forall_pos_le_add
  intro δ hδ
  let B : ℝ := max Bh (Bq + |δ|)
  have hhB : ∀ x, |h x| ≤ B := by
    intro x
    have hb : |h x| ≤ Bh := by simpa only [Real.norm_eq_abs] using hBh x
    exact hb.trans (le_max_left _ _)
  have hqB : ∀ x, |steinGamma V h h x + δ| ≤ B := by
    intro x
    calc
      |steinGamma V h h x + δ| ≤ |steinGamma V h h x| + |δ| := abs_add_le _ _
      _ ≤ Bq + |δ| := by
        have hb : |steinGamma V h h x| ≤ Bq := by simpa only [Real.norm_eq_abs] using hBq x
        linarith
      _ ≤ B := le_max_right _ _
  obtain ⟨ε, hε, hε1, hc⟩ := exists_blPerturbation_convex hV hh hpos hδ
  have hqm : Measurable (fun x => steinGamma V h h x + δ) :=
    (hq.continuous.add continuous_const).measurable
  have hlog := concaveOn_blLogMoment_of_convex hV.continuous.measurable hVint
    hh.continuous.measurable hqm hhB hqB hε1 hc
  have hb := variance_le_integral_of_concave_blLogMoment (potentialMeasure V)
    hh.continuous.measurable hqm hhB hqB hε hε1 hlog
  calc
    variance (potentialMeasure V) h ≤
        ∫ x, (steinGamma V h h x + δ) ∂potentialMeasure V := hb
    _ = (∫ x, steinGamma V h h x ∂potentialMeasure V) + δ := by
      rw [integral_add hqint (integrable_const δ)]
      simp

theorem brascamp_lieb_normalized {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hVint : Integrable (fun x => Real.exp (-V x)))
    (hpos : ∀ x, (hessianMatrix V x).PosDef)
    (hZ : potentialPartition V = 1) (hh : IsTestFunction h) :
    variance (densityMeasure (fun x => Real.exp (-V x))) h ≤
      ∫ x, steinGamma V h h x ∂densityMeasure (fun x => Real.exp (-V x)) := by
  rw [← potentialMeasure_of_normalized hZ]
  exact brascamp_lieb hV hVint hpos hh

end LeanBlast.KLS

end

end OAI
