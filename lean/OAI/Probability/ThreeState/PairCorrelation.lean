import Mathlib
import OAI.Probability.ThreeState.PosteriorMoments

namespace OAI

/-! Two-message correlation and quantitative entropy increments. -/

namespace ThreeState
open Set

lemma log_correlation_cubic (a : ℝ) (ha : 0 < a) :
    (a-1)+(a-1)^2/2-(a-1)^3/6 ≤ a*Real.log a := by
  let f : ℝ → ℝ := fun x => x*Real.log x-((x-1)+(x-1)^2/2-(x-1)^3/6)
  let g : ℝ → ℝ := fun x => Real.log x-(x-1)+(x-1)^2/2
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt f (g x) x := by
    have hh := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).sub
      ((((hasDerivAt_id x).sub_const 1).add (((hasDerivAt_id x).sub_const 1).pow 2 |>.div_const 2)).sub
        (((hasDerivAt_id x).sub_const 1).pow 3 |>.div_const 6))
    convert hh using 1 <;> first | rfl | (dsimp only [g, id]; field_simp; ring)
  have hdg (x : ℝ) (hx : 0 < x) : HasDerivAt g ((x-1)^2/x) x := by
    have hh := ((Real.hasDerivAt_log hx.ne').sub ((hasDerivAt_id x).sub_const 1)).add
      (((hasDerivAt_id x).sub_const 1).pow 2 |>.div_const 2)
    convert hh using 1 <;> first | rfl | (simp only [id_eq]; field_simp; ring)
  have hconv : ConvexOn ℝ (Ioi 0) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g) (f'' := fun x => (x-1)^2/x) (convex_Ioi 0)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hdg x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact div_nonneg (sq_nonneg _) hx.le
  have hf1 : f 1 = 0 := by simp [f]
  have hg1 : g 1 = 0 := by simp [g]
  have hf0 : 0 ≤ f a := by
    rcases lt_trichotomy a 1 with hl | he | hg
    · have hh := hconv.slope_le_of_hasDerivAt ha (by norm_num : (1:ℝ) ∈ Ioi 0) hl (hd 1 (by norm_num))
      rw [hg1, slope_def_field, hf1] at hh
      have hp := (div_le_iff₀ (sub_pos.mpr hl)).mp hh
      linarith
    · simp [he, hf1]
    · have hh := hconv.le_slope_of_hasDerivAt (by norm_num : (1:ℝ) ∈ Ioi 0) ha hg (hd 1 (by norm_num))
      rw [hg1, slope_def_field, hf1] at hh
      have hp := (le_div_iff₀ (sub_pos.mpr hg)).mp hh
      linarith
  dsimp only [f] at hf0
  linarith

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def correlationZ (a b : Message) : ℝ := avg (fun i => messageDeviation a i * messageDeviation b i)
lemma continuous_correlationZ : Continuous (fun p : Message × Message => correlationZ p.1 p.2) := by
  apply continuous_avg
  intro i
  exact ((((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).sub continuous_const).mul
    ((((continuous_apply i).comp continuous_subtype_val).comp continuous_snd).sub continuous_const)

noncomputable def symPerm : Fin 6 → Equiv.Perm Spin :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]
noncomputable def symAvg (f : Message → ℝ) (m : Message) : ℝ :=
  (∑ i : Fin 6, f (permMessage (symPerm i) m))/6

lemma integral_symAvg (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q)
    (f : Message → ℝ) (hf : Continuous f) :
    (∫ m, symAvg f m ∂(Q : Measure Message)) = ∫ m, f m ∂(Q : Measure Message) := by
  simp only [symAvg, integral_div]
  have hi (i : Fin 6) : Integrable (fun m => f (permMessage (symPerm i) m)) (Q : Measure Message) :=
    integrable_continuous_message Q (hf.comp (continuous_permMessage _))
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_permMessage Q hs _ _ hf.measurable]
  simp

lemma symAvg_correlationZ (a b : Message) : symAvg (fun m => correlationZ m b) a = 0 := by
  have ha := average_message a
  have hb := average_message b
  simp only [Radial.avg_expand] at ha hb
  have ha2 : a 2 = 3-a 0-a 1 := by linarith
  have hb2 : b 2 = 3-b 0-b 1 := by linarith
  norm_num [symAvg, symPerm, Fin.sum_univ_succ, correlationZ, messageDeviation,
    Radial.avg_expand, permMessage, Equiv.swap_apply_def, Equiv.trans_apply, Equiv.symm_trans_apply, Fin.ext_iff]
  rw [ha2, hb2]
  ring

lemma symAvg_correlationZ_sq (a b : Message) :
    symAvg (fun m => (correlationZ m b)^2) a = 2*messageX a*messageX b := by
  have ha := average_message a
  have hb := average_message b
  simp only [Radial.avg_expand] at ha hb
  have ha2 : a 2 = 3-a 0-a 1 := by linarith
  have hb2 : b 2 = 3-b 0-b 1 := by linarith
  norm_num [symAvg, symPerm, Fin.sum_univ_succ, correlationZ, messageDeviation,
    Radial.avg_expand, permMessage, Equiv.swap_apply_def, Equiv.trans_apply, Equiv.symm_trans_apply, Fin.ext_iff,
    messageX, Radial.momentX]
  rw [ha2, hb2]
  ring

lemma symAvg_correlationZ_cube (a b : Message) :
    symAvg (fun m => (correlationZ m b)^3) a = 2*messageY a*messageY b := by
  have ha := average_message a
  have hb := average_message b
  simp only [Radial.avg_expand] at ha hb
  have ha2 : a 2 = 3-a 0-a 1 := by linarith
  have hb2 : b 2 = 3-b 0-b 1 := by linarith
  norm_num [symAvg, symPerm, Fin.sum_univ_succ, correlationZ, messageDeviation,
    Radial.avg_expand, permMessage, Equiv.swap_apply_def, Equiv.trans_apply, Equiv.symm_trans_apply, Fin.ext_iff,
    messageY, Radial.momentY]
  rw [ha2, hb2]
  ring

lemma integral_correlationZ (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q) (b : Message) :
    (∫ m, correlationZ m b ∂(Q : Measure Message)) = 0 := by
  rw [← integral_symAvg Q hs (fun m => correlationZ m b) (continuous_correlationZ.comp (continuous_id.prodMk continuous_const))]
  simp only [symAvg_correlationZ, integral_zero]

lemma integral_correlationZ_sq (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q) (b : Message) :
    (∫ m, (correlationZ m b)^2 ∂(Q : Measure Message)) = 2*posteriorMu Q*messageX b := by
  rw [← integral_symAvg Q hs (fun m => (correlationZ m b)^2) ((continuous_correlationZ.comp (continuous_id.prodMk continuous_const)).pow 2)]
  simp only [symAvg_correlationZ_sq, integral_mul_const, integral_const_mul, posteriorMu]

lemma integral_correlationZ_cube (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q) (b : Message) :
    (∫ m, (correlationZ m b)^3 ∂(Q : Measure Message)) = 2*posteriorEta Q*messageY b := by
  rw [← integral_symAvg Q hs (fun m => (correlationZ m b)^3) ((continuous_correlationZ.comp (continuous_id.prodMk continuous_const)).pow 3)]
  simp only [symAvg_correlationZ_cube, integral_mul_const, integral_const_mul, posteriorEta]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma correlationZ_comm (a b : Message) : correlationZ a b = correlationZ b a := by
  simp [correlationZ, mul_comm]

noncomputable def pairNormalizer (lam : ℝ) (h : Admissible lam) (a b : Message) : ℝ :=
  avg (fun i => a i*edgeMessage lam h b i)

lemma pairNormalizer_eq (lam : ℝ) (h : Admissible lam) (a b : Message) :
    pairNormalizer lam h a b = 1+lam*correlationZ a b := by
  have ha := average_message a
  have hb := average_message b
  simp only [Radial.avg_expand] at ha hb
  simp only [pairNormalizer, correlationZ, messageDeviation, edgeMessage, Radial.avg_expand]
  rw [message_last a, message_last b]
  ring

lemma continuous_pairNormalizer (lam : ℝ) (h : Admissible lam) :
    Continuous (fun p : Message × Message => pairNormalizer lam h p.1 p.2) := by
  simp only [pairNormalizer_eq]
  exact continuous_const.add (continuous_const.mul continuous_correlationZ)

lemma pairNormalizer_pos (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (a b : Message) : 0 < pairNormalizer lam h a b := by
  have he (i : Spin) : (1-lam)*a i ≤ a i*edgeMessage lam h b i := by
    nlinarith [mul_le_mul_of_nonneg_left (edgeMessage_bounds lam h hl0 b i).1 (Message.nonneg a i)]
  have ha := average_message a
  simp only [pairNormalizer, Radial.avg_expand] at *
  nlinarith [he 0, he 1, he 2]

noncomputable def pairMessage (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (a b : Message) : Message :=
  ⟨fun i => a i*edgeMessage lam h b i/pairNormalizer lam h a b, by
    constructor
    · intro i
      exact div_nonneg (mul_nonneg (Message.nonneg a i) (Message.nonneg _ _)) (pairNormalizer_pos lam h hl0 hl1 a b).le
    · rw [← Finset.sum_div]
      change (∑ i, a i*edgeMessage lam h b i)/((∑ i, a i*edgeMessage lam h b i)/3) = 3
      have hh := ne_of_gt (pairNormalizer_pos lam h hl0 hl1 a b)
      dsimp only [pairNormalizer, avg] at hh
      have hs : (∑ i, a i*edgeMessage lam h b i) ≠ 0 := by
        intro he
        apply hh
        rw [he]
        norm_num
      field_simp [hs]⟩

lemma continuous_pairMessage (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun p : Message × Message => pairMessage lam h hl0 hl1 p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).mul
    (((continuous_apply i).comp continuous_subtype_val).comp ((continuous_edgeMessage lam h).comp continuous_snd))).div
      (continuous_pairNormalizer lam h) (fun p => ne_of_gt (pairNormalizer_pos lam h hl0 hl1 p.1 p.2))

lemma integral_pairNormalizer (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (a : Message) :
    (∫ b, pairNormalizer lam h a b ∂(Q : Measure Message)) = 1 := by
  change (∫ b, avg (fun i => a i*edgeMessage lam h b i) ∂(Q : Measure Message)) = 1
  rw [integral_avg]
  · simp only [integral_const_mul, integral_edgeMessage lam h Q hQ, mul_one]
    exact average_message a
  · intro i
    exact integrable_continuous_message Q (continuous_const.mul (((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)))

noncomputable def pairIncrement (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (a : Message) : ℝ :=
  ∫ b, pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b) ∂(Q : Measure Message)

lemma continuous_pairIntegrand (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun p : Message × Message => pairNormalizer lam h p.1 p.2*Real.log (pairNormalizer lam h p.1 p.2)) :=
  (continuous_pairNormalizer lam h).mul ((continuous_pairNormalizer lam h).log
    (fun p => ne_of_gt (pairNormalizer_pos lam h hl0 hl1 p.1 p.2)))

lemma pairIncrement_nonneg (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (a : Message) : 0 ≤ pairIncrement lam h Q a := by
  have hf : Continuous (fun b => pairNormalizer lam h a b) :=
    (continuous_pairNormalizer lam h).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous (fun b => pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b)) :=
    (continuous_pairIntegrand lam h hl0 hl1).comp (continuous_const.prodMk continuous_id)
  have hin (b : Message) : pairNormalizer lam h a b-1 ≤ pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b) := by
    have hp := pairNormalizer_pos lam h hl0 hl1 a b
    have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne'] at hh
    exact hh
  have hif : Integrable (fun b => pairNormalizer lam h a b-1) (Q : Measure Message) :=
    integrable_continuous_message Q (hf.sub continuous_const)
  have hh := integral_mono hif (integrable_continuous_message Q hg) hin
  rw [integral_sub (integrable_continuous_message Q hf) (integrable_const 1), integral_pairNormalizer lam h Q hQ] at hh
  simpa [pairIncrement] using hh

lemma pairIncrement_lower (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hs : SpinSymmetric Q) (a : Message) :
    lam^2*posteriorMu Q*messageX a-lam^3*posteriorEta Q*messageY a/3 ≤ pairIncrement lam h Q a := by
  let z : Message → ℝ := fun b => correlationZ b a
  have hz : Continuous z := continuous_correlationZ.comp (continuous_id.prodMk continuous_const)
  have h1 : (∫ b, z b ∂(Q : Measure Message)) = 0 := integral_correlationZ Q hs a
  have h2 : (∫ b, (z b)^2 ∂(Q : Measure Message)) = 2*posteriorMu Q*messageX a := integral_correlationZ_sq Q hs a
  have h3 : (∫ b, (z b)^3 ∂(Q : Measure Message)) = 2*posteriorEta Q*messageY a := integral_correlationZ_cube Q hs a
  have hin (b : Message) : lam*z b+lam^2*(z b)^2/2-lam^3*(z b)^3/6 ≤ pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b) := by
    have hh := log_correlation_cubic _ (pairNormalizer_pos lam h hl0 hl1 a b)
    rw [pairNormalizer_eq, correlationZ_comm a b] at hh ⊢
    dsimp only [z]
    convert hh using 1
    ring
  have hf : Continuous (fun b => lam*z b+lam^2*(z b)^2/2-lam^3*(z b)^3/6) := by fun_prop
  have hg : Continuous (fun b => pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b)) :=
    (continuous_pairIntegrand lam h hl0 hl1).comp (continuous_const.prodMk continuous_id)
  have hh := integral_mono (integrable_continuous_message Q hf) (integrable_continuous_message Q hg) hin
  have hi1 := integrable_continuous_message Q hz
  have hi2 : Integrable (fun b => (z b)^2) (Q : Measure Message) := integrable_continuous_message Q (hz.pow 2)
  have hi3 : Integrable (fun b => (z b)^3) (Q : Measure Message) := integrable_continuous_message Q (hz.pow 3)
  have hiadd : Integrable (fun b => lam*z b+lam^2*(z b)^2/2) (Q : Measure Message) :=
    (hi1.const_mul _).add ((hi2.const_mul _).div_const _)
  rw [integral_sub hiadd ((hi3.const_mul _).div_const _), integral_add (hi1.const_mul _) ((hi2.const_mul _).div_const _),
    integral_div, integral_div, integral_const_mul, integral_const_mul, integral_const_mul, h1,h2,h3] at hh
  dsimp only [pairIncrement]
  linarith

end ThreeState

end OAI
