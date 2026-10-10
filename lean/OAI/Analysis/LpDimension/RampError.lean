import OAI.Analysis.LpDimension.RetractionIntegrals

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

lemma cut_error_bound {E : Type uE} [Fintype E] (P : Matrix E E ℝ) (H a : ℝ)
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hr : ∀ e, matrixRowNorm P e ≤ H)
    (v : E → ℝ) (e : E) :
    |P.mulVec (fun f => cutPart a (v f)) e-cutPart a (v e)| ≤ 2*H*a := by
  have hm := matrix_mulVec_bound P (fun f => cutPart a (v f)) a (fun f => abs_cutPart_le a (v f) ha) e
  have ht := abs_sub (P.mulVec (fun f => cutPart a (v f)) e) (cutPart a (v e))
  have hc := abs_cutPart_le a (v e) ha
  have hh := mul_le_mul_of_nonneg_right (hr e) ha
  nlinarith

lemma ramp_error_bound {E : Type uE} [Fintype E] (P : Matrix E E ℝ) (H : ℝ)
    (hH : 1 ≤ H) (hr : ∀ e, matrixRowNorm P e ≤ H)
    (ℓ : ℕ) (v : E → ℝ) (e : E) :
    |P.mulVec (fun f => dyadicRamp ℓ (v f)) e-dyadicRamp ℓ (v e)| ≤ 2*H*2^(2*ℓ) := by
  have hm := matrix_mulVec_bound P (fun f => dyadicRamp ℓ (v f)) (2^(2*ℓ)) (fun f => abs_dyadicRamp_le ℓ (v f)) e
  have ht := abs_sub (P.mulVec (fun f => dyadicRamp ℓ (v f)) e) (dyadicRamp ℓ (v e))
  have hc := abs_dyadicRamp_le ℓ (v e)
  have hh := mul_le_mul_of_nonneg_right (hr e) (by positivity : (0:ℝ) ≤ 2^(2*ℓ))
  have hpow : (0:ℝ) ≤ 2^(2*ℓ) := by positivity
  have := mul_le_mul_of_nonneg_right hH hpow
  nlinarith

lemma ramp_projection_error (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) [Fintype E]
      (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
      (P : Matrix E E ℝ) (w : E → ℝ) (_hw : ∀ e, 0 ≤ w e) (_hws : ∑ e, w e=1)
      (H B : ℝ) (_hH : 1 ≤ H) (_hB : 0 ≤ B) (ℓ : ℕ),
      (∀ e, matrixRowNorm P e ≤ H) →
      (∀ᵐ v ∂μ, P.mulVec v=v) →
      (∀ k < 2*ℓ, ∀ e, Integrable (fun v => (tailPart ((2:ℝ)^k) (v e))^2) μ) →
      (∀ k < 2*ℓ, ∀ e, (∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) ≤ B*((2:ℝ)^(2-p))^k) →
      (∀ k < 2*ℓ, (∑ e, w e*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)) ≤
        4*B*((2:ℝ)^(2-p))^k) →
      (∑ e, w e*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) ≤
        C*H^(p-2)*(ℓ:ℝ)*B := by
  obtain ⟨C,hC,hdy⟩ := dyadic_interpolation p hp
  refine ⟨20*C*2^(p-2),by positivity,?_⟩
  intro E _ μ _ P w hw hws H B hH _hB ℓ hr hfix htailI htail hPE
  let q : ℝ := (2:ℝ)^(2-p)
  have hq : 0 < q := by dsimp [q]; positivity
  let d : ℕ → E → (E → ℝ) → ℝ := fun k e v =>
    P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)
  let R : E → (E → ℝ) → ℝ := fun e v =>
    P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)
  have hdm (k : ℕ) (e : E) : Measurable (d k e) := by
    dsimp [d,Matrix.mulVec,dotProduct]; fun_prop
  have hdB (k : ℕ) (e : E) (v : E → ℝ) : |d k e v| ≤ 2*H*2^k :=
    cut_error_bound P H _ hH (by positivity) hr v e
  have hdI (k : ℕ) (e : E) : Integrable (fun v => (d k e v)^2) μ := by
    simpa only [Real.rpow_two,sq_abs] using bounded_power_integrable μ (d k e) (hdm k e) 2 (2*H*2^k)
      (by norm_num) (by positivity) (hdB k e)
  have hRm (e : E) : Measurable (R e) := by dsimp [R,Matrix.mulVec,dotProduct]; fun_prop
  have hRI (e : E) : Integrable (fun v => |R e v|^p) μ :=
    bounded_power_integrable μ _ (hRm e) p (2*H*2^(2*ℓ)) (by linarith) (by positivity)
      (fun v => ramp_error_bound P H hH hr ℓ v e)
  have hdE (k : ℕ) (hk : k < 2*ℓ) :
      (∑ e, w e*(∫ v, (d k e v)^2 ∂μ)) ≤ 10*B*q^k := by
    have htL (e : E) : MemLp (fun v : E → ℝ => tailPart ((2:ℝ)^k) (v e)) 2 μ :=
      (memLp_two_iff_integrable_sq (show Measurable (fun v : E → ℝ => tailPart ((2:ℝ)^k) (v e)) by fun_prop).aestronglyMeasurable).mpr (htailI k hk e)
    have hi (e : E) : Integrable (fun v => (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2) μ :=
      (matrix_memLp μ P _ htL e).integrable_sq
    have he (e : E) : (∫ v, (d k e v)^2 ∂μ) ≤
        2*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)+
        2*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_add ((hi e).const_mul 2) ((htailI k hk e).const_mul 2)]
      apply integral_mono_ae (hdI k e) (((hi e).const_mul 2).add ((htailI k hk e).const_mul 2))
      filter_upwards [hfix] with v hv
      dsimp [d]
      rw [cut_error_eq_neg_tail_error P v hv,neg_sq]
      nlinarith [sq_nonneg (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e+tailPart ((2:ℝ)^k) (v e))]
    have hs : (∑ e, w e*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) ≤ B*q^k := by
      calc
        _ ≤ ∑ e, w e*(B*q^k) := Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (htail k hk e) (hw e))
        _ = _ := by rw [← Finset.sum_mul,hws,one_mul]
    calc
      _ ≤ ∑ e, w e*(2*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ)+
        2*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e) (hw e))
      _ = 2*(∑ e, w e*(∫ v, (P.mulVec (fun a => tailPart ((2:ℝ)^k) (v a)) e)^2 ∂μ))+
          2*(∑ e, w e*(∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ)) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      _ ≤ _ := by have hh := hPE k hk; change _ ≤ 4*B*q^k at hh; linarith
  have hpoint (e : E) (v : E → ℝ) : |R e v|^p ≤
      C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) := by
    have hh := hdy (2*ℓ) (2*H) (fun k => |d k e v|) (by positivity)
      (fun k => abs_nonneg _) (fun k _ => hdB k e v)
    have hb := Real.rpow_le_rpow (abs_nonneg _) (ramp_error_le_cut_errors P v ℓ e) (by linarith : 0 ≤ p)
    simpa only [sq_abs] using hb.trans hh
  have heI (e : E) : (∫ v, |R e v|^p ∂μ) ≤
      C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∫ v, (d k e v)^2 ∂μ)) := by
    have hsI : Integrable (fun v => ∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) μ :=
      integrable_finsetSum _ (fun k _ => (hdI k e).const_mul _)
    calc
      _ ≤ ∫ v, C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(d k e v)^2) ∂μ :=
        integral_mono (hRI e) (hsI.const_mul _) (hpoint e)
      _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun k _ => (hdI k e).const_mul _)]
                  simp only [integral_const_mul]
  calc
    _ ≤ ∑ e, w e*(C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∫ v, (d k e v)^2 ∂μ))) :=
      Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (heI e) (hw e))
    _ = C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(∑ e, w e*(∫ v, (d k e v)^2 ∂μ))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ C*(2*H)^(p-2)*(∑ k ∈ Finset.range (2*ℓ), (q^k)⁻¹*(10*B*q^k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hdE k (Finset.mem_range.mp hk)) (by positivity))
    _ = _ := by
      have he (k : ℕ) : (q^k)⁻¹*(10*B*q^k)=10*B := by field_simp
      simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ H)]
      ring

end SubpolynomialLp

end

end OAI
