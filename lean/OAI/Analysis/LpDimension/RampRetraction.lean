import OAI.Analysis.LpDimension.RampError

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uI uV

namespace SubpolynomialLp

def aboveVariance (p : ℝ) : ℝ := (p/(p-2))/(1-(2:ℝ)^((2-p)/2))^2

lemma aboveVariance_pos (p : ℝ) (hp : 2 < p) : 0 < aboveVariance p := by
  have hs : (2:ℝ)^((2-p)/2) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  dsimp [aboveVariance]
  positivity

lemma dyadic_tail_power (p : ℝ) (k : ℕ) : ((2:ℝ)^k)^(2-p) = ((2:ℝ)^(2-p))^k := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm]

lemma ramp_retraction (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) (V : Type uV) (I : Type uI) [Fintype E] [Fintype V] [Fintype I]
      [DecidableEq E] [DecidableEq V] [Nonempty E] [Nonempty I]
      (src dst : E → V) (δ w : E → ℝ) (_hδ : ∀ e, 0 < δ e)
      (_hw : ∀ e, 0 < w e) (_hws : ∑ e, w e=1)
      (_hcard : 2 ≤ Fintype.card V)
      (_hinc : ∀ i : V, ∃ e, src e=i ∨ dst e=i)
      (_hconn : ∀ i j : V, i ≠ j → ∃ e,
        (src e=i ∧ dst e=j) ∨ (src e=j ∧ dst e=i))
      (g : I → E → ℝ) (_hg : ∀ e, ∑ i, |g i e|^p=1)
      (_hgr : ∀ i, ∃ x, (normalizedGradient src dst δ).mulVec x=g i)
      (ℓ : ℕ),
      let μ := paretoVectorLaw p g
      let H := 4*Real.log (Fintype.card V : ℝ)
      let N := (Fintype.card I : ℝ)
      let u := fun v : E → ℝ => fun e => dyadicRamp ℓ (v e)
      ∃ P ∈ retractions (normalizedGradient src dst δ),
        (∀ e, matrixRowNorm P e ≤ H) ∧
        (∑ e, w e*(∫ v, |P.mulVec (u v) e-u v e|^p ∂μ)) ≤ C*H^(p-2)*(ℓ:ℝ)/N ∧
        (∑ e, w e*(∫ v, (P.mulVec (u v) e)^2 ∂μ)) ≤ 4*aboveVariance p/N ∧
        (∀ e, (∫ v, (P.mulVec (u v) e)^2 ∂μ) ≤ H^2*aboveVariance p/N) := by
  obtain ⟨C,hC,hError⟩ := ramp_projection_error p hp
  refine ⟨C*(p/(p-2)),by positivity,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  dsimp only
  let μ := paretoVectorLaw p g
  let H := 4*Real.log (Fintype.card V : ℝ)
  let N := (Fintype.card I : ℝ)
  let u := fun v : E → ℝ => fun e => dyadicRamp ℓ (v e)
  let U := aboveVariance p
  let T := p/(p-2)
  let q : ℝ := (2:ℝ)^(2-p)
  have hU : 0 < U := aboveVariance_pos p hp
  have hT : 0 < T := by dsimp [T]; positivity
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 1 ≤ H := by
    have ht := log_nat_lower (Fintype.card V) hcard
    dsimp [H]; linarith
  let := paretoVectorLaw_probability p (by linarith) g
  let f : Option (Fin (2*ℓ)) → E → (E → ℝ) → ℝ := fun j e v =>
    match j with
    | none => dyadicRamp ℓ (v e)
    | some k => tailPart ((2:ℝ)^k.val) (v e)
  let B : Option (Fin (2*ℓ)) → ℝ := fun j =>
    match j with
    | none => U/N
    | some k => (T/N)*q^k.val
  have hB (j : Option (Fin (2*ℓ))) : 0 < B j := by cases j <;> dsimp [B] <;> positivity
  have hf (j : Option (Fin (2*ℓ))) (e : E) : MemLp (f j e) 2 μ := by
    cases j with
    | none =>
      apply (memLp_two_iff_integrable_sq (show Measurable (f none e) by dsimp [f]; fun_prop).aestronglyMeasurable).mpr
      simpa only [f,Real.rpow_two,sq_abs] using paretoVectorLaw_ramp_integrable p 2 (by linarith) (by norm_num) g ℓ e
    | some k =>
      exact (memLp_two_iff_integrable_sq (show Measurable (f (some k) e) by dsimp [f]; fun_prop).aestronglyMeasurable).mpr
        (paretoVectorLaw_tail_integrable p ((2:ℝ)^k.val) hp g hg e)
  have hbound (j : Option (Fin (2*ℓ))) (e : E) : (∫ v, (f j e v)^2 ∂μ) ≤ B j := by
    cases j with
    | none =>
      have he := paretoVectorLaw_ramp_moment p 2 (by linarith) (by norm_num) g hg ℓ e
      simp only [Real.rpow_two,sq_abs] at he
      dsimp [f,B]
      rw [he]
      exact div_le_div_of_nonneg_right (pareto_dyadicRamp_variance p hp ℓ) hN.le
    | some k =>
      dsimp [f,B,μ,T,N,q]
      rw [paretoVectorLaw_tail_moment p _ hp (one_le_pow₀ (by norm_num)) g hg e,dyadic_tail_power]
      exact le_of_eq (by ring)
  obtain ⟨P,hP,hr,hPE⟩ := controlled_retraction_integrals μ src dst δ w hδ hw hws hcard hinc hconn f hf B hB hbound
  have hraw (k : ℕ) (e : E) : (∫ v, (tailPart ((2:ℝ)^k) (v e))^2 ∂μ) = (T/N)*q^k := by
    rw [paretoVectorLaw_tail_moment p _ hp (one_le_pow₀ (by norm_num)) g hg e,dyadic_tail_power]
    dsimp [T,N,q]; ring
  refine ⟨P,hP,hr,?_,?_,?_⟩
  · have hfix : ∀ᵐ v ∂μ, P.mulVec v=v := by
      filter_upwards [paretoVectorLaw_range p g (normalizedGradient src dst δ) hgr] with v hv
      exact retraction_fixes _ P hP v hv
    have hh := hError E μ P w (fun e => (hw e).le) hws H (T/N) hH (by positivity) ℓ hr hfix
      (fun k _ e => paretoVectorLaw_tail_integrable p ((2:ℝ)^k) hp g hg e)
      (fun k _ e => (hraw k e).le)
      (fun k hk => by simpa only [f,B,q,mul_assoc] using hPE (some ⟨k,hk⟩))
    convert hh using 1
    dsimp [T,N,H]
    ring
  · simpa only [f,B,mul_div_assoc] using hPE none
  · intro e
    have hh := matrix_integral_sq_bound μ P (f none) (hf none) (U/N) (by positivity) (hbound none) e
    have hr0 := matrixRowNorm_nonneg P e
    have hr2 := (sq_le_sq₀ hr0 (by linarith : 0 ≤ H)).mpr (hr e)
    have hmul := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ U/N)
    exact hh.trans (by simpa only [mul_div_assoc] using hmul)

end SubpolynomialLp

end

end OAI
