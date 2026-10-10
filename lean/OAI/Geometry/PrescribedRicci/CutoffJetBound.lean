import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransport
import OAI.Geometry.PrescribedRicci.JetTrim

namespace OAI

/-! Cutoff Jet Bound. -/

section

 
noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical ENNReal
namespace GlobalElliptic
open SobolevChart TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι κ Z : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

lemma initialJet_zero_bound (e : ι → E) (F : κ → 𝓢(E,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h0 : ∀ a x, ‖F a x‖ ≤ B)
    (h1 : ∀ a i x, ‖fderiv ℝ (F a) x (e i)‖ ≤ B) :
    familyJetNorm e (realComponents (initialJet e (fun a x => F a x))) 0 ∞ ≤ B := by
  obtain ⟨⟨⟨a,i⟩,b⟩,ha⟩ := familyJetNorm_attained e (realComponents (initialJet e (fun a x => F a x))) 0 ∞
  rw [ha]
  obtain ⟨w,hw⟩ := jetNorm_attained e (realComponents (initialJet e (fun a x => F a x)) ((a,i),b)) 0 ∞
  rw [hw]
  have hh (x : E) : ‖initialJet e (fun a x => F a x) (a,i) x‖ ≤ B := by
    cases i with
    | none => exact h0 a x
    | some i => exact h1 a i x
  have hmeas := (realComponents_smooth (initialJet e (fun a x => F a x))
    (initialJet_smooth e _ (fun a => (F a).smooth')) ((a,i),b)).continuous.aestronglyMeasurable (μ:=volume)
  change lpNorm (realComponents (initialJet e (fun a x => F a x)) ((a,i),b)) ∞ volume ≤ B
  rw [← toReal_eLpNorm,eLpNorm_exponent_top hmeas]
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound ?_)).trans_eq
    (ENNReal.toReal_ofReal hB)
  filter_upwards [] with x
  change ‖if b then (initialJet e (fun a x => F a x) (a,i) x).im else
    (initialJet e (fun a x => F a x) (a,i) x).re‖ ≤ B
  cases b
  · exact (Complex.abs_re_le_norm _).trans (hh x)
  · exact (Complex.abs_im_le_norm _).trans (hh x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nonempty ι] in
lemma ChartCutoff.uniform_C1 {U : Set E} (σ : ChartCutoff U) (hU : IsOpen U)
    (e : ι → E) (f : Z → E → ℂ) (hs : ∀ z, ContDiffOn ℝ ∞ (f z) U)
    {M P : ℝ} (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hm : ∀ z x, x ∈ tsupport (σ : E → ℂ) → ‖f z x‖ ≤ M)
    (hp : ∀ z x, x ∈ tsupport (σ : E → ℂ) → ∀ i, ‖fderiv ℝ (f z) x (e i)‖ ≤ P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, (∀ x, ‖σ.product hU (hs z) x‖ ≤ B) ∧
      (∀ i x, ‖fderiv ℝ (σ.product hU (hs z)) x (e i)‖ ≤ B) := by
  let K := ‖σ.val.toBoundedContinuousFunction‖
  let Q := ∑ i, ‖(∂_{e i} σ.val).toBoundedContinuousFunction‖
  have hK : 0 ≤ K := norm_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ K*M+(Q*M+K*P) := add_nonneg (mul_nonneg hK hM)
    (add_nonneg (mul_nonneg hQ hM) (mul_nonneg hK hP))
  refine ⟨K*M+(Q*M+K*P),hB,fun z => ⟨?_,?_⟩⟩
  · intro x
    by_cases hx : x ∈ tsupport (σ : E → ℂ)
    · rw [ChartCutoff.product_apply,norm_mul]
      have h := mul_le_mul (σ.val.toBoundedContinuousFunction.norm_coe_le_norm x) (hm z x hx)
        (norm_nonneg _) hK
      change ‖σ x‖*‖f z x‖ ≤ K*M at h
      nlinarith only [h,mul_nonneg hQ hM,mul_nonneg hK hP]
    · rw [ChartCutoff.product_apply,image_eq_zero_of_notMem_tsupport hx,zero_mul,norm_zero]
      exact hB
  · intro i x
    by_cases hx : x ∈ tsupport (σ : E → ℂ)
    · have hf := ((hs z).contDiffAt (hU.mem_nhds (σ.support_sub hx))).differentiableAt (by simp)
      have he : fderiv ℝ (σ.product hU (hs z)) x (e i) =
          σ x * fderiv ℝ (f z) x (e i) + fderiv ℝ σ.val x (e i) * f z x := by
        change fderiv ℝ (fun y => σ.val y * f z y) x (e i) = _
        rw [fderiv_fun_mul (σ.val.differentiableAt) hf]
        simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
        ring
      rw [he]
      have hq : ‖fderiv ℝ σ.val x (e i)‖ ≤ Q := by
        have hh := (∂_{e i} σ.val).toBoundedContinuousFunction.norm_coe_le_norm x
        change ‖(∂_{e i} σ.val) x‖ ≤ _ at hh
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv] at hh
        exact hh.trans (Finset.single_le_sum (fun j _ => norm_nonneg (∂_{e j} σ.val).toBoundedContinuousFunction) (Finset.mem_univ i))
      have hk : ‖σ x‖ ≤ K := σ.val.toBoundedContinuousFunction.norm_coe_le_norm x
      have hsum : ‖σ x * fderiv ℝ (f z) x (e i) + fderiv ℝ σ.val x (e i) * f z x‖ ≤ K*P+Q*M := by
        apply (norm_add_le _ _).trans
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hk (hp z x hx i) (norm_nonneg _) hK)
          (mul_le_mul hq (hm z x hx) (norm_nonneg _) hQ)
      exact hsum.trans (by nlinarith only [mul_nonneg hK hM])
    · have he : (σ.product hU (hs z) : E → ℂ) =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp only [ChartCutoff.product_apply]; rw [hy]; simp
      rw [he.fderiv_eq]
      simpa using hB
end GlobalElliptic

end
end

end OAI
