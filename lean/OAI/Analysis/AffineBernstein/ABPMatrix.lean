import Mathlib
import OAI.Analysis.AffineBernstein.DetBarrierPhase

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ABPMatrix

lemma det_le_det_mul_mixed_trace_pow {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosSemidef) :
    B.det ≤ A.det * ((A⁻¹ * B).trace)^n := by
  obtain ⟨C,hC,hCd,hCt⟩ := exists_normalized_posSemidef hA hB
  have hh := posSemidef_det_le_trace_pow hC
  rw [hCd,hCt] at hh
  have he := (div_le_iff₀ hA.det_pos).mp hh
  simpa only [mul_comm] using he

lemma hessian_det_le_of_linearized_bound {n : ℕ} {u f : Space n → ℝ}
    {x : Space n} (hu : (hessian u x).PosDef) (hf : (hessian f x).PosSemidef)
    {K : ℝ} (_ : 0 ≤ K) (hL : inverseHessianTrace u f x ≤ K) :
    (hessian f x).det ≤ (hessian u x).det * K^n := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
  have ht : ((hessian u x)⁻¹ * hessian f x).trace = inverseHessianTrace u f x := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,inverseHessianTrace]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs.apply i j]
  have hh := det_le_det_mul_mixed_trace_pow hu hf
  rw [ht] at hh
  have hn : 0 ≤ inverseHessianTrace u f x := by
    rw [← ht]
    exact trace_mul_posSemidef_nonneg hu.posSemidef.inv hf
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hL n) hu.det_pos.le)

end ABPMatrix

open Filter
open scoped Topology

lemma hessian_posSemidef_of_localMin {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMin f x) : (hessian f x).PosSemidef := by
  have hh := hessian_neg_posSemidef_of_localMax hf.neg hm.neg
  simpa only [hessian_neg,neg_neg] using hh

/-- The elementary supporting-plane step of ABP, without convex-envelope axioms. -/
lemma abp_gradient_coverage {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (Space n)} (hK : IsCompact K) {a : Space n} (ha : a ∈ K)
    {m R : ℝ} (hm : 0 < m) (hR : 0 < R)
    (hKR : K ⊆ Metric.closedBall a R) (hfa : f a ≤ -m)
    (hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x) :
    ∀ p ∈ Metric.ball (0 : Space n) (m/(2*R)),
      ∃ x ∈ interior K, f x < 0 ∧ (hessian f x).PosSemidef ∧ gradient f x = p := by
  intro p hp
  have hpN : ‖p‖ * R < m/2 := by
    rw [Metric.mem_ball,dist_zero_right] at hp
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*R)).mp hp
    nlinarith
  let g := graphAffineFunction f (-innerSL ℝ p) 1 (inner ℝ p a)
  have hg : ContDiff ℝ ∞ g :=
    ((-innerSL ℝ p).contDiff.add (contDiff_const.mul hf)).add contDiff_const
  have hge (x : Space n) : g x = f x - inner ℝ p (x-a) := by
    simp only [g,graphAffineFunction,neg_apply,innerSL_apply_apply,
      one_mul,inner_sub_right]
    ring
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn ⟨a,ha⟩ hg.continuous.continuousOn
  have hxR : ‖x-a‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hKR hx
  have hip : inner ℝ p (x-a) < m/2 :=
    (real_inner_le_norm _ _).trans_lt ((mul_le_mul_of_nonneg_left hxR (norm_nonneg p)).trans_lt hpN)
  have hlow : f x < 0 := by
    have ht : g x ≤ g a := hmin ha
    rw [hge,hge] at ht
    simp only [sub_self,inner_zero_right,sub_zero] at ht
    linarith
  have hxi : x ∈ interior K := by
    by_contra H
    exact (not_lt_of_ge (hb x hx H)) hlow
  have hl : IsLocalMin g x :=
    hmin.isLocalMin (mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset)
  have hhe : hessian g x = hessian f x := by
    ext i j
    simpa only [g,one_mul] using hessian_graphAffineFunction isOpen_univ hf.contDiffOn
      (mem_univ x) (-innerSL ℝ p) 1 (inner ℝ p a) i j
  refine ⟨x,hxi,hlow,?_,?_⟩
  · rw [← hhe]
    exact hessian_posSemidef_of_localMin hg.contDiffAt hl
  · apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left]
    have hdz : dirDeriv v g x = 0 := by rw [dirDeriv,hl.fderiv_eq_zero]; rfl
    rw [dirDeriv_graphAffineFunction (hf.differentiable (by simp) x)] at hdz
    simp only [neg_apply,innerSL_apply_apply,one_mul] at hdz
    change fderiv ℝ f x v = inner ℝ p v
    change -inner ℝ p v + fderiv ℝ f x v = 0 at hdz
    linarith

/-- A closed set large enough to contain every lower supporting point. -/
def abpContactSet {n : ℕ} (K : Set (Space n)) (f : Space n → ℝ) : Set (Space n) :=
  {x | x ∈ K ∧ f x ≤ 0 ∧ ∀ v : Space n, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v}

lemma isCompact_abpContactSet {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) : IsCompact (abpContactSet K f) := by
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  apply hK.of_isClosed_subset _ (fun _ hx => hx.1)
  have hc : IsClosed {x | ∀ v : Space n, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v} := by
    simpa only [ofPred_forall] using
      (isClosed_iInter fun v : Space n => isClosed_le (continuous_const (y := (0:ℝ)))
        ((hf2.clm_apply (continuous_const (y := v))).clm_apply (continuous_const (y := v))))
  exact hK.isClosed.inter ((isClosed_le hf.continuous continuous_const).inter hc)

lemma abpContactSet_hessian {n : ℕ} {K : Set (Space n)} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) {x : Space n} (hx : x ∈ abpContactSet K f) :
    (hessian f x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (hessian_isSymm hf.contDiffAt)
  intro p
  let v : Space n := (WithLp.equiv 2 (Fin n → ℝ)).symm p
  have hh := hx.2.2 v
  rw [second_fderiv_eq_sum hf.contDiffAt] at hh
  simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,v] using hh

/-- The measure-theoretic ABP estimate uses the genuine gradient Jacobian.
No injectivity of the gradient or convexity of the tested function is assumed. -/
theorem abp_contact_measure {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (Space n)} (hK : IsCompact K) {a : Space n} (ha : a ∈ K)
    {m R D : ℝ} (hm : 0 < m) (hR : 0 < R)
    (hKR : K ⊆ Metric.closedBall a R) (hfa : f a ≤ -m)
    (hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    (hdet : ∀ x ∈ abpContactSet K f, (hessian f x).det ≤ D) :
    volume (Metric.ball (0 : Space n) (m/(2*R))) ≤
      ENNReal.ofReal D * volume (abpContactSet K f) := by
  let C := abpContactSet K f
  have hC := isCompact_abpContactSet hK hf
  have hg : Metric.ball (0 : Space n) (m/(2*R)) ⊆ gradient f '' C := by
    intro p hp
    obtain ⟨x,hxi,hfx,hpx,hgx⟩ := abp_gradient_coverage hf hK ha hm hR hKR hfa hb p hp
    refine ⟨x,⟨interior_subset hxi,hfx.le,?_⟩,hgx⟩
    intro v
    exact second_fderiv_nonneg hf.contDiffAt hpx v
  calc
    _ ≤ volume (gradient f '' C) := measure_mono hg
    _ ≤ ∫⁻ x in C, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hC.measurableSet
        (fun _ _ => ((contDiffAt_gradient hf.contDiffAt).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _x in C, ENNReal.ofReal D := by
      apply setLIntegral_mono' hC.measurableSet
      intro x hx
      rw [det_fderiv_gradient_eq_hessian hf.contDiffAt,
        abs_of_nonneg (abpContactSet_hessian hf hx).det_nonneg]
      exact ENNReal.ofReal_le_ofReal (hdet x hx)
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,C]

end AffineBernstein

end

end OAI
