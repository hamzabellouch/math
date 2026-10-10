import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalModelAlgebra

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalMiddleSize (j V W : ℝ) (p : ScalarPoint) : ℝ :=
  (1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)*W+
    2*(|j*sqrt (scalarQMoment p.1/scalarS j p)| * (sqrt (scalarS j p)*V)+
      |j*scalarA j p/scalarS j p|)+
    |2*j*(scalarA j p+j*scalarBMoment p.1*scalarQMoment p.1)/(scalarS j p+j*scalarQMoment p.1)|+
    |j| * V^2+|2*j*scalarQMoment p.1|+|j*scalarBMoment p.1|

lemma continuousAt_conditionalMiddleSize {X : Type*} [TopologicalSpace X]
    {R : ℝ} (hR : 0 ≤ R) (j V W : ℝ) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) {x : X}
    (hs : scalarS j (f x) ≠ 0) (hS : scalarS j (f x)+j*scalarQMoment (f x).1 ≠ 0) :
    ContinuousAt (fun x=>conditionalMiddleSize j V W (f x)) x := by
  have hq := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hb := (continuous_scalarBMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hss := ((continuous_scalarS j).comp hf).continuousAt (x := x)
  have hSS : ContinuousAt (fun x=>scalarS j (f x)+j*scalarQMoment (f x).1) x := hss.add (continuousAt_const.mul hq)
  have ha := ((continuousOn_scalarA hR j).comp_continuous hf hdom).continuousAt (x := x)
  have hn : ContinuousAt (fun x=>(f x).2.1+(f x).2.2^2) x := by fun_prop
  have hk : ContinuousAt (fun x=>conditionalKappa j (f x)) x := (hn.div hss hs).sqrt
  have hl : ContinuousAt (fun x=>conditionalEll j (f x)) x := (hn.div hSS hS).sqrt
  unfold conditionalMiddleSize
  fun_prop (disch := assumption)

theorem conditionalMiddleSize_uniform {j R t0 T : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    (ht0 : 0 < t0) (V W : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (P : ProbabilityMeasure ℝ), P ∈ momentBall R →
      ∀ t ∈ Icc t0 T,∀ σ : ℝ, |σ| ≤ 1 → conditionalMiddleSize j V W (P,t,σ) ≤ L := by
  let X : Type := ↥(momentBall R) × ↥(Icc t0 T) × ↥(Icc (-1:ℝ) 1)
  let : CompactSpace (momentBall R) := isCompact_iff_compactSpace.mp (isCompact_momentBall R)
  let f : X → ScalarPoint := fun x=>((x.1:ProbabilityMeasure ℝ),(x.2.1:ℝ),(x.2.2:ℝ))
  have hf : Continuous f := by dsimp [f,X]; fun_prop
  have hdom : ∀ x,f x ∈ scalarMomentDomain R := fun (x : X)=>⟨x.1.2,mem_univ _⟩
  have hc : Continuous (fun x : X=>conditionalMiddleSize j V W (f x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have ht : 0 < (x.2.1:ℝ) := ht0.trans_le x.2.1.2.1
    have hs : 0 < scalarS j (f x) := by
      dsimp [scalarS,f]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ht (sq_nonneg _))
        (mul_nonneg hj (scalarQMoment_bounds _).1)
    have hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1 :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg hj (scalarQMoment_bounds _).1)
    exact continuousAt_conditionalMiddleSize hR j V W f hf hdom hs.ne' hS.ne'
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro P hP t ht σ hσ
  let x : X := (⟨P,hP⟩,⟨t,ht⟩,⟨σ,abs_le.mp hσ⟩)
  exact (hM (mem_image_of_mem _ (mem_univ x))).trans (le_max_right _ _)

lemma empirical_column_coefficient {n : ℕ} [NeZero n] {j t0 t T σ : ℝ}
    (hj : 0 ≤ j) (ht0 : 0 < t0) (ht : t ∈ Icc t0 T) (y : Fin n → ℝ) :
    (1+|scalarD j (empiricalLaw y,t,σ)|)/scalarS j (empiricalLaw y,t,σ) ≤
      max 1 ((1+|T|+j)/t0) := by
  have ht' : 0 < t := ht0.trans_le ht.1
  have hd : |scalarD j (empiricalLaw y,t,σ)| ≤ |T|+j := by
    apply (abs_add_le _ _).trans
    rw [abs_of_pos ht',abs_mul,abs_of_nonneg hj]
    have hh := mul_le_mul_of_nonneg_left (scalarM_bounds (empiricalLaw y)) hj
    have hT := ht.2.trans (le_abs_self T)
    nlinarith only [hh,hT]
  have hs : t0 ≤ scalarS j (empiricalLaw y,t,σ) := by
    dsimp [scalarS]
    exact ht.1.trans (le_add_of_nonneg_right (sq_nonneg σ) |>.trans
      (le_add_of_nonneg_right (mul_nonneg hj (scalarQMoment_bounds _).1)))
  apply le_trans _ (le_max_right _ _)
  exact div_le_div₀ (by positivity) (by linarith) ht0 hs
end SKGap
end
end

end OAI
