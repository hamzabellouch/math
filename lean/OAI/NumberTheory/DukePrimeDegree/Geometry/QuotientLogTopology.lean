import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogDistance

namespace OAI

/-! # Separation and continuity of logarithmic quotient distance -/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_rightOrbit (n : ℕ) (x : X n) : Continuous (fun g : G n => rightAction x g) := by
  induction x using Quotient.inductionOn with
  | h a =>
      change Continuous (fun g : G n => Quotient.mk _ (a*g))
      exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

theorem quotientLogDistance_eq_zero_iff {n : ℕ} (x y : X n) :
    quotientLogDistance x y=0 ↔ x=y := by
  constructor
  · intro hzero
    choose g hg hlen using fun k : ℕ => exists_rightAction_length_lt x y
      (show 0 < (1:ℝ)/((k:ℝ)+1) by positivity)
    have hlength : Tendsto (fun k => matrixLogLength (g k)) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => matrixLogLength_nonneg _)
        (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [hzero,zero_add] using (hlen k).le
    have hgroup := tendsto_one_of_matrixLogLength_tendsto_zero g hlength
    have horbit := (continuous_rightOrbit n x).continuousAt.tendsto.comp hgroup
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 x) := by
      simpa only [Function.comp_def,hg,rightAction_one] using horbit
    exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm
  · rintro rfl
    exact quotientLogDistance_self x

theorem continuous_quotientLogDistance (n : ℕ) (x : X n) :
    Continuous (quotientLogDistance x) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  intro g
  have hlen : Tendsto (fun h : G n => matrixLogLength (g⁻¹*h)) (𝓝 g) (𝓝 0) := by
    have H := ((continuous_matrixLogLength n).comp
      ((continuous_const : Continuous (fun _ : G n => g⁻¹)).mul continuous_id)).tendsto g
    simpa only [Function.comp_def,Pi.mul_apply,id_eq,inv_mul_cancel,matrixLogLength_one] using H
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlen.eventually (gt_mem_nhds hε)] with h hh
  have H := quotientLogDistance_right_bound x (Quotient.mk _ g) (g⁻¹*h)
  have he : rightAction (Quotient.mk _ g) (g⁻¹*h)=Quotient.mk _ h := by
    change Quotient.mk _ (g*(g⁻¹*h))=Quotient.mk _ h
    simp
  rw [he] at H
  change |quotientLogDistance x (Quotient.mk _ h)-quotientLogDistance x (Quotient.mk _ g)| < ε
  exact H.trans_lt hh

end DukePrimeDegree

end

end OAI
