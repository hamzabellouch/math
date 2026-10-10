import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingRowEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalOperator

namespace OAI

/-! The full incoming arithmetic series satisfies the exact forced
spectral equation. Every differentiation uses a locally finite row set. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

private lemma incoming_coordinate_smooth (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint t y v) s) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint x t v) s) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y t) s) v := by
  have hr := cubicThetaIncomingTerm_contDiffAt r s (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

lemma cubicThetaIncomingFinite_equation (S : Finset CubicThetaBottomRow)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*(∑ r∈S, cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y v) s)+
        ∑ r∈S, cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s := by
  have hcoords := fun r => incoming_coordinate_smooth r s x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaIncomingTerm_equation _ s x y hv]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  rfl

theorem cubicThetaIncomingEisenstein_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingEisenstein (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_compact_sum hK hKpos
  have he : (fun p => cubicThetaIncomingEisenstein p s)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaIncomingTerm r p s) := by
    filter_upwards [hKn] with p hp
    exact (hS p hp s).1
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  have hg := cubicThetaHyperbolicOperator_germ
    (F:=fun p => cubicThetaIncomingEisenstein p s)
    (G:=fun p => ∑ r∈S, cubicThetaIncomingTerm r p s) x y v he
  have hf := cubicThetaIncomingFinite_equation S s x y hv
  have heq := congrArg₂ (fun u w : ℂ => s*(s-2)*u+w)
    (hS _ hpK s).1.symm (hS _ hpK s).2.symm
  exact hg.trans (hf.trans heq)

end CubicFirstMoment

end

end OAI
