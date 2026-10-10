import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothGlobalWeak

namespace OAI

/-! The pointwise Euler equation of a compact radial profile is preserved
by the actual locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialEuler (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  (v:ℂ)^2*deriv (deriv f) v-(v:ℂ)*deriv f v

lemma cubicThetaRadialProfileTerm_equation (W J : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (r : CubicThetaBottomRow) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v=
      lam*cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) W-
        cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) J := by
  have hf : ContDiffAt ℝ 2 (W : ℝ → ℂ) (cubicThetaRowHeightCoordinates r x y v) :=
    hsm.contDiffAt.of_le (by norm_num)
  change cubicThetaHyperbolicOperator
    (fun a b t => star r.phase*W (cubicThetaRowHeightCoordinates r a b t)) x y v=_
  rw [cubicThetaHyperbolicOperator_const_mul,cubicThetaRowHeight_operator r x y hv hf]
  have hh : 0<cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have he : cubicThetaHyperbolicOperator (fun _ _ t => W t) 0 0
      (cubicThetaRowHeightCoordinates r x y v)=
      cubicThetaRadialEuler W (cubicThetaRowHeightCoordinates r x y v) := by
    simp only [cubicThetaHyperbolicOperator,cubicThetaRadialEuler,
      deriv_const',deriv_const,zero_add]
  rw [he,hEq _ hh]
  unfold cubicThetaRadialProfileTerm cubicThetaRowHeightCoordinates
  ring

private lemma radial_coordinate_smooth (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint t y v) W) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x t v) W) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y t) W) v := by
  have hr := cubicThetaRadialProfileTerm_contDiffAt W hsm r (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

lemma cubicThetaRadialProfileFinite_equation (W J : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (S : Finset CubicThetaBottomRow) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v=
      lam*(∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) W)-
        ∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) J := by
  have hcoords := fun r => radial_coordinate_smooth W hsm r x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaRadialProfileTerm_equation W J hsm lam hEq _ x y hv]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]

theorem cubicThetaRadialProfileSeries_equation (W J : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hJ : ∀ v≤(1:ℝ), J v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaRadialProfileSeries (cubicThetaCartesianPoint a b t) W) x y v=
      lam*cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) W-
        cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) J := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hKpos
  have hsum (U : C_c(ℝ,ℂ)) (hU : ∀ v≤(1:ℝ), U v=0) (p) (hp : p∈K) :
      cubicThetaRadialProfileSeries p U=∑ r∈S, cubicThetaRadialProfileTerm r p U := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (hU _ (hS p hp r hr).le)
  have he : (fun p => cubicThetaRadialProfileSeries p W)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaRadialProfileTerm r p W) := by
    filter_upwards [hKn] with p hp
    exact hsum W hW p hp
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  rw [cubicThetaHyperbolicOperator_germ x y v he,
    cubicThetaRadialProfileFinite_equation W J hsm lam hEq S x y hv,
    ←hsum W hW _ hpK,←hsum J hJ _ hpK]

lemma cubicThetaRadialProfile_coordinate_equation (W J : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hJ : ∀ v≤(1:ℝ), J v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm)) p=
      lam*cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm) p-
        cubicThetaSectionFunction (cubicThetaRadialProfileSection J hJ) p := by
  have he : ∀ x y v, 0<v →
      cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm) (cubicThetaCartesianPoint x y v)=
        cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) W := by
    intro x y v hv
    rw [cubicThetaSectionFunction_apply _ hv]
    rfl
  rw [cubicThetaCoordinateLaplacian_hyperbolic,cubicThetaHyperbolicOperator_congr he p.1.re p.1.im hp,
    cubicThetaRadialProfileSeries_equation W J hW hJ hsm lam hEq p.1.re p.1.im hp,
    cubicThetaCartesianPoint_self,cubicThetaSectionFunction_apply _ hp,cubicThetaSectionFunction_apply _ hp]
  rfl

end CubicFirstMoment

end

end OAI
