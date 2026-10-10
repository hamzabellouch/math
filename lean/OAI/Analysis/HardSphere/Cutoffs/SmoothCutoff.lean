import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped Topology

lemma exists_smooth_cutoff (N : ℕ) (L : Length) {K U : Set (Configuration N L)}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ f : SmoothMultiplier N L, Set.EqOn f.toFun 1 K ∧ tsupport f.toFun⊆U := by
  obtain ⟨c,hc0,hc1,_⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hK
    (Set.disjoint_left.mpr (fun X hX hKX ↦ hX (hKU hKX)))
  let C : C(Configuration N L,ℂ) := ⟨fun X ↦ (c X:ℂ),Complex.continuous_ofReal.comp c.continuous⟩
  obtain ⟨g,hg⟩ := (smoothAlgebra_dense N L).denseRange_val.exists_dist_lt C
    (show (0:ℝ)<1/8 by norm_num)
  have hclose (X : Configuration N L) : |(g.val X).re-c X|<1/8 := by
    have he := (ContinuousMap.dist_apply_le_dist (f := g.val) (g := C) X).trans_lt
      (show dist g.val C<1/8 from by rwa [dist_comm])
    have hh := (Complex.abs_re_le_norm (g.val X-C X)).trans_lt
      (show ‖g.val X-C X‖<1/8 from by simpa only [dist_eq_norm] using he)
    simpa only [Complex.sub_re,Complex.ofReal_re,C,ContinuousMap.coe_mk] using hh
  have hgSmooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ g.val (project N L X)) := g.property
  let f : Configuration N L→ℂ := fun X ↦ (Real.smoothTransition (2*(g.val X).re-1/2):ℂ)
  have hs : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration N ↦ f (project N L X)) :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (Complex.reCLM.contDiff.comp hgSmooth)).sub contDiff_const))
  let m : SmoothMultiplier N L := {
    toFun := f
    smooth := hs
    memLp_top := (continuous_of_continuous_lift hs.continuous).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    partial_memLp_top := fun p ↦ (continuous_coordDerivative hs p).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) }
  refine ⟨m,?_,?_⟩
  · intro X hX
    have hx := hclose X
    have hc : c X=1 := hc1 hX
    have hl : 1≤2*(g.val X).re-1/2 := by rw [hc] at hx; linarith [(abs_lt.mp hx).1]
    change (Real.smoothTransition (2*(g.val X).re-1/2):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le hl,Complex.ofReal_one]
  · have hc : tsupport f⊆{X | 1/4≤(g.val X).re} := by
      apply closure_minimal ?_ (isClosed_le continuous_const (Complex.continuous_re.comp g.val.continuous))
      intro X hX
      by_contra h
      change ¬1/4≤(g.val X).re at h
      have hz : f X=0 := by
        dsimp [f]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp h]),Complex.ofReal_zero]
      exact hX hz
    intro X hX
    have hh := hc hX
    change 1/4≤(g.val X).re at hh
    by_contra hn
    have hc : c X=0 := hc0 hn
    have hh' := hclose X
    rw [hc,sub_zero] at hh'
    linarith [(abs_lt.mp hh').2]

end HardSphere

end

end OAI
