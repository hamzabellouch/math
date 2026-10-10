import Mathlib
import OAI.Analysis.AffineBernstein.CapCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
def sourceEpigraph {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Set (Space n × ℝ) :=
  {p | p.1 ∈ Ω ∧ u p.1 ≤ p.2}

def triangularLinearHeight {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) : Space n →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp
    (M.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ))

@[simp] lemma triangularLinearHeight_apply {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    triangularLinearHeight M x = (M (x,0)).2 := rfl

def triangularGraphFunction {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) : Space n → ℝ :=
  let B := (triangularBaseEquiv M hc hcn).symm
  let a := (triangularLinearHeight M).comp B.toContinuousLinearMap
  cleGraphPullback u B (-B v.1) a c (v.2-a v.1)

lemma triangularGraphFunction_eval {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) (y : Space n) :
    triangularGraphFunction u M hc hcn v y =
      triangularLinearHeight M ((triangularBaseEquiv M hc hcn).symm (y-v.1)) +
        c*u ((triangularBaseEquiv M hc hcn).symm (y-v.1))+v.2 := by
  simp only [triangularGraphFunction,cleGraphPullback,sub_eq_add_neg,map_add,map_neg,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  ring

lemma triangularGraphFunction_image {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) (p : Space n × ℝ) :
    triangularGraphFunction u M hc hcn v (M p+v).1 =
      triangularLinearHeight M p.1+c*u p.1+v.2 := by
  rw [triangularGraphFunction_eval]
  have he : (triangularBaseEquiv M hc hcn).symm ((M p+v).1-v.1) = p.1 := by
    change (triangularBaseEquiv M hc hcn).symm ((M p).1+v.1-v.1) = _
    rw [add_sub_cancel_right,triangular_fst M hc]
    exact (triangularBaseEquiv M hc hcn).symm_apply_apply p.1
  rw [he]

lemma triangularGraph_regular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    let Ω' := {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
    let g := triangularGraphFunction u M hc hcp.ne' v
    IsOpen Ω' ∧ ContDiffOn ℝ ∞ g Ω' ∧
      (∀ y ∈ Ω', (hessian g y).PosDef) ∧ AffineMaximalOn Ω' g := by
  dsimp only
  unfold triangularGraphFunction
  simpa only [map_sub,sub_eq_add_neg,map_add,map_neg] using
    cleGraphPullback_regular hΩ hu hp hm (triangularBaseEquiv M hc hcp.ne').symm
      (-((triangularBaseEquiv M hc hcp.ne').symm v.1))
      ((triangularLinearHeight M).comp (triangularBaseEquiv M hc hcp.ne').symm.toContinuousLinearMap)
      hcp (v.2-((triangularLinearHeight M).comp
        (triangularBaseEquiv M hc hcp.ne').symm.toContinuousLinearMap) v.1)

/-- The affine image is literally the epigraph of the derived graph; no new
solution or geometric stationary surrogate is assumed. -/
lemma triangular_sourceEpigraph_image {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    (fun p => M p+v) '' sourceEpigraph Ω u =
      sourceEpigraph {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
        (triangularGraphFunction u M hc hcp.ne' v) := by
  have hi (p : Space n × ℝ) :
      (M p+v ∈ sourceEpigraph
        {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
        (triangularGraphFunction u M hc hcp.ne' v)) ↔ p ∈ sourceEpigraph Ω u := by
    have he : (triangularBaseEquiv M hc hcp.ne').symm ((M p+v).1-v.1) = p.1 := by
      change (triangularBaseEquiv M hc hcp.ne').symm ((M p).1+v.1-v.1) = _
      rw [add_sub_cancel_right,triangular_fst M hc]
      exact (triangularBaseEquiv M hc hcp.ne').symm_apply_apply p.1
    change (_ ∈ Ω ∧ _ ≤ (M p+v).2) ↔ (p.1 ∈ Ω ∧ u p.1 ≤ p.2)
    rw [he,triangularGraphFunction_image]
    have hs := triangular_snd M hc p.1 p.2
    change (p.1 ∈ Ω ∧ triangularLinearHeight M p.1+c*u p.1+v.2 ≤ (M p).2+v.2) ↔ _
    rw [hs,triangularLinearHeight_apply,add_le_add_iff_right,add_le_add_iff_left,
      mul_le_mul_iff_right₀ hcp]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hi p).mpr hp
  · intro hz
    refine ⟨M.symm (z-v),?_,by simp⟩
    exact (hi _).mp (by simpa using hz)

end AffineBernstein
end

end OAI
