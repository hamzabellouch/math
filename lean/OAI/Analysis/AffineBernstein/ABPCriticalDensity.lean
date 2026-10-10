import Mathlib
import OAI.Analysis.AffineBernstein.TangentShiftCalculus
import OAI.Analysis.AffineBernstein.ABPMatrix

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ABPCriticalDensity

/-- Critical density for a positive supersolution of the actual linearized
Monge--Ampère operator. The touching paraboloid is replaced by the genuine
convex tangent section, so no ellipticity-ratio bound is presupposed. -/
theorem linearizedMA_critical_density {n : ℕ} {u s : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, (hessian u x).PosDef)
    {a : Space n} {h ε R D : ℝ} (hh : 0 < h) (hε : 0 < ε) (hR : 0 < R)
    (hD : 0 ≤ D)
    (hK : IsCompact {x | tangentHeight u a x ≤ h})
    (hKR : {x | tangentHeight u a x ≤ h} ⊆ Metric.closedBall a R)
    (hspos : ∀ x, 0 ≤ s x) (hsa : s a ≤ ε)
    (hLs : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hdet : ∀ x, tangentHeight u a x ≤ h → (hessian u x).det ≤ D) :
    volume (Metric.ball (0 : Space n) (1/(2*R))) ≤
      ENNReal.ofReal (D * (2*(n:ℝ)/h)^n) *
        volume {x | tangentHeight u a x ≤ h ∧ s x ≤ 2*ε} := by
  let K : Set (Space n) := {x | tangentHeight u a x ≤ h}
  let q := tangentShift u a h
  let f : Space n → ℝ := fun x => ε⁻¹ * s x + (2/h)*q x
  have hq : ContDiff ℝ ∞ q :=
    contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn a h)
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul hs).add (contDiff_const.mul hq)
  have ha : a ∈ K := by simp only [K,mem_ofPred_eq,tangentHeight,sub_self,map_zero]; linarith
  have hfa : f a ≤ -(1:ℝ) := by
    have he : q a = -h := by simp [q,tangentShift,tangentHeight]
    dsimp only [f]
    rw [he]
    have hdiv := (div_le_one hε).mpr hsa
    rw [div_eq_mul_inv,mul_comm] at hdiv
    have hht : (2/h)*(-h) = -(2:ℝ) := by field_simp [hh.ne']
    rw [hht]
    linarith
  have hboundary (x : Space n) (hx : x ∈ K) (hxi : x ∉ interior K) : q x = 0 := by
    have hle : tangentHeight u a x ≤ h := hx
    have he : tangentHeight u a x = h := by
      by_contra H
      have hlt : tangentHeight u a x < h := lt_of_le_of_ne hle H
      have hcont : Continuous (tangentHeight u a) := by
        exact ((hu.continuous.sub continuous_const).sub
          ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)))
      have hopen : IsOpen {y | tangentHeight u a y < h} := isOpen_lt hcont continuous_const
      have hi : {y | tangentHeight u a y < h} ⊆ interior K :=
        interior_maximal (fun y hy => (show tangentHeight u a y ≤ h from le_of_lt hy)) hopen
      exact hxi (hi hlt)
    simp only [q,tangentShift,he,sub_self]
  have hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x := by
    intro x hx hxi
    simp only [f,hboundary x hx hxi,mul_zero,add_zero]
    exact mul_nonneg (inv_nonneg.mpr hε.le) (hspos x)
  have hL (x : Space n) : inverseHessianTrace u f x ≤ 2*(n:ℝ)/h := by
    rw [show f = (fun y => ε⁻¹*s y+(2/h)*q y) from rfl,
      inverseHessianTrace_add isOpen_univ (contDiffOn_const.mul hs.contDiffOn)
        (contDiffOn_const.mul hq.contDiffOn) (mem_univ x),
      inverseHessianTrace_const_mul isOpen_univ hs.contDiffOn (mem_univ x),
      inverseHessianTrace_const_mul isOpen_univ hq.contDiffOn (mem_univ x)]
    have he : inverseHessianTrace u q x = (n:ℝ) := by
      change (∑ i,∑ j, (hessian u x)⁻¹ i j * hessian q x i j) = _
      rw [show hessian q x = hessian u x from hessian_tangentShift isOpen_univ hu.contDiffOn a h (mem_univ x)]
      exact inverseHessianTrace_self (hp x)
    rw [he]
    have hn := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε.le) (hLs x)
    have ht : (2/h)*(n:ℝ) = 2*(n:ℝ)/h := by ring
    rw [ht]
    linarith
  have hd (x : Space n) (hx : x ∈ abpContactSet K f) :
      (hessian f x).det ≤ D*(2*(n:ℝ)/h)^n := by
    have ht := hessian_det_le_of_linearized_bound (hp x) (abpContactSet_hessian hf hx)
      (by positivity : 0 ≤ 2*(n:ℝ)/h) (hL x)
    exact ht.trans (mul_le_mul (hdet x hx.1) le_rfl (by positivity) hD)
  have haB := abp_contact_measure hf hK ha zero_lt_one hR hKR hfa hb hd
  have hlow : abpContactSet K f ⊆ {x | tangentHeight u a x ≤ h ∧ s x ≤ 2*ε} := by
    intro x hx
    refine ⟨hx.1,?_⟩
    have hqnonneg := tangentHeight_nonneg isOpen_univ convex_univ hu.contDiffOn
      (fun y hy => hp y) (mem_univ a) (mem_univ x)
    have hxF : ε⁻¹*s x+(2/h)*(tangentHeight u a x-h) ≤ 0 := hx.2.1
    have htwo : (2/h)*h = (2:ℝ) := by field_simp [hh.ne']
    have hn : 0 ≤ (2/h)*tangentHeight u a x := mul_nonneg (by positivity) hqnonneg
    rw [mul_sub,htwo] at hxF
    have hr : s x/ε ≤ 2 := by rw [div_eq_mul_inv,mul_comm]; linarith
    exact (div_le_iff₀ hε).mp hr
  exact haB.trans (mul_le_mul_right (measure_mono (μ := volume) hlow) _)

end ABPCriticalDensity



end
end AffineBernstein
end

end OAI
