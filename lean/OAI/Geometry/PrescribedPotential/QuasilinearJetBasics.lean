import Mathlib
import OAI.Geometry.PrescribedPotential.FrozenEllipticJets
import OAI.Geometry.PrescribedPotential.HigherJetCommutator

namespace OAI

/-! Quasilinear Jet Basics. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def firstJet (u : E → F) (x : E) : F × (E →L[ℝ] F) := (u x,fderiv ℝ u x)
lemma firstJet_smoothOn {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (firstJet u) U :=
  hu.prodMk (hu.fderiv_of_isOpen hU (m := ∞) (by simp))
lemma firstJet_smoothAt {u : E → F} {x : E} (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (firstJet u) x := hu.prodMk (hu.fderiv_right (m := ∞) (by simp))
lemma norm_firstJet_deriv {u : E → F} {x : E} (hu : ContDiffAt ℝ ∞ u x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (firstJet u) x‖ =
      max ‖iteratedFDeriv ℝ m u x‖ ‖iteratedFDeriv ℝ (m+1) u x‖ := by
  change ‖iteratedFDeriv ℝ m (fun y => (u y,fderiv ℝ u y)) x‖ = _
  rw [iteratedFDeriv_prodMk hu (hu.fderiv_right (m := ∞) (by simp))
    (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top),
    ContinuousMultilinearMap.opNorm_prod,norm_iteratedFDeriv_fderiv]
lemma composition_first_jet_bound {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) :
    ‖iteratedFDeriv ℝ 1 (g ∘ f) x‖ ≤
      ‖iteratedFDeriv ℝ 1 g (f x)‖*‖iteratedFDeriv ℝ 1 f x‖ := by
  simp only [norm_iteratedFDeriv_one]
  rw [fderiv_comp x (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp))]
  exact ContinuousLinearMap.opNorm_comp_le _ _

 

lemma compact_coefficient_jets {K : Set F} (hK : IsCompact K) {a : F → G}
    (ha : ∀ y ∈ K, ContDiffAt ℝ ∞ a y) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j, j ≤ m → ∀ y ∈ K, ‖iteratedFDeriv ℝ j a y‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ j a y‖ ≤ C := by
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (fun y hy =>
      ((ha y hy).iteratedFDeriv_right (m := ∞) (i := j)
        (by exact WithTop.coe_le_coe.mpr le_top)).continuousAt.continuousWithinAt)
    exact ⟨max C 0,le_max_right _ _,fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC hb using hb
  refine ⟨1+∑ j ∈ range (m+1), C j,le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hC j)),?_⟩
  intro j hj y hy
  exact (hb j y hy).trans ((Finset.single_le_sum (fun i _ => hC i)
    (mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one))

end HigherJet
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma norm_hessian_deriv (u : E → F) (x : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (hessian u) x‖ = ‖iteratedFDeriv ℝ (m+2) u x‖ := by
  simp only [hessian,norm_iteratedFDeriv_fderiv]

local instance hessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance hessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

lemma frozen_first_bound (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u : E → F} {a : E → G}
    (hu : ContDiffOn ℝ ∞ u U) (ha : ContDiffOn ℝ ∞ a U) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ 1 (fun y => B (a y-a x) (hessian u y)) x‖ ≤
      ‖B‖*‖iteratedFDeriv ℝ 1 a x‖*‖iteratedFDeriv ℝ 2 u x‖ := by
  have h := frozen_product_jet_bound B hU ha (hessian_smoothOn hU hu) hx 1
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,ite_true,one_mul,zero_mul,zero_add,ite_false,
    Nat.reduceSub,norm_hessian_deriv,Nat.reduceAdd,show ¬ (1 : ℕ) = 0 from by decide,mul_assoc] using h

lemma frozen_second_bound (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u : E → F} {a : E → G}
    (hu : ContDiffOn ℝ ∞ u U) (ha : ContDiffOn ℝ ∞ a U) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ 2 (fun y => B (a y-a x) (hessian u y)) x‖ ≤
      ‖B‖*(2*‖iteratedFDeriv ℝ 1 a x‖*‖iteratedFDeriv ℝ 3 u x‖+
        ‖iteratedFDeriv ℝ 2 a x‖*‖iteratedFDeriv ℝ 2 u x‖) := by
  have h := frozen_product_jet_bound B hU ha (hessian_smoothOn hU hu) hx 2
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,ite_true,one_mul,zero_mul,zero_add,ite_false,
    Nat.reduceSub,norm_hessian_deriv,not_false_eq_true,Nat.cast_one,Nat.cast_ofNat] at h
  exact h
end HigherJet

end
end

end OAI
