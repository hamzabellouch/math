import Mathlib
import OAI.Geometry.PrescribedPotential.DirectionalJetEnergy
import OAI.Geometry.PrescribedPotential.QuasilinearJetBasics
import OAI.Geometry.PrescribedPotential.QuasilinearResidualAlgebra
import OAI.Geometry.PrescribedPotential.SecondJetComposition

namespace OAI

/-! Quasilinear Low Residuals. -/

section

 

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
local instance lowHessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance lowHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

lemma norm_iteratedFDeriv_add_le {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y+g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖+‖iteratedFDeriv ℝ m g x‖ := by
  change ‖iteratedFDeriv ℝ m (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.of_le (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hg.of_le (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))]
  exact norm_add_le _ _

lemma low_coefficient_bounds {u : E → F} {a : F → G} {b : F × (E →L[ℝ] F) → F} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (ha : ContDiffAt ℝ ∞ a (u x))
    (hb : ContDiffAt ℝ ∞ b (firstJet u x)) {C : ℝ} (hC : 0 ≤ C)
    (hP : (Fintype.card (OrderedFinpartition 2) : ℝ) ≤ C)
    (hu1 : ‖iteratedFDeriv ℝ 1 u x‖ ≤ C)
    (haj : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j a (u x)‖ ≤ C)
    (hbj : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j b (firstJet u x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 1 (a ∘ u) x‖ ≤ C^2 ∧
    ‖iteratedFDeriv ℝ 2 (a ∘ u) x‖ ≤ C^2*(‖iteratedFDeriv ℝ 2 u x‖+C^2) ∧
    ‖iteratedFDeriv ℝ 1 (b ∘ firstJet u) x‖ ≤ C*(C+‖iteratedFDeriv ℝ 2 u x‖) ∧
    ‖iteratedFDeriv ℝ 2 (b ∘ firstJet u) x‖ ≤ C^2*(‖iteratedFDeriv ℝ 2 u x‖+
      ‖iteratedFDeriv ℝ 3 u x‖+(C+‖iteratedFDeriv ℝ 2 u x‖)^2) := by
  have hPC : (Fintype.card (OrderedFinpartition 2) : ℝ)*C ≤ C^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hP hC]
  have hf1 : ‖iteratedFDeriv ℝ 1 (firstJet u) x‖ ≤ C+‖iteratedFDeriv ℝ 2 u x‖ := by
    rw [norm_firstJet_deriv hu]
    exact max_le ((hu1.trans (le_add_of_nonneg_right (norm_nonneg _))))
      (le_add_of_nonneg_left hC)
  have hf2 : ‖iteratedFDeriv ℝ 2 (firstJet u) x‖ ≤ ‖iteratedFDeriv ℝ 2 u x‖+‖iteratedFDeriv ℝ 3 u x‖ := by
    rw [norm_firstJet_deriv hu]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  refine ⟨?_,?_,?_,?_⟩
  · exact (composition_first_jet_bound hu ha).trans (by
      simpa only [pow_two] using mul_le_mul (haj 1 (by decide)) hu1 (norm_nonneg _) hC)
  · exact (composition_second_jet_bound hu ha hC haj).trans
      (mul_le_mul hPC (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hu1 2))
        (by positivity) (sq_nonneg C))
  · exact (composition_first_jet_bound (firstJet_smoothAt hu) hb).trans
      (mul_le_mul (hbj 1 (by decide)) hf1 (norm_nonneg _) hC)
  · exact (composition_second_jet_bound (firstJet_smoothAt hu) hb hC hbj).trans
      (mul_le_mul hPC (add_le_add hf2 (pow_le_pow_left₀ (norm_nonneg _) hf1 2))
        (by positivity) (sq_nonneg C))

variable {ι : Type*} [Fintype ι]
lemma frozen_equation_jet_norm (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u r : E → F} {a : E → G}
    (hu : ContDiffOn ℝ ∞ u U) (hr : ContDiffOn ℝ ∞ r U)
    (ha : ContDiffOn ℝ ∞ a U) (heq : ∀ y ∈ U, B (a y) (hessian u y) = r y)
    {x : E} (hx : x ∈ U) (v : ι → E)
    (hframe : ∀ H : E →L[ℝ] E →L[ℝ] F, B (a x) H = ∑ i, H (v i) (v i))
    (e : OrthonormalBasis ι ℝ E) (m : ℕ) (σ : Fin m → ι) :
    ‖frameLaplace v (jetFamily e m u σ) x‖ ≤ ‖iteratedFDeriv ℝ m r x‖+
      ‖iteratedFDeriv ℝ m (fun y => B (a y-a x) (hessian u y)) x‖ := by
  unfold jetFamily
  rw [frozen_equation_word B hU hu hr ha heq hx v hframe]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · simpa only [Function.comp_def,e.norm_eq_one,Finset.prod_const_one,mul_one] using
      norm_word_ofFn_le hU hr m (fun i => e (σ i)) hx
  · simpa only [Function.comp_def,e.norm_eq_one,Finset.prod_const_one,mul_one] using
      norm_word_ofFn_le hU ((B.contDiff.comp_contDiffOn (ha.sub contDiffOn_const)).clm_apply
        (hessian_smoothOn hU hu)) m (fun i => e (σ i)) hx

lemma quasilinear_low_residuals (B : G →L[ℝ] (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) {u r : E → F} {a : F → G} {b : F × (E →L[ℝ] F) → F}
    (hu : ContDiffOn ℝ ∞ u U) (hr : ContDiffOn ℝ ∞ r U)
    (ha : ∀ y ∈ U, ContDiffAt ℝ ∞ a (u y))
    (hb : ∀ y ∈ U, ContDiffAt ℝ ∞ b (firstJet u y))
    (heq : ∀ y ∈ U, B (a (u y)) (hessian u y) = r y+b (firstJet u y))
    {x : E} (hx : x ∈ U) (v : ι → E)
    (hframe : ∀ H : E →L[ℝ] E →L[ℝ] F, B (a (u x)) H = ∑ i, H (v i) (v i))
    (e : OrthonormalBasis ι ℝ E) {C : ℝ} (hC : 0 ≤ C) (hB : ‖B‖ ≤ C)
    (hP : (Fintype.card (OrderedFinpartition 2) : ℝ) ≤ C)
    (hu1 : ‖iteratedFDeriv ℝ 1 u x‖ ≤ C)
    (haj : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j a (u x)‖ ≤ C)
    (hbj : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j b (firstJet u x)‖ ≤ C)
    (hrj : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j r x‖ ≤ C) :
    (∀ σ : Fin 1 → ι, ‖frameLaplace v (jetFamily e 1 u σ) x‖ ≤
      (2*C+C^2+C^3)*(1+‖iteratedFDeriv ℝ 2 u x‖)) ∧
    (∀ σ : Fin 2 → ι, ‖frameLaplace v (jetFamily e 2 u σ) x‖ ≤
      (C+3*C^2+5*C^3+C^4+C^5)*(1+‖iteratedFDeriv ℝ 2 u x‖^2+‖iteratedFDeriv ℝ 3 u x‖)) := by
  have hac : ContDiffOn ℝ ∞ (a ∘ u) U := fun y hy =>
    ((ha y hy).comp y (hu.contDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hbc : ContDiffOn ℝ ∞ (b ∘ firstJet u) U := fun y hy =>
    ((hb y hy).comp y (firstJet_smoothAt (hu.contDiffAt (hU.mem_nhds hy)))).contDiffWithinAt
  obtain ⟨ha1,ha2,hb1,hb2⟩ := low_coefficient_bounds (hu.contDiffAt (hU.mem_nhds hx))
    (ha x hx) (hb x hx) hC hP hu1 haj hbj
  have hnorm (m : ℕ) (σ : Fin m → ι) : ‖frameLaplace v (jetFamily e m u σ) x‖ ≤
      ‖iteratedFDeriv ℝ m r x‖+‖iteratedFDeriv ℝ m (b ∘ firstJet u) x‖+
        ‖iteratedFDeriv ℝ m (fun y => B (a (u y)-a (u x)) (hessian u y)) x‖ := by
    exact (frozen_equation_jet_norm B hU hu (hr.add hbc) hac heq hx v hframe e m σ).trans
      (add_le_add (norm_iteratedFDeriv_add_le (hr.contDiffAt (hU.mem_nhds hx))
        (hbc.contDiffAt (hU.mem_nhds hx)) m) le_rfl)
  constructor
  · intro σ
    apply affine_residual_bound hC (norm_nonneg _) (hrj 1 (by decide)) hb1 _ (hnorm 1 σ)
    have hh := frozen_first_bound B hU hu hac hx
    exact hh.trans (by
      calc
        _ ≤ C*C^2*‖iteratedFDeriv ℝ 2 u x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul hB ha1 (norm_nonneg _) hC) (norm_nonneg _)
        _ = _ := by ring)
  · intro σ
    apply quadratic_residual_bound hC (norm_nonneg _) (norm_nonneg _) (hrj 2 (by decide)) hb2 _ (hnorm 2 σ)
    exact (frozen_second_bound B hU hu hac hx).trans (mul_le_mul hB
      (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha1 (by norm_num)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ha2 (norm_nonneg _))) (by positivity) hC)
end HigherJet

end
end

end OAI
