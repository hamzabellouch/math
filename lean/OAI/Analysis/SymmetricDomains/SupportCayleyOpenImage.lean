import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.CayleyTangentBound

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def supportCayley (x : E × (Fin (k+1) → ℂ)) : E × (Fin (k+1) → ℂ) :=
  ((x.2 0+I)⁻¹ • x.1,fun i => normalCayley (x.2 i))

def supportUncayley (x : E × (Fin (k+1) → ℂ)) : E × (Fin (k+1) → ℂ) :=
  ((normalUncayley (x.2 0)+I) • x.1,fun i => normalUncayley (x.2 i))

theorem supportUncayley_cayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, x.2 i+I ≠ 0) : supportUncayley (supportCayley x) = x := by
  apply Prod.ext
  · simp only [supportUncayley,supportCayley,normalUncayley_cayley (hx 0),
      smul_smul,mul_inv_cancel₀ (hx 0),one_smul]
  · funext i
    exact normalUncayley_cayley (hx i)

theorem supportCayley_uncayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, 1-x.2 i ≠ 0) : supportCayley (supportUncayley x) = x := by
  apply Prod.ext
  · simp only [supportUncayley,supportCayley,smul_smul,
      inv_mul_cancel₀ (normalUncayley_add_I_ne_zero (hx 0)),one_smul]
  · funext i
    exact normalCayley_uncayley (hx i)

theorem analyticAt_supportCayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, x.2 i+I ≠ 0) : AnalyticAt ℂ supportCayley x := by
  have hw (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => q.2 i) x :=
    ((ContinuousLinearMap.proj i : (Fin (k+1) → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => (q.2 0+I)⁻¹ • q.1) x :=
    (((hw 0).add analyticAt_const).inv (hx 0)).smul analyticAt_fst
  refine hz.prod (AnalyticAt.pi fun i => ?_)
  exact ((hw i).sub analyticAt_const).div ((hw i).add analyticAt_const) (hx i)

theorem analyticAt_supportUncayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, 1-x.2 i ≠ 0) : AnalyticAt ℂ supportUncayley x := by
  have hw (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => q.2 i) x :=
    ((ContinuousLinearMap.proj i : (Fin (k+1) → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp analyticAt_snd
  have hu (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => normalUncayley (q.2 i)) x :=
    (analyticAt_const.mul (analyticAt_const.add (hw i))).div
      (analyticAt_const.sub (hw i)) (hx i)
  exact ((hu 0).add analyticAt_const).smul analyticAt_fst |>.prod (AnalyticAt.pi hu)

def supportCayleyChart : OpenPartialHomeomorph (E × (Fin (k+1) → ℂ)) (E × (Fin (k+1) → ℂ)) where
  toFun := supportCayley
  invFun := supportUncayley
  source := {x | ∀ i, x.2 i+I ≠ 0}
  target := {x | ∀ i, 1-x.2 i ≠ 0}
  map_source' := by
    intro x hx i
    exact sub_ne_zero.mpr (normalCayley_ne_one (hx i)).symm
  map_target' := by
    intro x hx i
    exact normalUncayley_add_I_ne_zero (hx i)
  left_inv' _ hx := supportUncayley_cayley hx
  right_inv' _ hx := supportCayley_uncayley hx
  open_source := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage ((continuous_apply i |>.comp continuous_snd).add continuous_const)
  open_target := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage (continuous_const.sub (continuous_apply i |>.comp continuous_snd))
  continuousOn_toFun := fun _ hx => (analyticAt_supportCayley hx).continuousAt.continuousWithinAt
  continuousOn_invFun := fun _ hx => (analyticAt_supportUncayley hx).continuousAt.continuousWithinAt

theorem supportCayley_bounded {D : Set (E × (Fin (k+1) → ℂ))}
    {c : ℝ} (hc : 0 < c) (hD : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < (x.2 i).im) :
    Bornology.IsBounded (supportCayley '' D) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (2*Real.sqrt c)⁻¹ 1,?_⟩
  rintro y ⟨x,hx,rfl⟩
  rw [supportCayley,Prod.norm_def]
  apply max_le
  · exact (cayley_tangent_bound hc (hD x hx 0).le).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (norm_normalCayley_lt_one ?_).le
    exact (mul_nonneg hc.le (sq_nonneg _)).trans_lt (hD x hx i)

theorem supportCayley_open_image {D : Set (E × (Fin (k+1) → ℂ))}
    (hD : IsOpen D) (hupper : ∀ x ∈ D, ∀ i, 0 < (x.2 i).im) :
    IsOpen (supportCayley '' D) := by
  have hsub : D ⊆ (supportCayleyChart (E := E) (k := k)).source := by
    intro x hx i
    exact add_I_ne_zero_of_im_pos (hupper x hx i)
  exact supportCayleyChart.isOpen_image_of_subset_source hD hsub

end Release061

end

end OAI
