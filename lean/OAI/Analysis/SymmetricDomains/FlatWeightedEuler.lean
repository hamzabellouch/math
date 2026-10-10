import Mathlib
import OAI.Analysis.SymmetricDomains.ModelNormalTranslationAd
import OAI.Analysis.SymmetricDomains.LieBracketIndicatorConst

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

 theorem sqrt_exp_eq (t : ℝ) : Real.sqrt (Real.exp t)=Real.exp (t/2) := by
  rw [Real.sqrt_eq_iff_eq_sq (Real.exp_pos t).le (Real.exp_pos (t/2)).le,
    ←Real.exp_nat_mul]
  congr 1
  ring

def flatWeightedEuler (r k : ℕ) : Affine (r+k) →L[ℂ] Affine (r+k) :=
  (affineProductCoordinates r k).toContinuousLinearMap.comp
    ((((1/2 : ℂ) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k))).comp
      (affineProductCoordinates r k).symm.toContinuousLinearMap)

 theorem flatWeightedScale_exp_apply {r k : ℕ} (t : ℝ) (x : Affine (r+k)) :
    flatWeightedScale (Real.exp_pos t) x=affineProductCoordinates r k
      (Real.exp (t/2) • ((affineProductCoordinates r k).symm x).1,
        Real.exp t • ((affineProductCoordinates r k).symm x).2) := by
  change affineProductCoordinates r k
    (Real.sqrt (Real.exp t) • ((affineProductCoordinates r k).symm x).1,
      Real.exp t • ((affineProductCoordinates r k).symm x).2)=_
  rw [sqrt_exp_eq]

 theorem hasDerivAt_flatWeightedScale_exp {r k : ℕ} (x : Affine (r+k)) :
    HasDerivAt (fun t : ℝ => flatWeightedScale (Real.exp_pos t) x)
      (flatWeightedEuler r k x) 0 := by
  let e := affineProductCoordinates r k
  have ha : HasDerivAt (fun t : ℝ => Real.exp (t/2)) (1/2) 0 := by
    convert (Real.hasDerivAt_exp (0/2)).comp 0 ((hasDerivAt_id (0 : ℝ)).div_const 2) using 1 <;> first | rfl | norm_num
  have hb : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hp := (ha.smul_const (e.symm x).1).prodMk (hb.smul_const (e.symm x).2)
  have hh := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Affine r × Affine k)
    (E := Affine (r+k)) 0 (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt hp
  simp only [one_smul] at hh
  convert hh using 1 <;> try rfl
  · funext t
    exact flatWeightedScale_exp_apply t x
  · change e ((1/2 : ℂ) • (e.symm x).1,(e.symm x).2)=e ((1/2 : ℝ) • (e.symm x).1,(e.symm x).2)
    congr 2
    ext i
    simp [Complex.real_smul]

 theorem exists_actual_model_euler {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) :
    ∃ E : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm E.val=((affineProductCoordinates r k) '' D).indicator (flatWeightedEuler r k) := by
  apply exists_complete_linear_generator_in_model hU hc hbd Γ hhol e
    (fun t => flatWeightedScale (Real.exp_pos t))
    (fun t => flatWeightedScale_mem D hd (Real.exp_pos t))
  · intro x
    rw [flatWeightedScale_exp_apply]
    simp
  · intro s t x
    rw [flatWeightedScale_exp_apply (s+t),flatWeightedScale_exp_apply s,flatWeightedScale_exp_apply t]
    simp only [ContinuousLinearEquiv.symm_apply_apply,add_div,Real.exp_add,mul_smul]
  · simp_rw [flatWeightedScale_exp_apply]
    apply (affineProductCoordinates r k).continuous.comp
    exact ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul
      (continuous_fst.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))).prodMk
      ((Real.continuous_exp.comp continuous_fst).smul
        (continuous_snd.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd)))
  · exact hasDerivAt_flatWeightedScale_exp

end Biholomorph
end Release061

end

end OAI
