import OAI.Analysis.Mahler.DilationTransport
import OAI.Analysis.Mahler.WedgeCalculus

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology TensorProduct

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The linear operation taking a real derivative to d^c. -/
noncomputable def dcOperator : (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ) :=
  (-1 / 4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure

noncomputable def dcOneOperator : (E →L[ℝ] ℂ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp dcOperator

lemma dcOneOperator_fderiv (u : E → ℂ) (x : E) :
    dcOneOperator (fderiv ℝ u x) = oneForm (dcLinear u) x := rfl

/-- The second derivative determines the actual exterior derivative of d^c. -/
noncomputable def ddcTwoJet (B : E →L[ℝ] (E →L[ℝ] ℂ)) :
    E [⋀^Fin 2]→L[ℝ] ℂ :=
  alternatizeUncurryFin (dcOneOperator.comp B)

theorem extDeriv_dc_eq_twoJet {u : E → ℂ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    extDeriv (oneForm (dcLinear u)) x = ddcTwoJet (fderiv ℝ (fderiv ℝ u) x) := by
  have hd := dcOneOperator.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (oneForm (dcLinear u)) _ x at hd
  unfold extDeriv ddcTwoJet
  rw [hd.fderiv]

lemma continuous_dcOneOperator : Continuous (dcOneOperator (E := E)) :=
  dcOneOperator.continuous

lemma continuous_ddcTwoJet : Continuous (ddcTwoJet (E := E)) := by
  unfold ddcTwoJet alternatizeUncurryFin
  exact (alternatizeUncurryFinCLM ℝ E ℂ).continuous.comp
    (continuous_const.clm_comp continuous_id)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuous_wedge_eval [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a : X → E [⋀^ι]→ₗ[ℝ] ℂ} {b : X → E [⋀^κ]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun s => a s v))
    (hb : ∀ v, Continuous (fun s => b s v)) (v : ι ⊕ κ → E) :
    Continuous (fun s => wedge (a s) (b s) v) := by
  have ht (σ : Equiv.Perm.ModSumCongr ι κ) :
      Continuous (fun s => (LinearMap.mul' ℝ ℂ)
        (AlternatingMap.domCoprod.summand (a s) (b s) σ v)) := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      exact continuous_const.mul ((ha _).mul (hb _))
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, _root_.map_sum] using continuous_finsetSum Finset.univ (fun σ _ => ht σ)

lemma continuous_wedgePower_eval {X : Type*} [TopologicalSpace X]
    {a : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun s => a s v)) (k : ℕ) (v : WedgePowerSlots k → E) :
    Continuous (fun s => wedgePower (a s) k v) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact continuous_wedge_eval ha ih v

abbrev RealComplexTwoJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] ℂ) × (E →L[ℝ] (E →L[ℝ] ℂ))

noncomputable def boundaryJet (p : RealComplexTwoJet E) (k : ℕ) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (dcOneOperator p.1).toAlternatingMap
    (wedgePower (ddcTwoJet p.2).toAlternatingMap k)

lemma continuous_boundaryJet_eval (k : ℕ) (v : Fin 1 ⊕ WedgePowerSlots k → E) :
    Continuous (fun p : RealComplexTwoJet E => boundaryJet p k v) := by
  apply continuous_wedge_eval
  · intro w
    change Continuous (fun p : RealComplexTwoJet E => dcOperator p.1 (w 0))
    exact (dcOperator.continuous.comp continuous_fst).clm_apply continuous_const
  · apply continuous_wedgePower_eval
    intro w
    change Continuous (fun p : RealComplexTwoJet E => ddcTwoJet p.2 w)
    exact (continuous_eval_const w).comp
      (continuous_ddcTwoJet.comp continuous_snd)

theorem boundaryForm_eq_jet {u : E → ℂ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (k : ℕ) :
    boundaryForm u k x = boundaryJet (fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x) k := by
  unfold boundaryForm boundaryJet
  rw [dcOneOperator_fderiv, extDeriv_dc_eq_twoJet hu]

end Mahler

end OAI
