import OAI.Analysis.KadisonKastler.AbelianInvariantMean
import OAI.Analysis.KadisonKastler.PureStateExtension

namespace OAI

/-! # Invariant states obtained by the constructed scalar mean

The scalar orbit of the state is averaged, so every invariant restriction
is preserved even when the state is not normal. Strong invariance under
probability-measure averages is a separate step.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))

def stateOrbitScalar (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (T : H →L[ℂ] H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => φ (unitaryConj (U g) T)) (‖φ‖*‖T‖) (fun g =>
      (φ.le_opNorm _).trans_eq (by rw [norm_unitaryConj]))

@[simp] theorem stateOrbitScalar_apply (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) (g : G) : stateOrbitScalar U φ T g=φ (unitaryConj (U g) T) := rfl

def stateOrbitMap (φ : (H →L[ℂ] H) →L[ℂ] ℂ) :
    (H →L[ℂ] H) →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := stateOrbitScalar U φ
      map_add' S T := by
        ext g
        change φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (S+T)) =
          φ ((Unitary.conjStarAlgAut ℂ _ (U g)) S)+φ ((Unitary.conjStarAlgAut ℂ _ (U g)) T)
        rw [map_add,map_add]
      map_smul' c T := by
        ext g
        change φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (c • T)) = c • φ _
        rw [map_smul,map_smul]
        rfl }
    ‖φ‖ (fun T => (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (fun g => (φ.le_opNorm _).trans_eq (by rw [norm_unitaryConj])))

def averagedState (φ : (H →L[ℂ] H) →L[ℂ] ℂ) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  m.toCLM.comp (stateOrbitMap U φ)

@[simp] theorem averagedState_apply (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) : m.averagedState U φ T = m.toCLM (stateOrbitScalar U φ T) := rfl

theorem averagedState_eq_of_invariant_values (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (T : H →L[ℂ] H) (hT : ∀ g, φ (unitaryConj (U g) T)=φ T) :
    m.averagedState U φ T=φ T := by
  have he : stateOrbitScalar U φ T=BoundedContinuousFunction.const G (φ T) := by
    ext g
    exact hT g
  rw [averagedState_apply,he,m.fixed]

theorem averagedState_isState (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (m.averagedState U φ) := by
  apply (isState_iff _).mpr
  refine ⟨?_,fun T => ?_⟩
  · rw [m.averagedState_eq_of_invariant_values U φ 1 (fun g => by
      rw [show unitaryConj (U g) (1 : H →L[ℂ] H)=1 from
        (Unitary.conjStarAlgAut ℂ _ (U g)).map_one])]
    exact ((isState_iff φ).mp hφ).1
  · apply m.positive
    intro g
    change (φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (star T*T))).im = 0 ∧
      0 ≤ (φ ((Unitary.conjStarAlgAut ℂ _ (U g)) (star T*T))).re
    let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U g)
    have he : e (star T*T)=star (e T)*e T := by
      calc
        _ = e (star T)*e T := e.map_mul _ _
        _ = _ := congrArg (fun a : H →L[ℂ] H => a*e T) (map_star e T)
    change (φ (e (star T*T))).im=0 ∧ 0 ≤ (φ (e (star T*T))).re
    rw [he]
    exact hφ.2 (e T)

theorem averagedState_invariant (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (g : G)
    (T : H →L[ℂ] H) :
    m.averagedState U φ (unitaryConj (U g) T) = m.averagedState U φ T := by
  have he : stateOrbitScalar U φ (unitaryConj (U g) T) =
      scalarMeanTranslate g⁻¹ (stateOrbitScalar U φ T) := by
    ext h
    change φ (unitaryConj (U h) (unitaryConj (U g) T))=φ (unitaryConj (U ((g⁻¹)⁻¹*h)) T)
    rw [← unitaryConj_mul,← map_mul,inv_inv,mul_comm h g]
  rw [averagedState_apply,he,m.invariant,← averagedState_apply]

theorem averagedState_fixed (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (T : H →L[ℂ] H)
    (hT : ∀ g, unitaryConj (U g) T=T) : m.averagedState U φ T=φ T :=
  m.averagedState_eq_of_invariant_values U φ T (fun g => congrArg φ (hT g))

end ScalarInvariantMean

end

end KadisonKastler

end OAI
