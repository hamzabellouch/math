import OAI.Analysis.ModularTheory.CrossedProduct
import OAI.Analysis.ModularRecovery.StrongIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace OAI

/-! Strong continuity and integrated regular translations in the concrete
modular crossed product. These are actual operators on L²(ℝ,H), without a
trace or semifiniteness assumption on the generated von Neumann algebra. -/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma continuous_modularLpTranslate (f : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun t : ℝ => modularLpTranslate volume t f) := by
  let g : ℝ → C(ℝ, ℝ) := fun t => ⟨fun s => s - t, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_sub_right volume t) (by norm_num)

def modularLpTranslateOperator (t : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (modularLpTranslate (H := H) volume t).toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] lemma modularLpTranslateOperator_apply (t : ℝ)
    (f : Lp H 2 (volume : Measure ℝ)) :
    modularLpTranslateOperator t f = modularLpTranslate volume t f := rfl

omit [CompleteSpace H] in
lemma modularLpTranslate_opNorm_le (t : ℝ) :
    ‖modularLpTranslateOperator (H := H) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖modularLpTranslate volume t f‖ ≤ 1 * ‖f‖
  rw [(modularLpTranslate volume t).norm_map, one_mul]

def integratedModularTranslation (k : ℝ → ℂ) (hk : Integrable k) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  BoundedRecovery.strongIntegral k hk
    (modularLpTranslateOperator (H := H))
    (fun (f : Lp H 2 (volume : Measure ℝ)) => continuous_modularLpTranslate f)
    1 (modularLpTranslate_opNorm_le (H := H))

omit [CompleteSpace H] in
lemma integratedModularTranslation_apply (k : ℝ → ℂ) (hk : Integrable k)
    (f : Lp H 2 (volume : Measure ℝ)) :
    integratedModularTranslation k hk f = ∫ t, k t • modularLpTranslate volume t f := rfl

omit [CompleteSpace H] in
lemma integratedModularTranslation_norm_le (k : ℝ → ℂ) (hk : Integrable k) :
    ‖integratedModularTranslation (H := H) k hk‖ ≤ ∫ t, ‖k t‖ := by
  have hn := BoundedRecovery.norm_strongIntegral_le k hk
    (modularLpTranslateOperator (H := H))
    (fun (f : Lp H 2 (volume : Measure ℝ)) => continuous_modularLpTranslate f)
    zero_le_one (modularLpTranslate_opNorm_le (H := H))
  exact hn.trans_eq (mul_one _)

lemma integratedModularTranslation_mem (S : BoundedRecovery.StandardModularData H)
    (k : ℝ → ℂ) (hk : Integrable k) :
    integratedModularTranslation k hk ∈ modularCrossedProduct volume S := by
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro f
  have hi := BoundedRecovery.integrable_smul_bounded_orbit hk
    (continuous_modularLpTranslate f)
    (fun t => (modularLpTranslate volume t).norm_map f |>.le)
  change b (∫ t, k t • modularLpTranslate volume t f) =
    ∫ t, k t • modularLpTranslate volume t (b f)
  rw [← b.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul]
  congr 1
  have heq := (VonNeumannAlgebra.mem_commutant_iff.mp hb)
    _ (modularCrossedProduct_translate volume S t)
  exact (congrArg (fun c : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) => c f) heq).symm

end WeakPureInfiniteness

end

end OAI
