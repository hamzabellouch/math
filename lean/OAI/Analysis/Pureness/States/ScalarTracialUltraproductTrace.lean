import OAI.Analysis.Pureness.States.ScalarMatrixUltraEmbedding
import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltralimitComplex

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder

lemma scalarMatrixPositiveTrace_eq_state (n : ℕ) (z : FinMatrix ℂ (n+1)) :
    (scalarMatrixPositiveTrace n).complexValue z = (scalarMatrixTracialState n).functional z := by
  rw [scalarMatrixPositiveTrace_complex]
  change (n+1 : ℂ)⁻¹ * Matrix.trace (CStarMatrix.ofMatrix.symm z) =
    (Fintype.card (Fin (n+1)) : ℂ)⁻¹ * ∑ i, z i i
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,Matrix.trace]
  rfl

variable (U : Ultrafilter ℕ)

instance scalarMatrixUltraPartialOrder : PartialOrder (ScalarTracialMatrixUltraproduct U) :=
  CStarAlgebra.spectralOrder _
instance scalarMatrixUltraStarOrderedRing : StarOrderedRing (ScalarTracialMatrixUltraproduct U) :=
  CStarAlgebra.spectralOrderedRing _

lemma scalarFilteredQuotientMap_apply (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
      scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit u =
        (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
          scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap u := rfl

def scalarMatrixUltraValue (z : ScalarTracialMatrixUltraproduct U) : ℂ :=
  ultralimitAWQuasitrace scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_sqrt_add
    (ultraproductAWEmbedding scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
      scalarMatrixPositiveTrace_metricSize_add z)

lemma scalarMatrixUltraValue_map (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    scalarMatrixUltraValue U (filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
      scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit u) =
        (ultralimitPositiveQuasitrace scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit).complexValue u :=
  ultralimitAWQuasitrace_original _ _ _ _ _ u

lemma scalarMatrixUltraValue_tendsto (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    Tendsto (fun n => (scalarMatrixTracialState n).functional (u n)) (U : Filter ℕ)
      (nhds (scalarMatrixUltraValue U (filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit u))) := by
  rw [scalarMatrixUltraValue_map]
  simpa only [scalarMatrixPositiveTrace_eq_state] using
    quasitraceUltraComplex_tendsto scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit u

lemma scalarMatrixUltraValue_add (z w : ScalarTracialMatrixUltraproduct U) :
    scalarMatrixUltraValue U (z+w) = scalarMatrixUltraValue U z+scalarMatrixUltraValue U w := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective z
  obtain ⟨v,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective w
  have hq : (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap (u+v) = (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap u + (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap v := rfl
  rw [← hq]
  apply tendsto_nhds_unique (scalarMatrixUltraValue_tendsto U (u+v))
  simpa only [lp.coeFn_add,Pi.add_apply,map_add,scalarFilteredQuotientMap_apply] using
    (scalarMatrixUltraValue_tendsto U u).add (scalarMatrixUltraValue_tendsto U v)

lemma scalarMatrixUltraValue_smul (c : ℂ) (z : ScalarTracialMatrixUltraproduct U) :
    scalarMatrixUltraValue U (c • z) = c*scalarMatrixUltraValue U z := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective z
  have hq : (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap (c • u) = c • (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap u := rfl
  rw [← hq]
  apply tendsto_nhds_unique (scalarMatrixUltraValue_tendsto U (c • u))
  simpa only [lp.coeFn_smul,Pi.smul_apply,map_smul,smul_eq_mul,scalarFilteredQuotientMap_apply] using
    (scalarMatrixUltraValue_tendsto U u).const_mul c

lemma scalarMatrixUltraValue_tracial (z w : ScalarTracialMatrixUltraproduct U) :
    scalarMatrixUltraValue U (z*w) = scalarMatrixUltraValue U (w*z) := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective z
  obtain ⟨v,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective w
  rw [← map_mul (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap u v,← map_mul (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ) scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap v u]
  apply tendsto_nhds_unique (scalarMatrixUltraValue_tendsto U (u*v))
  have he (n : ℕ) : (scalarMatrixTracialState n).functional ((u*v) n) =
      (scalarMatrixTracialState n).functional ((v*u) n) :=
    (scalarMatrixTracialState n).tracial (u n) (v n)
  simpa only [he,scalarFilteredQuotientMap_apply] using scalarMatrixUltraValue_tendsto U (v*u)

lemma scalarMatrixUltraValue_unit : scalarMatrixUltraValue U 1 = 1 := by
  unfold scalarMatrixUltraValue
  rw [map_one,ultralimitAWQuasitrace_unit]

lemma scalarMatrixUltraValue_square_nonneg (z : ScalarTracialMatrixUltraproduct U) :
    0 ≤ scalarMatrixUltraValue U (star z*z) := by
  let φ := ultraproductAWEmbedding scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
    scalarMatrixPositiveTrace_metricSize_add
  let Q := ultralimitAWQuasitrace scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_sqrt_add
  change 0 ≤ Q (φ (star z*z))
  rw [map_mul φ,map_star φ]
  exact Q.square_nonneg _

lemma scalarMatrixUltraValue_square_eq_zero (z : ScalarTracialMatrixUltraproduct U) :
    scalarMatrixUltraValue U (star z*z) = 0 ↔ z=0 := by
  let φ := ultraproductAWEmbedding scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
    scalarMatrixPositiveTrace_metricSize_add
  let Q := ultralimitAWQuasitrace scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_sqrt_add
  change Q (φ (star z*z))=0 ↔ _
  rw [map_mul φ,map_star φ]
  rw [ultralimitAWQuasitrace_faithful]
  constructor
  · intro h
    apply ultraproductAWEmbedding_injective scalarMatrixPositiveTrace U scalarMatrixPositiveTrace_unit
      scalarMatrixPositiveTrace_metricSize_add
    exact h.trans (map_zero φ).symm
  · rintro rfl
    exact map_zero φ

def scalarMatrixUltraLinear : ScalarTracialMatrixUltraproduct U →ₗ[ℂ] ℂ where
  toFun := scalarMatrixUltraValue U
  map_add' := scalarMatrixUltraValue_add U
  map_smul' := scalarMatrixUltraValue_smul U

def scalarMatrixUltraTracialState : TracialState (ScalarTracialMatrixUltraproduct U) where
  functional := { scalarMatrixUltraLinear U with
    monotone' := by
      intro z w hzw
      apply sub_nonneg.mp
      change 0 ≤ scalarMatrixUltraLinear U w-scalarMatrixUltraLinear U z
      rw [← map_sub]
      obtain ⟨v,hv⟩ := Positive.exists_starMul_factor (⟨w-z,sub_nonneg.mpr hzw⟩ : Positive (ScalarTracialMatrixUltraproduct U))
      change 0 ≤ scalarMatrixUltraValue U (w-z)
      change star v*v = w-z at hv
      rw [← hv]
      exact scalarMatrixUltraValue_square_nonneg U v }
  normalized := scalarMatrixUltraValue_unit U
  tracial := scalarMatrixUltraValue_tracial U

lemma scalarMatrixUltraTracialState_faithful (z : ScalarTracialMatrixUltraproduct U) :
    (scalarMatrixUltraTracialState U).functional (star z*z)=0 ↔ z=0 :=
  scalarMatrixUltraValue_square_eq_zero U z
end CuntzPureness

end

end OAI
