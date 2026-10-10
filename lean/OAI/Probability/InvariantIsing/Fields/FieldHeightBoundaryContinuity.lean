import OAI.Probability.InvariantIsing.Fields.FieldHeightRegularization

namespace OAI

/-! The strict regularization converges in the actual field value and
every actual magnetization level. No endpoint derivative is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldVaryingOverlaps_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (root : ℝ≥0) (i : Fin (L.length + 1)) :
    (∫ u, fieldVaryingSquares L t i (Real.sqrt (root : ℝ) * u) ∂gaussianReal 0 1) =
      fieldScalarOverlaps (L.map (fun av => (av.1, av.2 t))) root
        (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) i) := by
  have hm := (fieldVaryingSquares_regular L hL t i).1
  rw [fieldScalarOverlaps, ← fieldVaryingSquares_eq_scalar L t i,
    integral_gaussianReal_zero_eq_standard root hm]

def fieldRegularizedRoot (h : FieldStep) (t : ℝ) : ℝ≥0 :=
  NNReal.mk (h.height 0 + fieldHeightEpsilon t)
    (add_nonneg (h.nonneg 0) (fieldHeightEpsilon_nonneg t))

lemma continuous_fieldRegularizedRoot (h : FieldStep) : Continuous (fieldRegularizedRoot h) :=
  (continuous_const.add continuous_fieldHeightEpsilon).subtype_mk _

lemma continuous_fieldRegularizedValue (h : FieldStep) :
    Continuous (fun t => fieldValue (fieldRegularized h t) 0) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hval := continuous_fieldVaryingValue L hL hc hV hv
  obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hL hV hv
  have hroot : Continuous (fun t : ℝ => (fieldRegularizedRoot h t : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)
  have hi := continuous_field_gaussian_integral hval hroot
    (show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const)
    hcap zero_le_one (fun t y => by simpa only [one_mul] using hb t y)
  have hlast : Continuous (fun t => (fieldRegularized h t).height (Fin.last h.depth) / 2) := by
    change Continuous (fun t => (h.height (Fin.last h.depth) +
      fieldHeightEpsilon t * ((Fin.last h.depth).val + 1 : ℕ)) / 2)
    have heps := continuous_fieldHeightEpsilon
    fun_prop
  convert hi.sub hlast using 1
  funext t
  rw [fieldValue_scalar_chain, ← fieldRegularizedIncrements_eval,
    ← fieldVaryingValue_eq_scalar]
  simp only [gaussianOperator, ite_true, zero_add, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one,
    fieldRegularizedRoot, NNReal.coe_mk, Pi.sub_apply, L]
  rfl

lemma continuous_fieldRegularizedMagnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    Continuous (fun t => fieldMagnetizationLevel (fieldRegularized h t) i) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  let j : Fin (L.length + 1) := ⟨i.val, by
    simpa only [L, fieldRegularizedIncrements, List.length_ofFn] using i.isLt⟩
  have hcont := continuous_fieldVaryingOverlaps L hL hc hV hv
    (fieldRegularizedRoot h) (continuous_fieldRegularizedRoot h) j
  convert hcont using 1
  funext t
  rw [fieldVaryingOverlaps_eq_scalar L hL]
  unfold fieldMagnetizationLevel
  have hroot : (NNReal.mk ((fieldRegularized h t).height 0)
      ((fieldRegularized h t).nonneg 0)) = fieldRegularizedRoot h t := by
    apply Subtype.ext
    simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
      fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one]
    rfl
  rw [hroot]
  unfold fieldScalarOverlaps
  apply integral_congr_ae
  apply ae_of_all
  intro z
  exact congrFun (fieldScalarSquares_congr_list
    (fieldRegularizedIncrements_eval h t).symm (fun y => Real.log (Real.cosh y))
    Real.tanh _ _ rfl) z

end InvariantIsing

end

end OAI
