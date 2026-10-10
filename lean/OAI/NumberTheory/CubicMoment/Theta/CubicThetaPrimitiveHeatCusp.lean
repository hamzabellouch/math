import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveHeat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveZeroRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroRowHeat

namespace OAI

/-! Uniform control of the actual truncated primitive heat kernel in a cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

abbrev CubicThetaNonzeroFirstPrimitiveRow := {r : CubicThetaPrimitiveRow // r.c≠0}

def cubicThetaNonzeroFirstPrimitiveRow_map (r : CubicThetaNonzeroFirstPrimitiveRow) :
    CubicThetaNonzeroRow := (⟨r.val.c,r.property⟩,r.val.d)

lemma cubicThetaNonzeroFirstPrimitiveRow_map_injective :
    Function.Injective cubicThetaNonzeroFirstPrimitiveRow_map := by
  intro r q h
  apply Subtype.ext
  apply CubicThetaPrimitiveRow.ext
  · exact congrArg (fun r : CubicThetaNonzeroRow => r.1.val) h
  · exact congrArg (fun r : CubicThetaNonzeroRow => r.2) h

lemma cubicThetaPrimitiveHeatTerm_le_nonzero {p : ℂ × ℝ} (hp : 0<p.2)
    (t : ℝ) (r : CubicThetaNonzeroFirstPrimitiveRow) :
    cubicThetaPrimitiveHeatTerm p t r.val ≤
      cubicThetaNonzeroRowHeatTerm p t (cubicThetaNonzeroFirstPrimitiveRow_map r) := by
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · apply le_of_eq
    unfold cubicThetaNonzeroRowHeatTerm cubicThetaNonzeroRowQuadratic
      cubicThetaNonzeroFirstPrimitiveRow_map CubicThetaPrimitiveRow.height
      CubicThetaPrimitiveRow.denominator
    congr 1
    field_simp
  · exact (Real.exp_pos _).le

lemma cubicThetaPrimitiveHeat_nonzero_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaNonzeroFirstPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r.val) ≤
      cubicThetaNonzeroFirstHeat p t := by
  have hs := (cubicThetaPrimitiveHeat_summable hp ht).comp_injective
    (Subtype.val_injective (p:=fun r : CubicThetaPrimitiveRow => r.c≠0))
  have hfull := cubicThetaNonzeroRowHeatTerm_summable hp ht
  rw [←cubicThetaNonzeroRowHeatTerm_tsum hp ht]
  exact hs.tsum_le_tsum_of_inj cubicThetaNonzeroFirstPrimitiveRow_map
    cubicThetaNonzeroFirstPrimitiveRow_map_injective (fun _ _ => (Real.exp_pos _).le)
    (cubicThetaPrimitiveHeatTerm_le_nonzero hp t) hfull

lemma cubicThetaPrimitiveHeat_zero_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaZeroFirstRow,cubicThetaPrimitiveHeatTerm p t r.val) ≤
      (Nat.card CubicThetaZeroFirstRow:ℝ)*Real.exp (-t) := by
  let : Finite CubicThetaZeroFirstRow := cubicThetaZeroFirstRows_finite
  let : Fintype CubicThetaZeroFirstRow := Fintype.ofFinite _
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _r : CubicThetaZeroFirstRow,Real.exp (-t) := by
      apply Finset.sum_le_sum
      intro r _
      obtain ⟨u,rfl⟩ := cubicThetaUnitRow_surjective r
      unfold cubicThetaPrimitiveHeatTerm
      rw [cubicThetaUnitRow_height]
      split_ifs with hv
      · apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hp).mpr
        nlinarith
      · exact (Real.exp_pos _).le
    _ = _ := by simp [Nat.card_eq_fintype_card]

theorem cubicThetaPrimitiveHeat_cusp_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 1/2≤p.2 → ∀ t : ℝ, 0<t →
      cubicThetaPrimitiveHeat p t ≤ C*(1+t⁻¹^2) := by
  obtain ⟨D,hD,hbound⟩ := cubicThetaNonzeroFirstHeat_bound
  let n : ℝ := Nat.card CubicThetaZeroFirstRow
  have hn : 0≤n := Nat.cast_nonneg _
  refine ⟨n+D,add_nonneg hn hD,?_⟩
  intro p hp t ht
  have hp0 : 0<p.2 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp
  have he := (cubicThetaPrimitiveHeat_summable hp0 ht).tsum_subtype_add_tsum_subtype_compl
    {r : CubicThetaPrimitiveRow | r.c=0}
  have hb := add_le_add (cubicThetaPrimitiveHeat_zero_bound hp0 ht)
    (cubicThetaPrimitiveHeat_nonzero_bound hp0 ht)
  change _ ≤ n*Real.exp (-t)+cubicThetaNonzeroFirstHeat p t at hb
  change (∑' r : CubicThetaZeroFirstRow,cubicThetaPrimitiveHeatTerm p t r.val)+
    (∑' r : CubicThetaNonzeroFirstPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r.val)=
      cubicThetaPrimitiveHeat p t at he
  rw [he] at hb
  change cubicThetaPrimitiveHeat p t ≤ _ at hb
  apply hb.trans
  have hexp : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hzero := mul_le_mul_of_nonneg_left hexp hn
  have hnonzero := hbound p hp t ht
  have ht2 : 0≤t⁻¹^2 := sq_nonneg _
  nlinarith [mul_nonneg hn ht2]

end CubicFirstMoment

end

end OAI
