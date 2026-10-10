import OAI.MeasureTheory.Falconer.Incidence.CommonTripleIncidence

namespace OAI

/-! # Selecting a good original triple with common point incidence -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem exists_good_common_triple (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × W)) (hE : MeasurableSet E)
    (B : Set (W × W × W)) (hB : MeasurableSet B)
    (hμ : μ univ ≤ 1) (hν : ν univ ≤ 1) {a : ℝ} (ha : 0 < a)
    (hI : ENNReal.ofReal a ≤ (μ.prod ν) E)
    (hbad : (ν.prod (ν.prod ν)) B ≤ ENNReal.ofReal (a^3/4)) :
    ∃ w ∉ B, ENNReal.ofReal (a^3/2) < μ {x | (x,w) ∈ commonTripleRelation E} := by
  classical
  let ξ := ν.prod (ν.prod ν)
  let F := commonTripleRelation E ∩ (univ ×ˢ Bᶜ)
  have hF : MeasurableSet F := (commonTripleRelation_measurable E hE).inter
    (MeasurableSet.univ.prod hB.compl)
  have hξ : ξ univ ≤ 1 := by
    simp only [ξ,← univ_prod_univ,Measure.prod_prod]
    exact (mul_le_mul' hν (mul_le_mul' hν hν)).trans_eq (by simp)
  have hμ2 : (μ univ)^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left' hμ 2
  have hlo : ENNReal.ofReal (a^3) ≤ (μ.prod ξ) (commonTripleRelation E) := by
    rw [ENNReal.ofReal_pow ha.le]
    exact (pow_le_pow_left' hI 3).trans ((common_triple_incidence_moment μ ν E hE).trans
      (by simpa only [mul_one] using mul_le_mul' le_rfl hμ2))
  by_contra! hn
  have hfiber (w : W × W × W) : μ ((fun x => (x,w)) ⁻¹' F) ≤ ENNReal.ofReal (a^3/2) := by
    by_cases hw : w ∈ B
    · have he : (fun x => (x,w)) ⁻¹' F = ∅ := by
        ext x
        simp only [F,mem_preimage,mem_inter_iff,mem_prod,mem_univ,mem_compl_iff,hw,
          not_true_eq_false,and_false,mem_empty_iff_false]
      simp only [he,measure_empty,zero_le]
    · exact (measure_mono (fun _ hx => hx.1)).trans (hn w hw)
  have hgood : (μ.prod ξ) F ≤ ENNReal.ofReal (a^3/2) := by
    rw [Measure.prod_apply_symm hF]
    calc
      _ ≤ ∫⁻ _w, ENNReal.ofReal (a^3/2) ∂ξ := lintegral_mono hfiber
      _ = ENNReal.ofReal (a^3/2)*ξ univ := by rw [lintegral_const,mul_comm]
      _ ≤ ENNReal.ofReal (a^3/2) := by simpa only [mul_one] using mul_le_mul' le_rfl hξ
  have hsub : commonTripleRelation E ⊆ F ∪ (univ ×ˢ B) := by
    intro p hp
    by_cases hb : p.2 ∈ B
    · exact Or.inr ⟨mem_univ _,hb⟩
    · exact Or.inl ⟨hp,mem_univ _,hb⟩
  have hu : (μ.prod ξ) (commonTripleRelation E) ≤
      ENNReal.ofReal (a^3/2)+ENNReal.ofReal (a^3/4) := by
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    apply add_le_add hgood
    rw [Measure.prod_prod]
    exact (mul_le_mul' hμ hbad).trans_eq (one_mul _)
  have hlt : ENNReal.ofReal (a^3/2)+ENNReal.ofReal (a^3/4) < ENNReal.ofReal (a^3) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    nlinarith [pow_pos ha 3]
  exact (not_lt_of_ge (hlo.trans hu)) hlt

end Falconer

end OAI
