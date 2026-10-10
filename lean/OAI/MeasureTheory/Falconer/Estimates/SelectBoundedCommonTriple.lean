import OAI.MeasureTheory.Falconer.Estimates.SelectCommonTriple

namespace OAI

/-! # A good original triple for slice laws of bounded, unnormalized mass -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem exists_good_common_triple_bounded (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × W)) (hE : MeasurableSet E)
    (B : Set (W × W × W)) (hB : MeasurableSet B)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hμ : μ univ ≤ ENNReal.ofReal M) (hν : ν univ ≤ ENNReal.ofReal M)
    (hI : ENNReal.ofReal a ≤ (μ.prod ν) E)
    (hbad : (ν.prod (ν.prod ν)) B ≤ ENNReal.ofReal (a^3/(4*M^3))) :
    ∃ w ∉ B, ENNReal.ofReal (a^3/(2*M^5)) < μ {x | (x,w) ∈ commonTripleRelation E} := by
  let ξ := ν.prod (ν.prod ν)
  let F := commonTripleRelation E ∩ (univ ×ˢ Bᶜ)
  have hF : MeasurableSet F := (commonTripleRelation_measurable E hE).inter
    (MeasurableSet.univ.prod hB.compl)
  have hξ : ξ univ ≤ ENNReal.ofReal (M^3) := by
    simp only [ξ,← univ_prod_univ,Measure.prod_prod]
    calc
      _ ≤ ENNReal.ofReal M*(ENNReal.ofReal M*ENNReal.ofReal M) := mul_le_mul' hν (mul_le_mul' hν hν)
      _ = _ := by rw [ENNReal.ofReal_pow hM.le]; ring
  by_contra! hn
  have hfiber (w : W × W × W) : μ ((fun x => (x,w)) ⁻¹' F) ≤ ENNReal.ofReal (a^3/(2*M^5)) := by
    by_cases hw : w ∈ B
    · have he : (fun x => (x,w)) ⁻¹' F = ∅ := by
        ext x
        simp only [F,mem_preimage,mem_inter_iff,mem_prod,mem_univ,mem_compl_iff,hw,
          not_true_eq_false,and_false,mem_empty_iff_false]
      simp only [he,measure_empty,zero_le]
    · exact (measure_mono (fun _ hx => hx.1)).trans (hn w hw)
  have hgood : (μ.prod ξ) F ≤ ENNReal.ofReal ((a^3/(2*M^5))*M^3) := by
    rw [Measure.prod_apply_symm hF]
    calc
      _ ≤ ∫⁻ _w, ENNReal.ofReal (a^3/(2*M^5)) ∂ξ := lintegral_mono hfiber
      _ = ENNReal.ofReal (a^3/(2*M^5))*ξ univ := by rw [lintegral_const,mul_comm]
      _ ≤ ENNReal.ofReal (a^3/(2*M^5))*ENNReal.ofReal (M^3) := mul_le_mul' le_rfl hξ
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hsub : commonTripleRelation E ⊆ F ∪ (univ ×ˢ B) := by
    intro p hp
    by_cases hb : p.2 ∈ B
    · exact Or.inr ⟨mem_univ _,hb⟩
    · exact Or.inl ⟨hp,mem_univ _,hb⟩
  have htotal : (μ.prod ξ) (commonTripleRelation E) ≤
      ENNReal.ofReal ((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3))) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    apply add_le_add hgood
    rw [Measure.prod_prod]
    exact (mul_le_mul' hμ hbad).trans_eq (ENNReal.ofReal_mul hM.le).symm
  have hmain : ENNReal.ofReal (a^3) ≤
      ENNReal.ofReal (((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3)))*M^2) := by
    rw [ENNReal.ofReal_pow ha.le]
    apply (pow_le_pow_left' hI 3).trans
    apply (common_triple_incidence_moment μ ν E hE).trans
    apply (mul_le_mul' htotal (pow_le_pow_left' hμ 2)).trans_eq
    rw [← ENNReal.ofReal_pow hM.le,← ENNReal.ofReal_mul (by positivity)]
  have heq : ((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3)))*M^2 = 3*a^3/4 := by
    field_simp
    ring
  rw [heq] at hmain
  have hlt : ENNReal.ofReal (3*a^3/4) < ENNReal.ofReal (a^3) :=
    ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by nlinarith [pow_pos ha 3])
  exact (not_lt_of_ge hmain) hlt

end Falconer

end OAI
