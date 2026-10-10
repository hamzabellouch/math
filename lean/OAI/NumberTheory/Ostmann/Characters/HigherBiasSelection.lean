import OAI.NumberTheory.Ostmann.Characters.CharacterMaximum

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

theorem exists_positive_phase (u:ℂ) (hu:u≠0) :
    ∃ z:ℂ, ‖z‖=1 ∧ z*u=(‖u‖:ℂ) := by
  have hn : ‖u‖≠0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨conj u/(‖u‖:ℂ),?_,?_⟩
  · rw [norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),div_self hn]
  · rw [div_mul_eq_mul_div,Complex.conj_mul']
    field_simp

theorem exists_character_of_le_higherBias {p:ℕ} [Fact p.Prime]
    (S:Finset (ZMod p)) (δ:ℝ) (hδ:0<δ) (h:δ≤(higherBias S:ℝ)) :
    ∃ χ:MulChar (ZMod p) ℂ, ∃ a:ZMod p,
      2<orderOf χ ∧ δ≤translatedBias S χ a := by
  classical
  obtain ⟨⟨χ,a⟩,_,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun z:MulChar (ZMod p) ℂ×ZMod p=>if 2<orderOf z.1 then ‖translatedMean S z.1 z.2‖₊ else 0)
  by_cases hc:2<orderOf χ
  · refine ⟨χ,a,hc,?_⟩
    have hh : higherBias S=‖translatedMean S χ a‖₊ := by simpa only [higherBias, ite_eq_left hc] using he
    simpa only [hh, translatedBias, coe_nnnorm] using h
  · have hh : higherBias S=0 := by simpa only [higherBias, ite_eq_right hc] using he
    rw [hh,NNReal.coe_zero] at h
    exact False.elim ((not_le_of_gt hδ) h)

theorem exists_positive_character_test {p:ℕ} [Fact p.Prime]
    (S:Finset (ZMod p)) (δ:ℝ) (hδ:0<δ) (h:δ≤(higherBias S:ℝ)) :
    ∃ χ:MulChar (ZMod p) ℂ, ∃ a:ZMod p, ∃ z:ℂ,
      2<orderOf χ ∧ ‖z‖=1 ∧
      (∀x:ZMod p,‖z*χ (x-a)‖≤1) ∧
      δ≤((S.card:ℂ)⁻¹*∑x∈S,z*χ (x-a)).re := by
  obtain ⟨χ,a,hχ,hm⟩ := exists_character_of_le_higherBias S δ hδ h
  have hmean : translatedMean S χ a≠0 := norm_pos_iff.mp (hδ.trans_le hm)
  obtain ⟨z,hz,he⟩ := exists_positive_phase _ hmean
  refine ⟨χ,a,z,hχ,hz,?_,?_⟩
  · intro x
    rw [norm_mul,hz,one_mul]
    exact norm_character_le_one χ _
  · have heq : (S.card:ℂ)⁻¹*∑x∈S,z*χ (x-a)=z*translatedMean S χ a := by
      rw [← Finset.mul_sum]
      unfold translatedMean
      ring
    rw [heq,he,Complex.ofReal_re]
    exact hm

theorem weighted_high_bias_mass {ι:Type*} (S:Finset ι) (w b:ι→ℝ)
    (hw:∀i∈S,0≤w i) (hb:∀i∈S,b i≤1) (δ:ℝ) (hδ:0≤δ) :
    (∑i∈S,w i*b i)-δ*(∑i∈S,w i) ≤ ∑i∈S.filter (fun i=>δ≤b i),w i := by
  classical
  rw [Finset.sum_filter,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h:δ≤b i
  · rw [ite_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left (hb i hi) (hw i hi),mul_nonneg hδ (hw i hi)]
  · rw [ite_eq_right h]
    nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge h) (hw i hi)]

end Ostmann.Characters

end

end OAI
