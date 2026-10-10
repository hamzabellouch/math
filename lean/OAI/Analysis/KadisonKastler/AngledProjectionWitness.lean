import OAI.Analysis.KadisonKastler.SymmetricProjectionWitness

namespace OAI

/-! # Projection witnesses away from the reference line

The orthogonal-vector witness extends to a real unit-circle combination.
The squared sine is kept as a multiplier, so no trigonometric conventions
or division by a small angle enter the subsequent corner argument.
This is the local estimate in Haagerup, Acta Math.158(1987), Lemma2.14.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

omit [CompleteSpace H] in
theorem norm_real_combination_sq_le (x y : H) (c s : ℝ) (hcs : c^2+s^2 ≤ 1) :
    ‖c • x+s • y‖^2 ≤ ‖x‖^2+‖y‖^2 := by
  have hn := norm_add_le (c • x) (s • y)
  simp only [norm_smul,Real.norm_eq_abs] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ |c| * ‖x‖+|s| * ‖y‖)).mpr hn
  have hd := sq_nonneg (|s| * ‖x‖-|c| * ‖y‖)
  have hc := mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖))
  nlinarith only [hs,hd,hc,sq_abs c,sq_abs s]

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem norm_sub_sq_le_two (x y : H) :
    ‖x-y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have hn := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_sub_le x y)
  nlinarith only [hn,sq_nonneg (‖x‖-‖y‖)]

omit [CompleteSpace H] in
theorem real_combination_defect_lower (T : H →L[ℂ] H) (ξ ζ : H) (c s : ℝ)
    (hcs : c^2+s^2 ≤ 1)
    (hsmall : ‖T ξ‖^2 < s^2/8*‖T ζ‖^2) :
    s^2*‖T ζ‖^2 < 4*‖T (c • ξ+s • ζ)‖^2 := by
  have he : s • T ζ = T (c • ξ+s • ζ)-c • T ξ := by
    rw [map_add,ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.map_smul_of_tower]
    abel
  have hn := norm_sub_sq_le_two (T (c • ξ+s • ζ)) (c • T ξ)
  rw [← he] at hn
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hn
  have hcx : c^2*‖T ξ‖^2 ≤ ‖T ξ‖^2 := by
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith only [hcs,sq_nonneg s])
  nlinarith only [hn,hcx,hsmall]

variable [TopologicalSpace.SeparableSpace H]

theorem ModularConjugationData.angled_projection_witness
    (d : ModularConjugationData M Ω) (hM : TypeIIIFactor M)
    (h : HaagerupCommutatorWitnesses d) (hcyc : DenseRange (algebraVectorMap M Ω))
    (ζ : H) (hζ : d.conjugation ζ=ζ) (hunit : ‖ζ‖=1) (horth : inner ℂ Ω ζ=0)
    (c s : ℝ) (hcs : c^2+s^2 ≤ 1) (hs : 0 < s)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      s^2*(‖p.val.val Ω‖^2+‖p.val.val (c • Ω+s • ζ)‖^2) <
        16384*‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        δ*‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖^2 := by
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  obtain ⟨p,hp,hm,hd⟩ := d.symmetric_projection_witness hM h hcyc ζ hζ hunit horth
    (α := s^2/8*min 1 δ)
    (mul_pos (div_pos hs2 (by norm_num : (0 : ℝ)<8)) (lt_min (by norm_num) hδ))
  let T : H →L[ℂ] H := p.val.val-conjugationOperator d.conjugation p.val.val
  have hdΩ : ‖centralVectorDefect d.conjugation Ω p.val.val‖=‖T Ω‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation Ω p)
  have hdζ : ‖centralVectorDefect d.conjugation ζ p.val.val‖=‖T ζ‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation ζ p)
  have hdη : ‖centralVectorDefect d.conjugation (c • Ω+s • ζ) p.val.val‖=
      ‖T (c • Ω+s • ζ)‖ :=
    congrArg norm (centralVectorDefect_projection d.conjugation (c • Ω+s • ζ) p)
  rw [hdΩ,hdζ] at hd
  rw [hdζ] at hm
  have hsmall : ‖T Ω‖^2 < s^2/8*‖T ζ‖^2 := hd.trans_le (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) (min_le_left _ _)) (sq_nonneg _))
  have hsmallδ : ‖T Ω‖^2 < δ*s^2/8*‖T ζ‖^2 := hd.trans_le (by
    calc
      _ ≤ (s^2/8*δ)*‖T ζ‖^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)) (sq_nonneg _)
      _ = _ := by ring)
  have hlower := real_combination_defect_lower T Ω ζ c s hcs hsmall
  have hmass : ‖p.val.val (c • Ω+s • ζ)‖^2 ≤ ‖p.val.val Ω‖^2+‖p.val.val ζ‖^2 := by
    rw [map_add,ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower]
    exact norm_real_combination_sq_le _ _ c s hcs
  refine ⟨p,hp,?_,?_⟩
  · rw [hdη]
    have hmass' : ‖p.val.val Ω‖^2+‖p.val.val (c • Ω+s • ζ)‖^2 < 4096*‖T ζ‖^2 := by
      nlinarith only [hm,hmass,sq_nonneg ‖p.val.val ζ‖]
    have hmuls := mul_lt_mul_of_pos_left hmass' hs2
    nlinarith only [hmuls,hlower]
  · rw [hdΩ,hdη]
    have hmulδ := mul_lt_mul_of_pos_left hlower hδ
    nlinarith only [hsmallδ,hmulδ]

end

end KadisonKastler

end OAI
