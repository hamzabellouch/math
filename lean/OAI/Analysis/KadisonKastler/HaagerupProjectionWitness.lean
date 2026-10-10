import OAI.Analysis.KadisonKastler.SelfAdjointVectorWitness
import OAI.Analysis.KadisonKastler.SelfAdjointOutwardCut

namespace OAI

/-! # Projection witnesses from the modular commutator premise

This is the bounded symmetric-vector case of Haagerup's Lemma 2.13.
Both estimates concern a genuine projection in the original algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

private theorem two_vector_energy_bound {L R X D α : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hX : 0 ≤ X) (hα : 0 < α)
    (hsize : L+R < 26*D) (hsmall : X < (α/106496)*D) :
    α*(L^2+R^2)+2*2048*L*X < α*2048/2*D^2 := by
  have hD : 0 < D := by linarith
  have hLD : L ≤ 26*D := by linarith
  have hsq := (sq_lt_sq₀ (add_nonneg hL hR) (by positivity : 0 ≤ 26*D)).mpr hsize
  have hmass : L^2+R^2 < 676*D^2 := by nlinarith [mul_nonneg hL hR]
  have hmassα := mul_lt_mul_of_pos_left hmass hα
  have hLX := mul_le_mul_of_nonneg_right hLD hX
  have hXD := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < 26*D)
  have hterm : 2*2048*L*X < α*D^2 := by nlinarith
  nlinarith [mul_pos hα (sq_pos_of_pos hD)]

theorem exists_projection_of_relative_two_vector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H}
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η)
    (hw : ∀ ε : ℝ, 0 < ε → ∃ a : Algebra M,
      ‖a.val ξ‖+‖a.val η‖ < 12*‖centralVectorDefect J η a.val‖ ∧
      ‖centralVectorDefect J ξ a.val‖ < ε*‖centralVectorDefect J η a.val‖)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < 2048*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  obtain ⟨b,hb,hsize,hsmall⟩ := exists_selfAdjoint_relative_two_vector J hJ ξ η hξ hη hw
    (show 0 < α/106496 by positivity)
  have hDb (ζ : H) : centralVectorDefect J ζ b.val=
      (b.val-conjugationOperator J b.val) ζ := by
    rw [centralVectorDefect_apply,show star b.val=b.val from congrArg Subtype.val hb.star_eq]
    rfl
  apply exists_selfAdjoint_two_vector_projection J hJ hright b hb ξ η hξ hα (by norm_num)
  have he := two_vector_energy_bound (norm_nonneg (b.val ξ)) (norm_nonneg (b.val η))
    (norm_nonneg (centralVectorDefect J ξ b.val)) hα hsize hsmall
  simpa only [hDb] using he

namespace ModularConjugationData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)

theorem symmetric_vector_projection_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val Ω‖^2+‖p.val.val (a.val Ω)‖^2 <
        2048*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 := by
  obtain ⟨b,hb,hsize,hsmall⟩ := d.selfAdjoint_symmetric_vector_witness
    h a hbal hzero hnorm (show 0 < α/106496 by positivity)
  have hDb (ζ : H) : centralVectorDefect d.conjugation ζ b.val=
      (b.val-conjugationOperator d.conjugation b.val) ζ := by
    rw [centralVectorDefect_apply,
      show star b.val=b.val from congrArg Subtype.val hb.star_eq]
    rfl
  apply exists_selfAdjoint_two_vector_projection d.conjugation d.involutive
    (d.right_mem le_rfl) b hb Ω (a.val Ω) d.fixes_vector hα (by norm_num)
  have he := two_vector_energy_bound (norm_nonneg (b.val Ω))
    (norm_nonneg (b.val (a.val Ω)))
    (norm_nonneg (centralVectorDefect d.conjugation Ω b.val)) hα hsize hsmall
  simpa only [hDb] using he

theorem symmetric_vector_nonzero_projection_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ‖p.val.val Ω‖^2+‖p.val.val (a.val Ω)‖^2 <
        2048*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation (a.val Ω) p.val.val‖^2 := by
  obtain ⟨p,hp,hc⟩ := d.symmetric_vector_projection_witness h a hbal hzero hnorm hα
  refine ⟨p,?_,hp,hc⟩
  intro hz
  have hzv : p.val.val=0 := congrArg Subtype.val hz
  have he : (0 : ℝ) < 0 := by simpa only [hzv,map_zero,norm_zero,pow_two,mul_zero] using hc
  exact (lt_irrefl 0) he

end ModularConjugationData

end

end KadisonKastler

end OAI
