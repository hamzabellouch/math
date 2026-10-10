import OAI.Analysis.KadisonKastler.AngledProjectionWitness

namespace OAI

/-! # Orthogonal decomposition of two symmetric unit vectors -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

omit [CompleteSpace H] in
theorem conjugateIsometry_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (r : ℝ) (ξ : H) :
    J (r • ξ)=r • J ξ := by
  change J ((r : ℂ) • ξ)=(r : ℂ) • J ξ
  rw [J.map_smulₛₗ,Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem symmetric_inner_real (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H)
    (hξ : J ξ=ξ) (hη : J η=η) :
    inner ℂ ξ η=((inner ℂ ξ η).re : ℂ) := by
  have he := conjugateIsometry_inner J ξ η
  rw [hξ,hη] at he
  have hi := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

omit [CompleteSpace H] in
theorem symmetric_unit_angle_decomposition (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H)
    (hξ : J ξ=ξ) (hη : J η=η) (huξ : ‖ξ‖=1) (huη : ‖η‖=1)
    (hne : η ≠ ξ) (hne' : η ≠ -ξ) :
    ∃ (c s : ℝ) (ζ : H), c=(inner ℂ ξ η).re ∧ 0 < s ∧ c^2+s^2=1 ∧
      J ζ=ζ ∧ ‖ζ‖=1 ∧ inner ℂ ξ ζ=0 ∧ η=c • ξ+s • ζ := by
  let c := (inner ℂ ξ η).re
  let z := η-c • ξ
  have hi : inner ℂ ξ z=0 := by
    change inner ℂ ξ (η-(c : ℂ) • ξ)=0
    rw [inner_sub_right,inner_smul_right,symmetric_inner_real J ξ η hξ hη,
      inner_self_eq_norm_sq_to_K,huξ]
    norm_num [c]
  have hzJ : J z=z := by
    dsimp only [z]
    rw [map_sub,conjugateIsometry_real_smul,hη,hξ]
  have hdecomp : η=c • ξ+z := by dsimp only [z]; abel
  have hin : inner ℂ (c • ξ) z=0 := by
    change inner ℂ ((c : ℂ) • ξ) z=0
    rw [inner_smul_left,hi,mul_zero]
  have hsq : ‖c • ξ+z‖^2=‖c • ξ‖^2+‖z‖^2 := by
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • ξ) z hin
  rw [← hdecomp,huη,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,huξ] at hsq
  have hz : z ≠ 0 := by
    intro hz
    have hc : c^2=1^2 := by simpa only [hz,norm_zero,zero_pow (by decide : 2≠0),
      one_pow,mul_one,add_zero] using hsq.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hc with hc | hc
    · apply hne
      simpa only [hc,one_smul,hz,add_zero] using hdecomp
    · apply hne'
      simpa only [hc,neg_smul,one_smul,hz,add_zero] using hdecomp
  let s := ‖z‖
  have hs : 0 < s := norm_pos_iff.mpr hz
  let ζ := s⁻¹ • z
  have hsz : s • ζ=z := by
    dsimp only [ζ]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  refine ⟨c,s,ζ,rfl,hs,?_,?_,?_,?_,?_⟩
  · change c^2+‖z‖^2=1
    nlinarith only [hsq]
  · dsimp only [ζ]
    rw [conjugateIsometry_real_smul,hzJ]
  · dsimp only [ζ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    exact inv_mul_cancel₀ hs.ne'
  · change inner ℂ ξ ((s⁻¹ : ℝ) • z)=0
    change inner ℂ ξ (((s⁻¹ : ℝ) : ℂ) • z)=0
    rw [inner_smul_right,hi,mul_zero]
  · rw [hsz]
    exact hdecomp

variable [TopologicalSpace.SeparableSpace H]

theorem ModularConjugationData.noncollinear_projection_witness
    (d : ModularConjugationData M Ω) (hM : TypeIIIFactor M)
    (h : HaagerupCommutatorWitnesses d) (hcyc : DenseRange (algebraVectorMap M Ω))
    (hΩ : ‖Ω‖=1) (η : H) (hη : d.conjugation η=η) (hunit : ‖η‖=1)
    (hne : η ≠ Ω) (hne' : η ≠ -Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      (1-(inner ℂ Ω η).re^2)*(‖p.val.val Ω‖^2+‖p.val.val η‖^2) <
        16384*‖centralVectorDefect d.conjugation η p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        δ*‖centralVectorDefect d.conjugation η p.val.val‖^2 := by
  obtain ⟨c,s,ζ,hc,hs,hcs,hJζ,huζ,horth,he⟩ :=
    symmetric_unit_angle_decomposition d.conjugation Ω η d.fixes_vector hη hΩ hunit hne hne'
  obtain ⟨p,hp,hm,hd⟩ := d.angled_projection_witness hM h hcyc ζ hJζ huζ horth
    c s hcs.le hs hδ
  have hs2 : s^2=1-(inner ℂ Ω η).re^2 := by rw [hc] at hcs; linarith
  rw [← he,hs2] at hm
  rw [← he] at hd
  exact ⟨p,hp,hm,hd⟩

end

end KadisonKastler

end OAI
