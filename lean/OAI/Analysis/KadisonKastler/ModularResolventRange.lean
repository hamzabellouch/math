import OAI.Analysis.KadisonKastler.ModularPairingComplexification
import OAI.Analysis.KadisonKastler.ModularRadonSelfAdjoint
import OAI.Analysis.KadisonKastler.TomitaCentralizerGraph

namespace OAI

/-! # The bounded Tomita resolvent takes commutant vectors into the algebra

The real Radon--Nikodym equation identifies the orthogonal projection of a
commutant vector into the closed Tomita graph. Its first coordinate is the
already constructed bounded resolvent.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem rescaledGraphProjection_of_modular_pairing (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (b : H →L[ℂ] H) (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (x : Algebra M) (hx : IsSelfAdjoint x)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re = (inner ℂ (a.val.val Ω) (x.val Ω)).re) :
    rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 (b Ω)) =
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 x.val := by
  have hcomplex := modular_pairing_complex Ω b hb hbs 1 x (by simpa using hpair)
  let K := rescaledGraphSubspace M J Ω 1
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact K.smul_mem _ (rescaledGraphVector_mem M J Ω 1 x)
  · intro v hv
    have hc : IsClosed {w : TomitaGraphHilbert H |
        inner ℂ (Generator.tupleSingle 0 (b Ω) -
          (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 x.val) w = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_ hc hv
    rintro _ ⟨a, rfl⟩
    have hba : inner ℂ Ω (a.val (b Ω)) = inner ℂ (b Ω) (a.val Ω) := by
      have hab : a.val * b = b * a.val := hb _ (Set.mem_union_left _ a.property)
      have hs : b.adjoint = b := hbs.star_eq
      rw [← ContinuousLinearMap.adjoint_inner_right, hs]
      exact congrArg (fun T : H →L[ℂ] H => inner ℂ Ω (T Ω)) hab
    have hxa : inner ℂ (J (star x.val Ω)) (J (star a.val Ω)) =
        inner ℂ Ω (a.val (x.val Ω)) := by
      have hs : star x.val = x.val := congrArg Subtype.val hx.star_eq
      rw [hs, conjugateIsometry_inner]
      change (starRingEnd ℂ) (inner ℂ (x.val Ω) (star a.val Ω)) = _
      rw [inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have he := hcomplex a
    simp only [one_mul, star_one] at he
    rw [hba, ← hxa] at he
    change inner ℂ (Generator.tupleSingle 0 (b Ω) -
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 x.val) (rescaledGraphVector J Ω 1 a.val) = 0
    simp only [inner_sub_left, inner_smul_left, PiLp.inner_apply, Fin.sum_univ_two,
      Generator.tupleSingle_apply, Pi.single_apply, Fin.isValue, ↓reduceIte,
      rescaledGraphVector_zero, rescaledGraphVector_one, one_smul]
    have hhalf : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
      change star (1 / 2 : ℂ) = _
      simp
    simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false,
      inner_zero_left, add_zero, hhalf]
    linear_combination (1 / 2 : ℂ) * he

/-- A self-adjoint commutant vector has an actual bounded algebra representative
under the graph resolvent. No modular normalization is used. -/
theorem graphResolvent_commutant_selfAdjoint (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (b : Algebra M.commutant) (hb : IsSelfAdjoint b) :
    ∃ a : Algebra M, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 + ‖b‖ ∧
      graphResolvent M J Ω 1 (b.val Ω) = a.val Ω := by
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_selfAdjoint Ω b hb 1 (by norm_num)
  let a : Algebra M := (1 / 2 : ℝ) • x
  have ha : IsSelfAdjoint a := by
    change star ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) • x
    rw [star_smul, star_trivial, hx.star_eq]
  refine ⟨a, ha, ?_, ?_⟩
  · change ‖(1 / 2 : ℝ) • x‖ ≤ 1 + ‖b‖
    rw [norm_smul]
    norm_num at hxn ⊢
    linarith
  · have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
      (rescaledGraphProjection_of_modular_pairing J Ω b.val b.property
        (congrArg Subtype.val hb.star_eq) x hx (by simpa using hxp))
    change graphResolvent M J Ω 1 (b.val Ω) = (1 / 2 : ℂ) • x.val Ω at h
    change graphResolvent M J Ω 1 (b.val Ω) = (1 / 2 : ℝ) • x.val Ω
    rw [← Complex.coe_smul]
    convert h using 1
    norm_num

end

end KadisonKastler

end OAI
