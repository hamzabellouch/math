import OAI.NumberTheory.DirichletL.Hecke.Euler

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

def modulus (q : ℕ) : Ideal O := Ideal.span {(q : O)}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

theorem quotient_modulus_zero : (q : O ⧸ modulus q) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (modulus q))]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem norm_span_dvd (z : O) :
    z ∣ (Ideal.absNorm (Ideal.span {z}) : O) := by
  have h : (Ideal.absNorm (Ideal.span {z}) : ℤ) =
      ShortDraftLatticeCount.q (ActualEisensteinCoordinates.coords z) := by
    rw [← ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg z)
  rw [← Int.cast_natCast, h]
  exact ⟨_, ActualEisensteinCubic.coordinate_norm_eq_mul_conjO z⟩

theorem quotient_unit_of_norm_unit (z : O)
    (hz : IsUnit (Ideal.absNorm (Ideal.span {z}) : ZMod q)) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) := by
  have hc := (ZMod.isUnit_iff_coprime _ _).mp hz
  have hi : IsCoprime (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) (q : O ⧸ modulus q) := by
    simpa only [map_natCast] using hc.isCoprime.map (Int.castRingHom (O ⧸ modulus q))
  rw [quotient_modulus_zero, isCoprime_zero_right] at hi
  obtain ⟨w, hw⟩ := norm_span_dvd z
  have hn : (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) =
      Ideal.Quotient.mk (modulus q) z * Ideal.Quotient.mk (modulus q) w := by
    rw [← map_mul, ← hw, map_natCast]
  rw [hn] at hi
  exact isUnit_of_mul_isUnit_left hi

def residue (χ : DirichletCharacter ℂ q) : MulChar (O ⧸ modulus q) ℂ where
  toFun x := Quotient.liftOn' x (InitialMeanSquare.normCharacter χ) (by
    intro a b hab
    exact CanonicalCoefficientClass.normCharacter_factorsModulo χ a b
      ((modulus q).quotientRel_def.mp hab))
  map_one' := (InitialMeanSquare.normCharacter χ).map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact (InitialMeanSquare.normCharacter χ).map_mul a b
  map_nonunit' x hx := by
    refine Quotient.inductionOn' x (fun z hz => ?_) hx
    change χ (Ideal.absNorm (Ideal.span {z})) = 0
    apply MulChar.map_nonunit
    exact fun h => hz (quotient_unit_of_norm_unit z h)

@[simp] theorem residue_mk (χ : DirichletCharacter ℂ q) (z : O) :
    residue χ (Ideal.Quotient.mk (modulus q) z) = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem residue_unit_trivial (χ : DirichletCharacter ℂ q) (u : Oˣ) :
    residue χ (Ideal.Quotient.mk (modulus q) (u : O)) = 1 := by
  rw [residue_mk, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
  simp

variable [NeZero q]

def character (χ : DirichletCharacter ℂ q) : Character :=
  Character.ofResidue (modulus q) modulus_ne_bot (residue χ) (residue_unit_trivial χ)

@[simp] theorem elementCoeff_character (χ : DirichletCharacter ℂ q) (z : O) :
    elementCoeff (character χ) z = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) (hI : I ≠ 0) :
    idealCoeff (character χ) I = χ (Ideal.absNorm I) := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I]
  rw [idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
    elementCoeff_character, ConcretePrimeRowBridge.span_idealGenerator]

theorem moebius_idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff (character χ) I =
      ShortDraftHeckeBridge.baseChangeWeight χ I := by
  by_cases hI : I = 0
  · subst I
    unfold ShortDraftHeckeBridge.baseChangeWeight
    rw [UniqueFactorizationMonoid.moebius_zero]
    simp
  · rw [idealCoeff_character χ I hI]
    rfl

theorem inverseSeries_eq_pairInverse_LSeries (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff (character χ)) s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ (ShortDraftHeckeBridge.baseChangeChar χ)) s := by
  rw [IdealEuler.inverseSeries]
  have ht (I : Ideal O) : (UniqueFactorizationMonoid.moebius I : ℂ) *
      IdealEuler.weighted (idealCoeff (character χ)) s I =
      ShortDraftHeckeBridge.baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I := by
    change (UniqueFactorizationMonoid.moebius I : ℂ) *
      (idealCoeff (character χ) I * CubicEisenstein.fullIdealWeight s I) = _
    rw [← mul_assoc, moebius_idealCoeff_character]
  simp_rw [ht]
  rw [SmoothMobiusCorrection.idealDirichlet_eq_LSeries _
    (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ) s hs]
  exact ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ
    (ShortDraftHeckeBridge.baseChangeChar χ) _
    (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s

theorem LFunction_eq_dirichlet_product_right (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  have hH := inverseSeries_mul_LFunction (character χ) hs
  have hD := ShortDraftHeckeBridge.pair_inverse_euler_identity χ
    (ShortDraftHeckeBridge.baseChangeChar χ) s hs
  rw [inverseSeries_eq_pairInverse_LSeries χ hs] at hH
  have hne : LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ
      (ShortDraftHeckeBridge.baseChangeChar χ)) s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hH
    exact zero_ne_one hH
  apply mul_left_cancel₀ hne
  rw [hH, mul_comm, hD]

theorem LFunction_eq_dirichlet_product (χ : DirichletCharacter ℂ q)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  let U : Set ℂ := {0,1}ᶜ
  have hU : IsOpen U := (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    ((Set.toFinite ({0,1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hmem : s ∈ U := by simp [U, h0, h1]
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := LFunction (character χ))
    (g := fun z => χ.LFunction z * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction z)
    _ _ hpc htwo _ hmem
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (LFunction_differentiableAt _ hz'.1 (Or.inl hz'.2)).differentiableWithinAt
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 1 := by simp only [U, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz; exact hz.2
    exact ((χ.differentiableAt_LFunction z (Or.inl hz')).mul
      ((ShortDraftHeckeBridge.baseChangeChar χ).differentiableAt_LFunction z
        (Or.inl hz'))).differentiableWithinAt
  · filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_dirichlet_product_right χ hz

theorem dirichlet_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_seven_eighths_of_hecke hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet

end

end OAI
