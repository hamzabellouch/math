import OAI.Analysis.KadisonKastler.FactorPositiveNorm

namespace OAI

/-! # A commuting positive summand detected by faithful restrictions -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem real_smul_one_mem_vonNeumann (M : VonNeumannAlgebra H) (r : ℝ) :
    r • (1 : H →L[ℂ] H) ∈ M := by
  change r • (1 : H →L[ℂ] H) ∈ M.toStarSubalgebra
  exact (M.toStarSubalgebra.restrictScalars ℝ).smul_mem M.one_mem r

theorem positive_commutant_scalar_of_corner_norm
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (x y : H →L[ℂ] H) (hxM : x ∈ M) (hyM : y ∈ M.commutant)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfaith : ∀ p : AlgebraProjection M.commutant, p.val ≠ 0 →
      Commute p.val.val y →
      ‖cornerCompression (typeIIIInitialSpace p) (x + y)‖ = ‖x + y‖) :
    y = ‖y‖ • 1 := by
  let z := ‖y‖ • (1 : H →L[ℂ] H) - y
  have hz : 0 ≤ z := sub_nonneg.mpr (by
    simpa only [Algebra.algebraMap_eq_smul_one] using hy.isSelfAdjoint.le_algebraMap_norm_self)
  have hzn : ‖z‖ ≤ ‖y‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap z (norm_nonneg y) hz).mpr (by
      simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖y‖ • (1 : H →L[ℂ] H)) hy)
  suffices he : z = 0 by exact (sub_eq_zero.mp he).symm
  by_contra hz0
  let t := ‖z‖ / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (norm_pos_iff.mpr hz0)
  have hty : t ≤ ‖y‖ := by dsimp [t]; linarith [norm_nonneg z]
  let q := upperSpectralCut z t
  have hq : IsStarProjection q := upperSpectralCut_isStarProjection z t
  have hq0 : q ≠ 0 := upperSpectralCut_ne_zero_of_lt_norm z hz t ht.le (by
    dsimp [t]; linarith [norm_pos_iff.mpr hz0])
  have hzM : z ∈ M.commutant := M.commutant.sub_mem
    (real_smul_one_mem_vonNeumann M.commutant ‖y‖) hyM
  have hqM : q ∈ M.commutant := upperSpectralCut_mem M.commutant z hzM t
  let p : AlgebraProjection M.commutant := ⟨⟨q, hqM⟩,
    ⟨Subtype.ext hq.isIdempotentElem.eq, Subtype.ext hq.isSelfAdjoint.star_eq⟩⟩
  have hp0 : p.val ≠ 0 := fun h => hq0 (congrArg Subtype.val h)
  let E := typeIIIInitialSpace p
  let : Nontrivial E := nontrivial_projection_range q hq hq0
  have hEq : q = E.starProjection := typeIIIInitialSpace_projection p
  have hcp : cornerCompression E q = 1 := by
    rw [hEq, ← cornerExtension_one, cornerCompression_extension]
  have hc1 : cornerCompression E (1 : H →L[ℂ] H) = 1 :=
    (commutantReducingHom E M (hEq ▸ hqM)).map_one
  have hqy : Commute p.val.val y := by
    have hh := (upperSpectralCut_commutes_self z hz.isSelfAdjoint t).eq
    change q * (‖y‖ • 1 - y) = (‖y‖ • 1 - y) * q at hh
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at hh
    have he := congrArg (fun w : H →L[ℂ] H => ‖y‖ • q - w) hh
    change q * y = y * q
    simpa only [sub_sub_cancel] using he
  have hupper : cornerCompression E y ≤ (‖y‖ - t) • 1 := by
    have hh := cornerCompression_mono E (smul_upperSpectralCut_le z hz t)
    rw [(cornerCompression E).map_smul_of_tower, hcp] at hh
    change t • (1 : E →L[ℂ] E) ≤ cornerCompression E (‖y‖ • 1 - y) at hh
    rw [map_sub, (cornerCompression E).map_smul_of_tower, hc1] at hh
    have he := le_sub_iff_add_le.mp hh
    have heq : (‖y‖ - t) • (1 : E →L[ℂ] E) = ‖y‖ • 1 - t • 1 := by module
    rw [heq]
    exact le_sub_iff_add_le.mpr
      ((add_comm (cornerCompression E y) (t • (1 : E →L[ℂ] E))).le.trans he)
  have hyn : ‖cornerCompression E y‖ ≤ ‖y‖ - t :=
    (CStarAlgebra.norm_le_iff_le_algebraMap (cornerCompression E y) (sub_nonneg.mpr hty)
      (cornerCompression_nonneg E y hy)).mpr (by
        simpa only [Algebra.algebraMap_eq_smul_one] using hupper)
  have hnorm := hfaith p hp0 hqy
  have hadd := norm_add_positive_factor_commutant M hM x y hxM hyM hx hy
  have hb : ‖cornerCompression E (x + y)‖ ≤ ‖x‖ + (‖y‖ - t) := by
    rw [map_add]
    exact (norm_add_le (cornerCompression E x) (cornerCompression E y)).trans
      (add_le_add (norm_cornerCompression_le E x) hyn)
  rw [hnorm, hadd] at hb
  linarith

end

end KadisonKastler

end OAI
