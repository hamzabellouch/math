import OAI.Geometry.EinsteinFour.CP2PairUniqueness

namespace OAI

/-! The unit representatives needed for the projective fixed-point argument. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

theorem cp2Overlap_of_unit_representatives (p q : ComplexProjective2)
    (x y : CP2Vector) (hx : x ≠ 0) (hy : y ≠ 0)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1)
    (hpx : Projectivization.mk ℂ x hx = p) (hqy : Projectivization.mk ℂ y hy = q) :
    cp2Overlap p q = ‖inner ℂ x y‖ := by
  rw [← hpx, ← hqy, cp2Overlap_mk, hnx, hny, one_mul, div_one]

theorem cp2Overlap_eq_one_iff (p q : ComplexProjective2) :
    cp2Overlap p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hCS : ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖ =
        ‖cp2UnitRep p‖ * ‖cp2UnitRep q‖ := by
      simpa only [cp2Overlap, cp2UnitRep_norm, one_mul] using h
    obtain ⟨a, _, ha⟩ :=
      (norm_inner_eq_norm_iff (cp2UnitRep_ne_zero p) (cp2UnitRep_ne_zero q)).mp hCS
    rw [← cp2UnitRep_mk p, ← cp2UnitRep_mk q]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨a⁻¹, by rw [ha, smul_smul]; simp_all⟩
  · rintro rfl
    exact cp2Overlap_self p

theorem cp2_unit_aligned (p q : ComplexProjective2) (h : 0 < cp2Overlap p q) :
    ∃ v : CP2Vector, ∃ hv : v ≠ 0,
      ‖v‖ = 1 ∧ Projectivization.mk ℂ v hv = q ∧
      inner ℂ (cp2UnitRep p) v = (cp2Overlap p q : ℂ) := by
  let z := inner ℂ (cp2UnitRep p) (cp2UnitRep q)
  have hz : z ≠ 0 := by
    intro hz
    change 0 < ‖z‖ at h
    rw [hz, norm_zero] at h
    exact (lt_irrefl 0) h
  let a : ℂ := (‖z‖ : ℂ) / z
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hz)) hz
  have han : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, norm_ne_zero_iff.mpr hz]
  let v : CP2Vector := a • cp2UnitRep q
  have hv : v ≠ 0 := smul_ne_zero ha (cp2UnitRep_ne_zero q)
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · simp only [v, norm_smul, han, cp2UnitRep_norm, mul_one]
  · rw [← cp2UnitRep_mk q]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩
  · change inner ℂ (cp2UnitRep p) (a • cp2UnitRep q) = (‖z‖ : ℂ)
    rw [inner_smul_right]
    change ((‖z‖ : ℂ) / z) * z = _
    exact div_mul_cancel₀ _ hz

theorem cp2_aligned_center (p q : CP2Vector) (c : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hc : inner ℂ p q = (c : ℂ))
    (hc0 : 0 < c) :
    ∃ u : CP2Vector, ‖u‖ = 1 ∧
      ‖inner ℂ p u‖ ^ 2 + ‖inner ℂ q u‖ ^ 2 = 1 + c := by
  have hqp : inner ℂ q p = (c : ℂ) := by rw [← inner_conj_symm, hc]; simp
  have hs : ‖p + q‖ ^ 2 = 2 + 2 * c := by
    rw [norm_add_sq (𝕜 := ℂ), hp, hq, hc]
    simp
    ring
  have hn : ‖p + q‖ ≠ 0 := by intro h; rw [h] at hs; nlinarith
  let u : CP2Vector := ((‖p + q‖⁻¹ : ℝ) : ℂ) • (p + q)
  have hpi : inner ℂ p (p + q) = ((1 + c : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hp, hc]
  have hqi : inner ℂ q (p + q) = ((1 + c : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hq, hqp, add_comm]
  have hpn : ‖inner ℂ p u‖ = ‖p + q‖⁻¹ * (1 + c) := by
    simp only [u, inner_smul_right, hpi, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      Real.norm_of_nonneg (by linarith)]
  have hqn : ‖inner ℂ q u‖ = ‖p + q‖⁻¹ * (1 + c) := by
    simp only [u, inner_smul_right, hqi, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      Real.norm_of_nonneg (by linarith)]
  refine ⟨u, ?_, ?_⟩
  · simp only [u, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  · rw [hpn, hqn]
    field_simp
    nlinarith

end
end PositiveEinsteinFour

end OAI
