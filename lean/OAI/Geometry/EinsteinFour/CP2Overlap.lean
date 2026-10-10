import OAI.Geometry.Manifold.ProjectiveSphere

namespace OAI

/-! Unit representatives and transition probabilities for the actual
Fubini--Study distance on CP2. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

abbrev CP2Vector := EuclideanSpace ℂ (Fin 3)

def cp2UnitRep (p : ComplexProjective2) : CP2Vector :=
  ((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep

theorem cp2UnitRep_norm (p : ComplexProjective2) : ‖cp2UnitRep p‖ = 1 := by
  have hn : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
  simp [cp2UnitRep, norm_smul, Complex.norm_real, hn]

theorem cp2UnitRep_ne_zero (p : ComplexProjective2) : cp2UnitRep p ≠ 0 := by
  intro h
  have hn := cp2UnitRep_norm p
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem cp2UnitRep_mk (p : ComplexProjective2) :
    Projectivization.mk ℂ (cp2UnitRep p) (cp2UnitRep_ne_zero p) = p := by
  conv_rhs => rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨_, rfl⟩

def cp2Overlap (p q : ComplexProjective2) : ℝ :=
  ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖

theorem cp2Overlap_nonneg (p q : ComplexProjective2) : 0 ≤ cp2Overlap p q := norm_nonneg _

theorem cp2Overlap_le_one (p q : ComplexProjective2) : cp2Overlap p q ≤ 1 := by
  simpa only [cp2Overlap, cp2UnitRep_norm, one_mul] using norm_inner_le_norm (cp2UnitRep p) (cp2UnitRep q)

theorem cp2Overlap_eq_ratio (p q : ComplexProjective2) :
    cp2Overlap p q = ‖inner ℂ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖) := by
  have hp : (((‖p.rep‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr p.rep_nonzero)
  have hq : (((‖q.rep‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr q.rep_nonzero)
  have h := normalized_inner_smul p.rep q.rep
    (((‖p.rep‖⁻¹ : ℝ) : ℂ)) (((‖q.rep‖⁻¹ : ℝ) : ℂ)) hp hq
  change ‖inner ℂ (cp2UnitRep p) (cp2UnitRep q)‖ /
    (‖cp2UnitRep p‖ * ‖cp2UnitRep q‖) = _ at h
  simpa only [cp2Overlap, cp2UnitRep_norm, one_mul, div_one] using h


theorem fubiniStudyDistance_eq_arccos (p q : ComplexProjective2) :
    fubiniStudyDistance p q = Real.arccos (cp2Overlap p q) := by
  rw [cp2Overlap_eq_ratio]
  rfl

theorem cp2Overlap_eq_iff_distance_eq (p q r s : ComplexProjective2) :
    cp2Overlap p q = cp2Overlap r s ↔ fubiniStudyDistance p q = fubiniStudyDistance r s := by
  rw [fubiniStudyDistance_eq_arccos, fubiniStudyDistance_eq_arccos]
  constructor
  · exact congrArg Real.arccos
  · exact (Real.strictAntiOn_arccos.injOn
      ⟨(by linarith [cp2Overlap_nonneg p q]), cp2Overlap_le_one p q⟩
      ⟨(by linarith [cp2Overlap_nonneg r s]), cp2Overlap_le_one r s⟩)

theorem cp2Overlap_mk (x y : CP2Vector) (hx : x ≠ 0) (hy : y ≠ 0) :
    cp2Overlap (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) =
      ‖inner ℂ x y‖ / (‖x‖ * ‖y‖) := by
  rw [cp2Overlap_eq_ratio, normalized_inner_mk_rep]

theorem cp2Overlap_comm (p q : ComplexProjective2) : cp2Overlap p q = cp2Overlap q p :=
  norm_inner_symm _ _

@[simp] theorem cp2Overlap_self (p : ComplexProjective2) : cp2Overlap p p = 1 := by
  change ‖inner ℂ (cp2UnitRep p) (cp2UnitRep p)‖ = 1
  rw [inner_self_eq_norm_sq_to_K, cp2UnitRep_norm]
  norm_num

end
end PositiveEinsteinFour

end OAI
