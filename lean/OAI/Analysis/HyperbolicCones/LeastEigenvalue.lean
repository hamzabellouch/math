import OAI.Analysis.HyperbolicCones.MaxEigenvalue

namespace OAI

/-! The least spectral value and its continuity in the real symmetric matrix space. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

def leastEigenvalue {n : ℕ} (H : Sym n) : ℝ :=
  ‖(H : Mat n ℝ)‖ - ‖‖(H : Mat n ℝ)‖ • (1 : Mat n ℝ) - (H : Mat n ℝ)‖

theorem leastEigenvalue_isLeast {n : ℕ} [NeZero n] (H : Sym n) :
    IsLeast (spectrum ℝ (H : Mat n ℝ)) (leastEigenvalue H) := by
  let A : Mat n ℝ := H
  let B : Mat n ℝ := ‖A‖ • 1 - A
  have hB : B.PosSemidef := by
    apply (posSemidef_scalar_sub_iff A H.property ‖A‖).mpr
    intro x hx
    exact (le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx)
  have hshift : cfc (fun x : ℝ => ‖A‖ - x) A = B := by
    simpa only [A, B, neg_one_mul, neg_one_smul, sub_eq_add_neg] using matrix_cfc_affine H ‖A‖ (-1)
  have hspec : spectrum ℝ B = (fun x : ℝ => ‖A‖ - x) '' spectrum ℝ A := by
    have h := cfc_map_spectrum (fun x : ℝ => ‖A‖ - x) A H.property
      (A.finite_real_spectrum.continuousOn _)
    rwa [hshift] at h
  have hg := posSemidef_norm_isGreatest B hB
  constructor
  · have hm := hg.1
    rw [hspec] at hm
    obtain ⟨x, hx, heq⟩ := hm
    have hm : leastEigenvalue H = x := by
      change ‖A‖ - ‖B‖ = x
      linarith
    simpa only [hm] using hx
  · intro x hx
    have hb : ‖A‖ - x ≤ ‖B‖ := hg.2 (hspec.symm ▸ ⟨x, hx, rfl⟩)
    change ‖A‖ - ‖B‖ ≤ x
    linarith

theorem leastEigenvalue_nonneg_iff {n : ℕ} [NeZero n] (H : Sym n) :
    0 ≤ leastEigenvalue H ↔ (H : Mat n ℝ).PosSemidef := by
  constructor
  · intro h
    apply Matrix.nonneg_iff_posSemidef.mp
    apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (p := IsSelfAdjoint)
      (H : Mat n ℝ) H.property).mpr
    intro x hx
    exact h.trans ((leastEigenvalue_isLeast H).2 hx)
  · intro h
    exact spectrum_nonneg_of_nonneg h.nonneg (leastEigenvalue_isLeast H).1

theorem leastEigenvalue_neg_iff {n : ℕ} [NeZero n] (H : Sym n) :
    leastEigenvalue H < 0 ↔ ¬(H : Mat n ℝ).PosSemidef := by
  rw [← not_le, leastEigenvalue_nonneg_iff]

theorem continuous_leastEigenvalue (n : ℕ) : Continuous (@leastEigenvalue n) := by
  unfold leastEigenvalue
  exact continuous_subtype_val.norm.sub
    ((continuous_subtype_val.norm.smul continuous_const).sub continuous_subtype_val).norm

theorem leastEigenvalue_tendsto {n : ℕ} {T : Type u} {L : Filter T}
    {H : T → Sym n} {H₀ : Sym n} (hH : Tendsto H L (𝓝 H₀)) :
    Tendsto (fun t => leastEigenvalue (H t)) L (𝓝 (leastEigenvalue H₀)) :=
  (continuous_leastEigenvalue n).continuousAt.tendsto.comp hH

theorem leastEigenvalue_pos_iff {n : ℕ} [NeZero n] (H : Sym n) :
    0 < leastEigenvalue H ↔ (H : Mat n ℝ).PosDef := by
  constructor
  · intro h
    have hH : (H : Mat n ℝ).IsHermitian := H.property
    apply hH.posDef_iff_eigenvalues_pos.mpr
    intro i
    apply h.trans_le ((leastEigenvalue_isLeast H).2 ?_)
    rw [hH.spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩
  · intro h
    exact posDef_real_spectrum_positive h (leastEigenvalue_isLeast H).1

theorem det_eq_zero_of_leastEigenvalue_eq_zero {n : ℕ} [NeZero n]
    (H : Sym n) (h : leastEigenvalue H = 0) : Matrix.det (H : Mat n ℝ) = 0 := by
  have hz : (0 : ℝ) ∈ spectrum ℝ (H : Mat n ℝ) := by
    simpa only [h] using (leastEigenvalue_isLeast H).1
  have hi := spectrum.not_isUnit_of_zero_mem ℝ hz
  simpa only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using hi

theorem exists_positive_singular_on_segment {n : ℕ} [NeZero n]
    (F : ℝ → Sym n) (T : ℝ) (hT : 0 < T)
    (hF : ContinuousOn F (Set.Icc 0 T))
    (hzero : ¬(F 0 : Mat n ℝ).PosSemidef) (hend : (F T : Mat n ℝ).PosDef) :
    ∃ t ∈ Set.Ioo 0 T, Matrix.det (F t : Mat n ℝ) = 0 := by
  have hneg : leastEigenvalue (F 0) < 0 := (leastEigenvalue_neg_iff _).mpr hzero
  have hpos : 0 < leastEigenvalue (F T) := (leastEigenvalue_pos_iff _).mpr hend
  have hcont : ContinuousOn (fun t => leastEigenvalue (F t)) (Set.Icc 0 T) :=
    (continuous_leastEigenvalue n).comp_continuousOn hF
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hT.le hcont ⟨hneg.le, hpos.le⟩
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    linarith
  have htT : t ≠ T := by
    intro h
    subst t
    linarith
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htT⟩,
    det_eq_zero_of_leastEigenvalue_eq_zero (F t) heq⟩

end Paper256

end

end OAI
