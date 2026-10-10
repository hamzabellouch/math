import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldMinimum

namespace OAI

/-! The one-dimensional coercivity argument needed for the inverse mean
of a finite Gaussian slab. -/

noncomputable section
open Set Filter
open scoped Topology

namespace InvariantIsing

lemma exists_mean_root_of_linear_lower {F M : ℝ → ℝ} {C s : ℝ}
    (dF : ∀ z, HasDerivAt F (M z) z) (hl : ∀ z, |z| - C ≤ F z)
    (hs : |s| < 1) : ∃ z, M z = s := by
  let δ := 1 - |s|
  let R := (|F 0| + |C| + 1) / δ
  have hδ : 0 < δ := sub_pos.mpr hs
  have hR : 0 ≤ R := div_nonneg (by positivity) hδ.le
  have he : δ * R = |F 0| + |C| + 1 := by
    dsimp only [R]
    field_simp
  let G := fun z => F z - z * s
  have hG : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((dF z).sub ((hasDerivAt_id z).mul_const s)).continuousAt
  have hlow (z : ℝ) : δ * |z| - C ≤ G z := by
    have hz : z * s ≤ |z| * |s| := by
      simpa only [abs_mul] using le_abs_self (z * s)
    dsimp only [δ, G]
    nlinarith [hl z]
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩) hG.continuousOn
  have hglobal (c : ℝ) : G b ≤ G c := by
    by_cases hc : c ∈ Icc (-R) R
    · exact hmin hc
    have hcr : R ≤ |c| := by
      by_contra hn
      have hlt : |c| < R := lt_of_not_ge hn
      exact hc ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    have hlarge : F 0 ≤ G c := by
      have hm := mul_le_mul_of_nonneg_left hcr hδ.le
      have hcabs := le_abs_self C
      have hfabs := le_abs_self (F 0)
      linarith [hlow c]
    have hz := hmin (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith)
    change G b ≤ G 0 at hz
    have hz' : G b ≤ F 0 := by
      simpa only [G, zero_mul, sub_zero] using hz
    exact hz'.trans hlarge
  have hlocal : IsLocalMin G b := Eventually.of_forall hglobal
  have hd : HasDerivAt G (M b - s) b := by
    convert (dF b).sub ((hasDerivAt_id b).mul_const s) using 1
    · rfl
    · simp only [one_mul]
  exact ⟨b, sub_eq_zero.mp (hlocal.hasDerivAt_eq_zero hd)⟩

end InvariantIsing

end

end OAI
