import OAI.Analysis.OInfinity.CornerStabilization

namespace OAI

/-! # Closing the small stabilization gap

The principal-argument path between unitary elements at distance less than
`2` has speed at most `π`. Thus the middle gap in the finite corner
construction is closed by a genuine path with a uniform bound. The fixed
corner hypotheses are retained.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma selfAdjoint_expUnitary_sub_one_norm_le (x : selfAdjoint E) :
    ‖((selfAdjoint.expUnitary x : unitary E) : E) - 1‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ ≤ Real.pi
  · have hs := selfAdjoint.norm_sq_expUnitary_sub_one hx
    have hc := Real.one_sub_sq_div_two_le_cos (x := ‖x‖)
    nlinarith [norm_nonneg (((selfAdjoint.expUnitary x : unitary E) : E) - 1), norm_nonneg x]
  · nontriviality E
    calc
      _ ≤ ‖((selfAdjoint.expUnitary x : unitary E) : E)‖ + ‖(1 : E)‖ := norm_sub_le _ _
      _ = 2 := by rw [CStarRing.norm_coe_unitary, norm_one]; norm_num
      _ ≤ ‖x‖ := by linarith [Real.two_le_pi]

lemma selfAdjoint_expUnitary_sub_norm_le (x : selfAdjoint E) (t s : ℝ) :
    ‖((selfAdjoint.expUnitary (t • x) : unitary E) : E) -
      ((selfAdjoint.expUnitary (s • x) : unitary E) : E)‖ ≤ |t - s| * ‖x‖ := by
  have hc : Commute (((t - s) • x : selfAdjoint E) : E) ((s • x : selfAdjoint E) : E) := by
    simp only [selfAdjoint.val_smul]
    exact ((Commute.refl (x : E)).smul_left (t - s)).smul_right s
  have hs : t • x = (t - s) • x + s • x := by module
  have he : ((selfAdjoint.expUnitary (t • x) : unitary E) : E) -
      ((selfAdjoint.expUnitary (s • x) : unitary E) : E) =
      (((selfAdjoint.expUnitary ((t - s) • x) : unitary E) : E) - 1) *
        ((selfAdjoint.expUnitary (s • x) : unitary E) : E) := by
    conv_lhs => rw [hs, hc.expUnitary_add]
    simp only [Submonoid.coe_mul]
    noncomm_ring
  rw [he, CStarRing.norm_mul_coe_unitary]
  calc
    _ ≤ ‖(t - s) • x‖ := selfAdjoint_expUnitary_sub_one_norm_le _
    _ = |t - s| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]

lemma unitary_shortPath_sub_norm_le (u v : unitary E)
    (huv : ‖(v : E) - u‖ < 2) (t s : unitInterval) :
    ‖((Unitary.path u v huv t : unitary E) : E) -
      ((Unitary.path u v huv s : unitary E) : E)‖ ≤ Real.pi * |(t : ℝ) - s| := by
  change ‖((selfAdjoint.expUnitary ((t : ℝ) • Unitary.argSelfAdjoint (v * star u)) : unitary E) : E) *
      (u : E) - ((selfAdjoint.expUnitary ((s : ℝ) • Unitary.argSelfAdjoint (v * star u)) : unitary E) : E) *
      (u : E)‖ ≤ _
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary]
  calc
    _ ≤ |(t : ℝ) - s| * ‖Unitary.argSelfAdjoint (v * star u)‖ :=
      selfAdjoint_expUnitary_sub_norm_le _ _ _
    _ ≤ |(t : ℝ) - s| * Real.pi :=
      mul_le_mul_of_nonneg_left (Unitary.norm_argSelfAdjoint_le_pi _) (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- The principal-argument bridge closes the actual middle gap, with a
uniform speed bound independent of the two endpoint unitaries. -/
lemma exists_controlled_unitary_shortPath (u v : unitary E)
    (huv : ‖(u : E) - v‖ < 2) :
    ∃ p : Path u v, ∀ t s, ‖(p t : E) - p s‖ ≤ Real.pi * |(t : ℝ) - s| := by
  have h : ‖(v : E) - u‖ < 2 := by rwa [norm_sub_rev]
  exact ⟨Unitary.path u v h, unitary_shortPath_sub_norm_le u v h⟩

/-- Concatenating two uniformly controlled paths costs only the time rescaling. -/
lemma unitaryPath_trans_sub_norm_le {a b c : unitary E}
    (p : Path a b) (q : Path b c) (L : ℝ)
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|)
    (hq : ∀ t s, ‖(q t : E) - q s‖ ≤ L * |(t : ℝ) - s|) :
    ∀ t s, ‖((p.trans q) t : E) - (p.trans q) s‖ ≤ 2 * L * |(t : ℝ) - s| := by
  have hord : ∀ t s : unitInterval, (t : ℝ) ≤ s →
      ‖((p.trans q) t : E) - (p.trans q) s‖ ≤ 2 * L * |(t : ℝ) - s| := by
    intro t s hts
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · by_cases hs : (s : ℝ) ≤ 1 / 2
      · rw [Path.trans_apply, dite_eq_left ht, Path.trans_apply, dite_eq_left hs]
        calc
          _ ≤ L * |2 * (t : ℝ) - 2 * (s : ℝ)| := hp _ _
          _ = _ := by rw [← mul_sub, abs_mul]; norm_num; ring
      · rw [Path.trans_apply, dite_eq_left ht, Path.trans_apply, dite_eq_right hs]
        let t' : unitInterval := ⟨2 * t, by constructor <;> linarith [t.2.1]⟩
        let s' : unitInterval := ⟨2 * s - 1, by constructor <;> linarith [s.2.2]⟩
        change ‖(p t' : E) - q s'‖ ≤ _
        calc
          _ ≤ ‖(p t' : E) - b‖ + ‖(b : E) - q s'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ L * |2 * (t : ℝ) - 1| + L * |0 - (2 * (s : ℝ) - 1)| := by
            apply add_le_add
            · simpa only [Path.target, Set.Icc.coe_one] using hp t' 1
            · simpa only [Path.source, Set.Icc.coe_zero] using hq 0 s'
          _ = _ := by
            rw [abs_of_nonpos (by linarith : 2 * (t : ℝ) - 1 ≤ 0),
              abs_of_nonpos (by linarith : 0 - (2 * (s : ℝ) - 1) ≤ 0),
              abs_of_nonpos (sub_nonpos.mpr hts)]
            ring
    · have hs : ¬ (s : ℝ) ≤ 1 / 2 := by linarith
      rw [Path.trans_apply, dite_eq_right ht, Path.trans_apply, dite_eq_right hs]
      calc
        _ ≤ L * |(2 * (t : ℝ) - 1) - (2 * (s : ℝ) - 1)| := hq _ _
        _ = _ := by
          have he : (2 * (t : ℝ) - 1) - (2 * (s : ℝ) - 1) = 2 * ((t : ℝ) - s) := by ring
          rw [he, abs_mul]
          norm_num
          ring
  intro t s
  rcases le_total (t : ℝ) (s : ℝ) with hts | hst
  · exact hord t s hts
  · rw [norm_sub_rev, abs_sub_comm]
    exact hord s t hst

/-- Restrict a uniformly controlled angular path to its quarter-turn interval. -/
def unitaryQuarterPath (u : ℝ → unitary E) (hu : Continuous u) :
    Path (u 0) (u (Real.pi / 2)) where
  toFun t := u ((Real.pi / 2) * (t : ℝ))
  continuous_toFun := hu.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

lemma unitaryQuarterPath_sub_norm_le (u : ℝ → unitary E) (hu : Continuous u)
    (hbound : ∀ θ φ, ‖(u θ : E) - u φ‖ ≤ 4 * |θ - φ|) (t s : unitInterval) :
    ‖(unitaryQuarterPath u hu t : E) - unitaryQuarterPath u hu s‖ ≤
      (2 * Real.pi) * |(t : ℝ) - s| := by
  change ‖(u ((Real.pi / 2) * (t : ℝ)) : E) - u ((Real.pi / 2) * (s : ℝ))‖ ≤ _
  calc
    _ ≤ 4 * |(Real.pi / 2) * (t : ℝ) - (Real.pi / 2) * (s : ℝ)| := hbound _ _
    _ = _ := by
      rw [← mul_sub, abs_mul, abs_of_pos (half_pos Real.pi_pos)]
      ring

/-- The small middle gap is closed, yielding a uniformly controlled genuine
path for the compressed unitary. The fixed corner hypotheses are explicit. -/
lemma exists_uniform_compressed_unitary_path (q a b z : E)
    (hqstar : star q = q) (hqq : q * q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4 * δ < 2)
    (haz : ‖z * a - a * z‖ ≤ δ) (hbz : ‖z * b - b * z‖ ≤ δ) :
    ∃ u : unitary E, (u : E) = cornerCompression a z ∧
      ∃ p : Path u 1, ∀ t s, ‖(p t : E) - p s‖ ≤ (8 * Real.pi) * |(t : ℝ) - s| := by
  obtain ⟨u, v, huc, hvc, hu0, hv1, hgap, hun, hvn⟩ :=
    exists_controlled_cornerStabilization_paths q a b z hqstar hqq haa hbb hab hsum
      hqz hzq hzz hzz' δ hδ haz hbz
  have hclose : ‖(v 0 : E) - u (Real.pi / 2)‖ < 2 := by
    rw [norm_sub_rev]
    exact hgap.trans_lt hsmall
  let p := unitaryQuarterPath u huc
  let r := unitaryQuarterPath v hvc
  let middle := Unitary.path (u (Real.pi / 2)) (v 0) hclose
  have hp : ∀ t s, ‖(p t : E) - p s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| :=
    unitaryQuarterPath_sub_norm_le u huc hun
  have hr : ∀ t s, ‖(r t : E) - r s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| :=
    unitaryQuarterPath_sub_norm_le v hvc hvn
  have hm : ∀ t s, ‖(middle t : E) - middle s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| := by
    intro t s
    exact (unitary_shortPath_sub_norm_le _ _ hclose t s).trans (by
      nlinarith [abs_nonneg ((t : ℝ) - s), Real.pi_pos])
  have hpm : ∀ t s, ‖((p.trans middle) t : E) - (p.trans middle) s‖ ≤
      (4 * Real.pi) * |(t : ℝ) - s| := by
    simpa only [show 2 * (2 * Real.pi) = 4 * Real.pi by ring] using
      unitaryPath_trans_sub_norm_le p middle (2 * Real.pi) hp hm
  have hr' : ∀ t s, ‖(r t : E) - r s‖ ≤ (4 * Real.pi) * |(t : ℝ) - s| := by
    intro t s
    exact (hr t s).trans (by nlinarith [abs_nonneg ((t : ℝ) - s), Real.pi_pos])
  have hy : (1 : unitary E) = v (Real.pi / 2) := Subtype.ext hv1.symm
  let result : Path (u 0) 1 := ((p.trans middle).trans r).cast rfl hy
  refine ⟨u 0, hu0, result, ?_⟩
  intro t s
  change ‖(((p.trans middle).trans r) t : E) - ((p.trans middle).trans r) s‖ ≤ _
  simpa only [show 2 * (4 * Real.pi) = 8 * Real.pi by ring] using
    unitaryPath_trans_sub_norm_le (p.trans middle) r (4 * Real.pi) hpm hr' t s

end WeakPureInfiniteness

end

end OAI
