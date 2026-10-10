import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEssentialContraction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakSubsequence

namespace OAI

/-! # A finite-dimensional exception to the actual weak-null contraction

The argument uses a countable dense family only to choose finitely many
orthogonality constraints. The weak-null bound is supplied by the proved
whole-space energy observation inequality.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DefocusingNLS

theorem homogeneousOperator_finite_annihilator (a k r δ : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hδ : 0 < δ)
    (T : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hweak : ∀ u : ℕ → HomogeneousY a k, (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖T (u j)‖ ^ 2 < r + ε) :
    ∃ (d : ℕ → HomogeneousY a k) (N : ℕ),
      ∀ u : HomogeneousY a k, (∀ i ≤ N, inner ℂ (d i) u = 0) →
        ‖T u‖ ^ 2 ≤ (r + δ) * ‖u‖ ^ 2 := by
  let := homogeneousFourierMeasure_locallyFinite a k ha1 hk
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MeasureTheory.IsSeparable (homogeneousFourierMeasure a k) := inferInstance
  let : SecondCountableTopology (HomogeneousY a k) := inferInstance
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (HomogeneousY a k)
  refine ⟨d, ?_⟩
  by_contra! h
  choose u horth hlarge using h
  have hup (j : ℕ) : 0 < ‖u j‖ := by
    by_contra hz
    have hu0 : u j = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hz) (norm_nonneg _))
    simpa only [hu0, map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      lt_self_iff_false] using hlarge j
  let w : ℕ → HomogeneousY a k := fun j => (‖u j‖)⁻¹ • u j
  have hwn (j : ℕ) : ‖w j‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hup j)),
      inv_mul_cancel₀ (hup j).ne']
  have hTw (j : ℕ) : ‖T (w j)‖ = ‖T (u j)‖ / ‖u j‖ := by
    dsimp only [w]
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hup j))]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  have hwlarge (j : ℕ) : r + δ < ‖T (w j)‖ ^ 2 := by
    rw [hTw j, div_pow]
    exact (lt_div_iff₀ (sq_pos_of_pos (hup j))).mpr (hlarge j)
  have hworth (i j : ℕ) (hij : i ≤ j) : inner ℂ (d i) (w j) = 0 := by
    dsimp only [w]
    rw [inner_smul_right_eq_smul, horth j i hij, smul_zero]
  obtain ⟨v, _hv, φ, hφ, hw⟩ := homogeneousY_weak_subsequence a k 1 ha1 hk w
    (fun j => (hwn j).le)
  have hv0 : v = 0 := by
    have hi (i : ℕ) : inner ℂ (d i) v = 0 := by
      let ℓ : HomogeneousY a k →L[ℝ] ℂ := (innerSL ℂ (d i)).restrictScalars ℝ
      have hlim := hw ℓ
      change Tendsto (fun j => inner ℂ (d i) (w (φ j))) atTop (𝓝 (inner ℂ (d i) v)) at hlim
      have hzero : Tendsto (fun j => inner ℂ (d i) (w (φ j))) atTop (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop i)] with j hj
        exact (hworth i (φ j) hj).symm
      exact tendsto_nhds_unique hlim hzero
    have he : (fun x : HomogeneousY a k => inner ℂ x v) = fun _ => (0 : ℂ) :=
      hd.equalizer (by fun_prop) continuous_const (funext hi)
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (congrFun he v)
  have hupper := hweak (fun j => w (φ j)) (fun j => (hwn (φ j)).le)
    (fun ℓ => by simpa only [hv0, map_zero] using hw ℓ) δ hδ
  obtain ⟨j, hj⟩ := hupper.exists
  exact (not_lt_of_ge (hwlarge (φ j)).le) hj

end DefocusingNLS

end OAI
