import OAI.Probability.InvariantIsing.Magnetic.MagneticGridProjection

namespace OAI

/-! The normalized radius of the magnetic grid projection converges to its mesh. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma magnetic_cover_distance_tendsto (N : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (hNlim : Tendsto N atTop atTop) (A : ℕ) {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun k => (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)) atTop (𝓝 δ) := by
  have he k : 0≤(⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ ∧
      (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ≤((A:ℝ)+1)/(N k:ℝ) := by
    have hp : (0:ℝ)<N k := Nat.cast_pos.mpr (hN k)
    have hx : 0≤δ*N k+A := by positivity
    have hl := Nat.le_ceil (δ*N k+A)
    have hu := Nat.ceil_lt_add_one hx
    constructor
    · apply sub_nonneg.mpr
      apply (le_div_iff₀ hp).mpr
      linarith [(Nat.cast_nonneg A : (0:ℝ)≤A)]
    · have hdiff : (⌈δ*N k+A⌉₊:ℝ)/(N k:ℝ)-δ=
          ((⌈δ*N k+A⌉₊:ℝ)-δ*N k)/(N k:ℝ) := by field_simp
      rw [hdiff]
      exact div_le_div_of_nonneg_right (by linarith) hp.le
  have hz := squeeze_zero (fun k => (he k).1) (fun k => (he k).2)
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNlim))
  simpa only [sub_add_cancel,zero_add] using hz.add_const δ

end InvariantIsing

end

end OAI
