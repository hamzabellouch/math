import OAI.Probability.InvariantIsing.Arrays.Overlaps

namespace OAI

/-! The exact site-symmetry identity used for cavity self-consistency.
It is a statement about the full two-replica law, before any cutoff. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

def cavitySpinPairPermutation {N : ℕ} (e : Equiv.Perm (Fin N)) :
    (Spin N × Spin N) ≃ᵐ (Spin N × Spin N) where
  toFun x := (x.1 ∘ e, x.2 ∘ e)
  invFun x := (x.1 ∘ e.symm, x.2 ∘ e.symm)
  left_inv x := by ext i <;> simp
  right_inv x := by ext i <;> simp
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

def cavityTotalSpinOverlap {N : ℕ} (x : Spin N × Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, spinValue (x.1 i) * spinValue (x.2 i)

lemma cavityTotalSpinOverlap_permutation {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : Spin N × Spin N) :
    cavityTotalSpinOverlap (cavitySpinPairPermutation e x) = cavityTotalSpinOverlap x := by
  unfold cavityTotalSpinOverlap
  congr 1
  exact Equiv.sum_comp e (fun i => spinValue (x.1 i) * spinValue (x.2 i))

/-- Permutation symmetry makes every site insertion equal to the total-overlap
insertion. No Ghirlanda--Guerra identity is required for the full system. -/
theorem cavity_site_symmetry_identity {N : ℕ} (hN : 0 < N)
    (μ : Measure (Spin N × Spin N)) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), Measure.map (cavitySpinPairPermutation e) μ = μ)
    (φ : ℝ → ℝ) (j : Fin N) :
    (∫ x, φ (cavityTotalSpinOverlap x) * spinValue (x.1 j) * spinValue (x.2 j) ∂μ) =
      ∫ x, φ (cavityTotalSpinOverlap x) * cavityTotalSpinOverlap x ∂μ := by
  let a := fun i : Fin N => ∫ x, φ (cavityTotalSpinOverlap x) *
    spinValue (x.1 i) * spinValue (x.2 i) ∂μ
  have he (i : Fin N) : a i = a j := by
    let e := cavitySpinPairPermutation (Equiv.swap i j)
    have hh := integral_map_equiv (μ := μ) e
      (fun x => φ (cavityTotalSpinOverlap x) * spinValue (x.1 i) * spinValue (x.2 i))
    rw [hμ (Equiv.swap i j)] at hh
    dsimp only [e] at hh
    simp only [cavityTotalSpinOverlap_permutation] at hh
    simpa only [cavitySpinPairPermutation,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left] using hh
  have hs : (∑ i, a i) = (N : ℝ) * a j := by simp_rw [he]; simp
  have hrewrite : (∫ x, φ (cavityTotalSpinOverlap x) * cavityTotalSpinOverlap x ∂μ) =
      (N : ℝ)⁻¹ * ∑ i, a i := by
    change _ = (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ x, φ (cavityTotalSpinOverlap x) *
      spinValue (x.1 i) * spinValue (x.2 i) ∂μ
    rw [← integral_finsetSum _ (fun i _ => Integrable.of_finite), ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [cavityTotalSpinOverlap, Finset.mul_sum, ← mul_assoc]
      ring_nf
  rw [hrewrite, hs, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

end InvariantIsing

end

end OAI
