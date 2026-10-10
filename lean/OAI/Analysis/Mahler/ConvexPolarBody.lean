import OAI.Analysis.Mahler.ConvexGeometry

namespace OAI

namespace SymmetricMahler
open Set Finset
variable {I : Type*} [Fintype I] [decidableEqI : DecidableEq I]

omit decidableEqI in
lemma convex_coordinatePolar [DecidableEq I] (K : Set (I → ℝ)) : Convex ℝ (coordinatePolar K) := by
  intro p hp q hq a b ha hb hab x hx
  calc
    (∑ i, (a • p + b • q) i * x i) =
        a * (∑ i, p i*x i) + b * (∑ i, q i*x i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        sum_add_distrib, mul_sum]
      apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ a*1+b*1 := add_le_add
      (mul_le_mul_of_nonneg_left (hp x hx) ha) (mul_le_mul_of_nonneg_left (hq x hx) hb)
    _ = 1 := by linarith

omit decidableEqI in
lemma symmetric_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K) :
    ∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K := by
  intro p hp x hx
  have h := (abs_le.mp (polar_pairing_abs hsym hp hx)).1
  simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]
  linarith

omit decidableEqI in
/-- A compact K gives an open l1 neighborhood of zero inside the literal polar. -/
theorem zero_mem_interior_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hK : IsCompact K) :
    (0 : I → ℝ) ∈ interior (coordinatePolar K) := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  let S : Set (I → ℝ) := {p | (∑ i, |p i|) < R⁻¹}
  have hS : IsOpen S := isOpen_lt
    (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)) continuous_const
  have hz : (0 : I → ℝ) ∈ S := by simpa [S] using inv_pos.mpr hR
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hS.mem_nhds hz)
  intro p hp x hx
  calc
    (∑ i, p i*x i) ≤ ∑ i, |p i| * R := by
      apply sum_le_sum
      intro i _
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm x i).trans (hb x hx)) (abs_nonneg _)
    _ = (∑ i, |p i|)*R := by rw [sum_mul]
    _ ≤ 1 := by
      have h : (∑ i, |p i|) < 1/R := by simpa only [S, Set.mem_ofPred_eq, one_div] using hp
      exact ((lt_div_iff₀ hR).mp h).le

/-- The polar of an origin-symmetric convex body is again such a body. -/
theorem coordinatePolar_is_symmetric_convex_body {K : Set (I → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    IsCompact (coordinatePolar K) ∧ Convex ℝ (coordinatePolar K) ∧
      (∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K) ∧
      (interior (coordinatePolar K)).Nonempty :=
  ⟨isCompact_coordinatePolar hsym (zero_mem_interior_of_symmetric hconv hsym hint),
    convex_coordinatePolar K, symmetric_coordinatePolar hsym,
    ⟨0, zero_mem_interior_coordinatePolar hK⟩⟩

end SymmetricMahler

end OAI
