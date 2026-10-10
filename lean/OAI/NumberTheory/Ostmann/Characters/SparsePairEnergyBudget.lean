import OAI.NumberTheory.Ostmann.Supply.RestrictedSubsetEnergy
import OAI.NumberTheory.Ostmann.Characters.SparseFiniteContraction
import OAI.NumberTheory.Ostmann.Characters.SparseWeightPairAverage

namespace OAI

/-! # Combining the actual sparse pair kernel with its two energy budgets -/

namespace Ostmann
open scoped Classical BigOperators

theorem complementary_field_card_ratio {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) :
    ((p : ℝ) / S.card - 1)⁻¹ = (p : ℝ) / (Finset.univ \ S).card - 1 := by
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htNat : (Finset.univ \ S).card = p - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, ZMod.card]
  have ht : (0 : ℝ) < (Finset.univ \ S).card := by
    rw [htNat]
    exact_mod_cast Nat.sub_pos_of_lt hSp
  have hsum : ((S.card : ℕ) : ℝ) + (Finset.univ \ S).card = p := by
    rw [htNat]
    exact_mod_cast Nat.add_sub_of_le hSp.le
  have he : (p : ℝ) / S.card - 1 = ((Finset.univ \ S).card : ℝ) / S.card := by
    apply (eq_div_iff hs.ne').mpr
    field_simp
    linarith
  rw [he, inv_div]
  apply (eq_sub_iff_add_eq).mpr
  apply (div_add_one ht.ne').trans
  congr 1

theorem weighted_pair_square_bound (w α O a b E F : ℝ)
    (hw : 0 ≤ w) (hα : 0 ≤ α) (hO : 0 ≤ O) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hEF : 0 ≤ E)
    (hp : w ≤ O * a * b) (hA : α * a ^ 2 ≤ E) (hB : α * b ^ 2 ≤ F) :
    α ^ 2 * w ^ 2 ≤ O ^ 2 * E * F := by
  have hs := (sq_le_sq₀ hw (mul_nonneg (mul_nonneg hO ha) hb)).mpr hp
  have he := mul_le_mul hA hB (mul_nonneg hα (sq_nonneg b)) hEF
  calc
    _ ≤ α ^ 2 * (O * a * b) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg α)
    _ = O ^ 2 * ((α * a ^ 2) * (α * b ^ 2)) := by ring
    _ ≤ O ^ 2 * (E * F) := mul_le_mul_of_nonneg_left he (sq_nonneg O)
    _ = _ := by ring

/-- A single finite bound for the concrete sparse weight. The two energy
bounds here are the quantities proved by `restricted_lowMode_energy_budget`.
No norm of an untruncated tensor and no dimension factor appears. -/
theorem sparse_pair_average_energy_budget {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K)
    {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i)
    (α E F : ℝ) (hα : 0 ≤ α) (hE : 0 ≤ E)
    (hEA : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 ≤ E)
    (hEB : α * countingVectorNorm (lowModeVector (2 * K)
      (averagedCoordinates B (fun y => tensorPointCoordinates p
        (fun i => Finset.univ \ S i) (b y)))) ^ 2 ≤ F) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
      α ^ 2 * (sparseWeightPairAverage p S K A B a b) ^ 2 ≤
        (2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) ^ 2 * E * F := by
  intro U
  obtain ⟨hU, hmean, hop⟩ := sparse_finite_contraction p S hS hSp hp hlo hhi
    ε hε hεsmall hL1 L hL hH K hK
  refine ⟨hU, hmean, ?_⟩
  apply weighted_pair_square_bound _ _ _ _ _ E F
    (sparseWeightPairAverage_nonneg p S K A B a b) hα (by positivity)
    (by unfold countingVectorNorm; positivity) (by unfold countingVectorNorm; positivity) hE
    ?_ hEA hEB
  exact (sparseWeightPairAverage_le p S K A B a b ha hb).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hop (by unfold countingVectorNorm; positivity))
      (by unfold countingVectorNorm; positivity))

end Ostmann

end OAI
