import OAI.NumberTheory.Ostmann.Characters.SparseTensorKernel

namespace OAI

/-! # The independent unit-residue mean of the sparse polynomial -/

namespace Ostmann
open scoped Classical BigOperators

abbrev NonzeroResidue (p : ℕ) [NeZero p] := ↥(Finset.univ.erase (0 : ZMod p))

noncomputable def tensorUnitMean {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℂ) : ℂ :=
  (∏ i, ((p i : ℂ) - 1)⁻¹) *
    ∑ x : (∀ i, NonzeroResidue (p i)), f (fun i => x i)

theorem tensorUnitMean_product {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : ∀ i, ZMod (p i) → ℂ) :
    tensorUnitMean p (fun x => ∏ i, f i (x i)) =
      ∏ i, ((p i : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0, f i x := by
  unfold tensorUnitMean
  change (∏ i, ((p i : ℂ) - 1)⁻¹) *
    (∑ x : (∀ i, NonzeroResidue (p i)), ∏ i, f i (x i)) = _
  rw [← Fintype.prod_sum (fun i (x : NonzeroResidue (p i)) => f i x)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.sum_coe_sort]

noncomputable def tensorUnitMeanLinearMap {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)] :
    ((∀ i, ZMod (p i)) → ℂ) →ₗ[ℂ] ℂ where
  toFun := tensorUnitMean p
  map_add' f g := by simp [tensorUnitMean, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [tensorUnitMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem tensorUnitMean_polydisc {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100) :
    ‖tensorUnitMean p (fun x => ∏ i,
      (1 + u * localSparseKernel (E i) (x i)) * (1 + v * localSparseKernel (E i) (x i)))‖ ≤
        Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
  rw [tensorUnitMean_product p
    (fun i x => (1 + u * localSparseKernel (E i) x) * (1 + v * localSparseKernel (E i) x)), norm_prod]
  calc
    _ ≤ ∏ i, (1 + 6 / (p i : ℝ)) := Finset.prod_le_prod₀
      (fun i _ => norm_nonneg _)
      (fun i _ => sparse_unit_polydisc_bound (E i) (hE i) (hsym i) ε hε hε1 (hc i) u v hu hv)
    _ ≤ _ := by
      have hh := product_one_add_le_exp_sum (fun i => 6 / (p i : ℝ)) (by intro i; positivity)
      simpa only [div_eq_mul_inv, ← Finset.mul_sum] using hh

end Ostmann

end OAI
