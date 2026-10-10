import OAI.Geometry.NodalSets.Elliptic.SmoothOperatorJet
import OAI.Geometry.NodalSets.Elliptic.SmoothSymmetry
import OAI.Geometry.NodalSets.Elliptic.TaylorPolynomial

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def finiteTaylorSeries (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    FormalMultilinearSeries ℝ Coord ℂ := fun k ↦
  if k ≤ m then (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f y else 0

lemma taylorPolynomial_hasFiniteSeries (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    HasFiniteFPowerSeriesOnBall (reval (taylorPolynomial f y m))
      (finiteTaylorSeries f y m) 0 (m + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro k hk
    simp [finiteTaylorSeries, show ¬ k ≤ m by omega]
  · simp
  · intro x _
    rw [zero_add, reval_taylorPolynomial]
    apply Finset.sum_congr rfl
    intro k hk
    simp [finiteTaylorSeries, show k ≤ m by have := Finset.mem_range.mp hk; omega]

theorem iteratedFDeriv_taylorPolynomial {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (y : Coord) (m k : ℕ) (hk : k ≤ m) :
    iteratedFDeriv ℝ k (reval (taylorPolynomial f y m)) 0 = iteratedFDeriv ℝ k f y := by
  ext v
  rw [(taylorPolynomial_hasFiniteSeries f y m).toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [finiteTaylorSeries, ite_eq_left hk, smul_apply]
  have hs (σ : Equiv.Perm (Fin k)) :
      iteratedFDeriv ℝ k f y (fun i ↦ v (σ i)) = iteratedFDeriv ℝ k f y v :=
    smooth_iteratedFDeriv_perm hf k v y σ
  simp_rw [hs]
  simp [Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    Nat.factorial_ne_zero]

theorem flatAt_taylorPolynomial {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    FlatAt m (fun x ↦ f x - reval (taylorPolynomial f 0 m) x) 0 := by
  intro k hk
  change iteratedFDeriv ℝ k (f - reval (taylorPolynomial f 0 m)) 0 = 0
  rw [iteratedFDeriv_sub_apply
    (hf.contDiffAt.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
    ((reval_contDiff _).contDiffAt.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))),
    iteratedFDeriv_taylorPolynomial hf 0 m k hk, sub_self]

theorem smooth_operator_matching_polynomials
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i)) (m : ℕ) :
    ∃ (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly),
      (∀ i j, FlatAt m (fun x ↦ g i j x - reval (G i j) x) 0) ∧
      (∀ i, FlatAt m (fun x ↦ b i x - reval (B i) x) 0) := by
  exact ⟨fun i j ↦ taylorPolynomial (g i j) 0 m, fun i ↦ taylorPolynomial (b i) 0 m,
    fun i j ↦ flatAt_taylorPolynomial (hg i j) m,
    fun i ↦ flatAt_taylorPolynomial (hb i) m⟩

end
end Yau.Jets

end OAI
