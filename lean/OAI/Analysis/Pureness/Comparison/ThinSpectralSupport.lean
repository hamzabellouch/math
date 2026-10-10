import OAI.Analysis.Pureness.Comparison.HereditarySupportMass
import OAI.Analysis.Pureness.Comparison.OrthogonalSupportMass
import OAI.Analysis.Pureness.Comparison.SpectralTransport

namespace OAI
open scoped BigOperators
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [IsSimpleCStarAlgebra A]

theorem exists_common_support_mass_bound (n : ℕ) (c : Fin n → A)
    (hc : ∀ i, 0 ≤ c i) (hcn : ∀ i, c i ≠ 0) :
    ∃ e : A, ∃ he : 0 ≤ e, e ≠ 0 ∧ ∀ τ : TracialState A, ∀ i,
      (τ.spectralSupportMass e he).toReal ≤ (τ.spectralSupportMass (c i) (hc i)).toReal := by
  induction n with
  | zero => exact ⟨1, zero_le_one, one_ne_zero, fun _τ i => i.elim0⟩
  | succ n ih =>
    obtain ⟨d, hd, hdn, hbound⟩ := ih (fun i => c i.succ) (fun i => hc i.succ) (fun i => hcn i.succ)
    obtain ⟨e, he, hen, _hem, hlink⟩ := exists_linking_support_mass_bound (hc 0) hd (hcn 0) hdn
    refine ⟨e, he, hen, fun τ i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hlink τ).1
    · exact (hlink τ).2.trans (hbound τ j)

theorem exists_thin_full_spectral_element
    (hinfinite : ¬ FiniteDimensional ℂ A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : A, ∃ he : 0 ≤ e, e ≠ 0 ∧ ‖e‖ = 1 ∧
      closure (finiteSandwichIdeal e : Set A) = Set.univ ∧
      ∀ τ : TracialState A, (τ.spectralSupportMass e he).toReal < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  let k := N + 1
  have hk : (0 : ℝ) < k := by dsimp [k]; positivity
  have hkδ : 1 < (k : ℝ) * δ := by
    have hNδ : 1 < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
    dsimp [k]
    push_cast
    nlinarith
  obtain ⟨c, hc, horth⟩ := exists_finite_orthogonal_positive_family hinfinite k
    (b := 1) zero_le_one one_ne_zero
  obtain ⟨d, hd, hdn, hbound⟩ := exists_common_support_mass_bound k c (fun i => (hc i).1)
    (fun i => (hc i).2.1)
  have hsmall : ∀ τ : TracialState A, (τ.spectralSupportMass d hd).toReal < δ := by
    intro τ
    have hsum := τ.orthogonal_support_mass_sum_le_one c (fun i => (hc i).1) horth
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _hi => hbound τ i)
    have hkm : (k : ℝ) * (τ.spectralSupportMass d hd).toReal ≤ 1 := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hle.trans hsum
    nlinarith
  let e : A := ‖d‖⁻¹ • d
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdn
  have he : 0 ≤ e := smul_nonneg (inv_nonneg.mpr hnorm.le) hd
  have henorm : ‖e‖ = 1 := by simp [e, norm_smul, hnorm.ne']
  have hen : e ≠ 0 := by intro hz; rw [hz, norm_zero] at henorm; exact zero_ne_one henorm
  refine ⟨e, he, hen, henorm, full_of_ne_zero hen, fun τ => ?_⟩
  have heq := τ.smul_support_mass hd (inv_pos.mpr hnorm)
  change (τ.spectralSupportMass (‖d‖⁻¹ • d) he).toReal < δ
  rw [heq]
  exact hsmall τ
end CuntzComparison

end OAI
