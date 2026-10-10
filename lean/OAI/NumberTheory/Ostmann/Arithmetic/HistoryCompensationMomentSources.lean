import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentBasic
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationMoment
open Construction CompensationEqualityPatterns
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem sourceWeight_sum (sources : SourceFamily) (origin : ι → ℕ) (i : ι) :
    (∑ v : CommonSample sources origin, sourceWeight sources origin i v) = 1 := by
  have hinj : Function.Injective (sourceEmbed sources origin i) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun p : CommonSample sources origin => p.val) h
  have hsum : (∑ p : (sources (origin i)).Sample, (sources (origin i)).law.mass p) =
      ∑ v : CommonSample sources origin, sourceWeight sources origin i v := by
    apply Fintype.sum_of_injective (sourceEmbed sources origin i) hinj
    · intro v hv
      have hmem : v.val ∉ (sources (origin i)).candidates := by
        intro hp
        exact hv ⟨⟨v.val, hp⟩, Subtype.ext rfl⟩
      simp [sourceWeight, hmem]
    · intro p
      exact (sourceWeight_embed sources origin i p).symm
  exact hsum.symm.trans (sources (origin i)).law.mass_total

theorem logCellPrimeSource_mass_mul_le (c : ℝ) (E : Finset ℕ)
    (hZ : 0 < logCellMass c E) (p : (logCellPrimeSource c E hZ).Sample) :
    (logCellPrimeSource c E hZ).law.mass p * (p.val : ℝ) ≤ (logCellMass c E)⁻¹ := by
  have hp : 0 < (p.val : ℝ) := by
    exact_mod_cast (logCellPrimeSource c E hZ).prime p.val p.property |>.pos
  change (logCellPrior c E hZ).mass p * (p.val : ℝ) ≤ _
  apply (mul_le_mul_of_nonneg_right (logCellPrior_mass_le c E hZ p) hp.le).trans
  exact le_of_eq (by field_simp)

omit [DecidableEq ι] in

theorem sourceWeight_mass_mul_le (sources : SourceFamily) (origin : ι → ℕ)
    (centers : ι → ℝ) (deleted : ι → Finset ℕ)
    (hZ : ∀ i, 0 < logCellMass (centers i) (deleted i))
    (hsource : ∀ i, sources (origin i) = logCellPrimeSource (centers i) (deleted i) (hZ i))
    (i : ι) (v : CommonSample sources origin) :
    sourceWeight sources origin i v * (v.val : ℝ) ≤
      (logCellMass (centers i) (deleted i))⁻¹ := by
  unfold sourceWeight
  split_ifs with hmem
  · have hm : ∀ p : (sources (origin i)).Sample,
        (sources (origin i)).law.mass p * (p.val : ℝ) ≤
          (logCellMass (centers i) (deleted i))⁻¹ := by
      rw [hsource i]
      exact logCellPrimeSource_mass_mul_le (centers i) (deleted i) (hZ i)
    exact hm ⟨v.val, hmem⟩
  · simpa only [zero_mul] using (inv_nonneg.mpr (hZ i).le)

theorem source_block_moment_le (sources : SourceFamily) (origin : ι → ℕ)
    (centers : ι → ℝ) (deleted : ι → Finset ℕ)
    (hZ : ∀ i, 0 < logCellMass (centers i) (deleted i))
    (hsource : ∀ i, sources (origin i) = logCellPrimeSource (centers i) (deleted i) (hZ i))
    (j : ι) :
    (∑ v : CommonSample sources origin, (v.val : ℝ)⁻¹ *
      ∏ i, sourceWeight sources origin i v * (v.val : ℝ)) ≤
      ∏ i ∈ Finset.univ.erase j, (logCellMass (centers i) (deleted i))⁻¹ := by
  apply block_moment_le _ _ _ j
  · exact sourceWeight_nonneg sources origin
  · intro v
    exact_mod_cast (commonSample_prime sources origin v).pos
  · exact sourceWeight_mass_mul_le sources origin centers deleted hZ hsource
  · exact sourceWeight_sum sources origin j

omit [DecidableEq ι] in

theorem source_selected_moment_le {η : Type*} [Fintype η] [DecidableEq η]
    (sources : SourceFamily) (origin : ι → ℕ) (pick : η → ι)
    (centers : ι → ℝ) (deleted : ι → Finset ℕ)
    (hZ : ∀ i, 0 < logCellMass (centers i) (deleted i))
    (hsource : ∀ i, sources (origin i) = logCellPrimeSource (centers i) (deleted i) (hZ i))
    (j : η) :
    (∑ v : CommonSample sources origin, (v.val : ℝ)⁻¹ *
      ∏ i, sourceWeight sources origin (pick i) v * (v.val : ℝ)) ≤
      ∏ i ∈ Finset.univ.erase j, (logCellMass (centers (pick i)) (deleted (pick i)))⁻¹ := by
  apply block_moment_le _ _ _ j
  · intro i v
    exact sourceWeight_nonneg sources origin (pick i) v
  · intro v
    exact_mod_cast (commonSample_prime sources origin v).pos
  · intro i v
    exact sourceWeight_mass_mul_le sources origin centers deleted hZ hsource (pick i) v
  · exact sourceWeight_sum sources origin (pick j)

end Ostmann.Arithmetic.HistoryCompensationMoment

end

end OAI
