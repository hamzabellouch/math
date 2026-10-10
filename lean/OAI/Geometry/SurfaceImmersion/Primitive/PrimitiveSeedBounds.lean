import OAI.Geometry.SurfaceImmersion.Correction.PrimitiveInitialMean
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetCompactRange

namespace OAI

/-! One compact jet range and derivative profiles for all scalar seeds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial WeightedEstimates

lemma primitiveSeed_factor_bound {δ : ℝ} (hδ : δ^2 ≤ 1) :
    |Real.sqrt (1-δ^2)| ≤ 1 ∧ |Real.sqrt (1-δ^2)-1| ≤ δ^2 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hδ)
  have hn := Real.sqrt_nonneg (1-δ^2)
  have hu : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  rw [abs_of_nonneg hn,abs_of_nonpos (sub_nonpos.mpr hu)]
  exact ⟨hu,by nlinarith⟩

theorem compact_primitiveSeed_bounds {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {F : JetPolynomial.Base → JetPolynomial.Space}
    (hF : ContDiff ℝ ∞ F) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∃ A B : ℕ → ℝ,
      (∀ m, 1 ≤ A m) ∧ (∀ m, 1 ≤ B m) ∧
      ∀ δ : ℝ, δ^2 ≤ 1 → Set.MapsTo (lowJet (primitiveSeed δ F)) U Q ∧
        (∀ m, WeightedBound U 1 m (B m) (lowJet (primitiveSeed δ F))) ∧
        (∀ m, WeightedBound U 1 (m+2) (A m) (primitiveSeed δ F)) ∧
        (∀ m, WeightedBound U 1 m (A m * δ^2) (primitiveSeed δ F-F)) := by
  choose A hA ha using fun m => compact_local_weighted_bound hU isOpen_univ K.isCompact
    hUK (Set.subset_univ _) hF.contDiffOn (m+2)
  choose D hD hd using fun m => bounded_lowJet_prefix hU K hUK m
  obtain ⟨Q,hQ,hQG⟩ := bounded_lowJet_range hU K hUK (zero_le_one.trans (hA 0))
  refine ⟨Q,hQ,A,(fun m => D m+A m),hA,?_,?_⟩
  · intro m
    exact (hD m).trans (le_add_of_nonneg_right (zero_le_one.trans (hA m)))
  · intro δ hδ
    have hfactor := primitiveSeed_factor_bound hδ
    have hseed (m : ℕ) : WeightedBound U 1 (m+2) (A m) (primitiveSeed δ F) := by
      apply ((ha m 1 zero_le_one le_rfl).const_smul hU.uniqueDiffOn hF.contDiffOn
        (Real.sqrt (1-δ^2))).mono_const
      exact mul_le_of_le_one_left (zero_le_one.trans (hA m)) hfactor.1
    refine ⟨hQG _ (primitiveSeed_smooth δ hF) (hseed 0),?_,hseed,?_⟩
    · intro m
      apply hd m _ (primitiveSeed_smooth δ hF) 1 (A m) zero_lt_one le_rfl
        (zero_le_one.trans (hA m))
      intro j hj
      simpa only [one_pow,div_one] using (hseed m).mono_order hj
    · intro m
      have hb := ((ha m 1 zero_le_one le_rfl).mono_order (by omega : m ≤ m+2)).const_smul
        hU.uniqueDiffOn hF.contDiffOn (Real.sqrt (1-δ^2)-1)
      apply (hb.mono_const (by
        calc
          |Real.sqrt (1-δ^2)-1| * A m ≤ δ^2 * A m :=
            mul_le_mul_of_nonneg_right hfactor.2 (zero_le_one.trans (hA m))
          _ = A m * δ^2 := mul_comm _ _)).congr
      intro x _
      ext k
      simp only [primitiveSeed,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
