import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget
open LogCellPartition HistoryGiantGridCellBounds HistoryGiantReplacementError
open HistoryGiantPrincipalMassBounds HistoryGiantPriorExceptionalError SourcePriorGridDeletion
open PrimeCellReplacement HistoryGiantXiReplacementActual Filter

theorem eventually_periodic_error_bounds (k₀ : ℕ) (c₀ : ℝ)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G L₀ : ℝ) (M : ℕ) [NeZero M]
      (deleted : Finset ℕ), deleted.card ≤ 2 →
      Real.log (M:ℝ) ≤ Real.exp (giant.μ*L) →
      Real.exp (giant.a₀*L) ≤ G-1 →
      PrimeBounds k₀ δ K L₀ G L M deleted →
      ∀ (a : ℕ), a ≤ residueCostExponent k₀ →
      ∀ D A H Sp Sm : ℝ, 0 ≤ D → 0 ≤ A → 0 ≤ H → 0 ≤ Sp → 0 ≤ Sm →
      D ≤ smoothGrowthFactor k₀ c₀ giant.μ L →
      A ≤ smoothGrowthFactor k₀ c₀ giant.μ L →
      H ≤ (M:ℝ)^a*smoothGrowthFactor k₀ c₀ giant.μ L →
      Sp ≤ (M:ℝ)^a → Sm ≤ (M:ℝ)^a →
      (deletionCap G deleted*(1+fullMassRatio G deleted)*H +
        (2*(2*D*meshWidth giant L)*principalMass M
            (fun _ : Bool => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted) +
          (2*D*meshWidth giant L+A)*
            ((Fintype.card (GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1)
              (fun _ => meshWidth giant L)):ℝ)*(8*giantPrimeError K δ G deleted)))*Sp ≤
          29*Real.exp (-Real.exp (giant.target*L))) ∧
      ((Real.exp 1+1)*deletionCap G deleted*H +
        (2*(2*D*meshWidth giant L)*mixedPrincipalMass M
            (G-1) (G+1) G smoothPartition (fun _ : Unit => G-1) (fun _ => G+1)
            (fun _ => logCellMass G deleted) +
          (2*D*meshWidth giant L+A)*
            ((Fintype.card (MixedGridIndex (G-1) (G+1) (meshWidth giant L)
              (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => meshWidth giant L)):ℝ)*
              giantMixedError K δ G L deleted))*Sm ≤
          8*Real.exp (-Real.exp (giant.target*L))) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (giant.a₁*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num [giant]))
  filter_upwards [eventually_giant_grid_errors k₀ (C:=c₀) hK hδ,
    eventually_variation_with_mass k₀ c₀ (by norm_num : (0:ℝ) ≤ 10),
    eventually_exceptional_errors k₀ c₀, ht.eventually_ge_atTop 2,
    eventually_ge_atTop (0:ℝ)] with L hgrid hvar hexc hlen hL
  intro G L₀ M _ deleted hdeleted hmod hlo hb a ha D A H Sp Sm hD hA hH hSp hSm
    hDF hAF hHF hSpQ hSmQ
  have hM : 0 < M := NeZero.pos M
  have hG : 2 ≤ G := by
    have := Real.one_le_exp (mul_nonneg (show 0 ≤ giant.a₀ by norm_num [giant]) hL)
    linarith
  have hmass := original_giant_principal_masses M hM (bulkSize k₀ L) G deleted
    hG hb.mass_pos hb.inverse_cost
  have hgrid' := hgrid G L₀ M deleted hM hmod hb a ha
  have hvarp := hvar a M
    (principalMass M (fun _ : Bool => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted))
    ha hM hmod hmass.1.2
  have hvarm := hvar a M
    (mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted))
    ha hM hmod hmass.2.2
  have hex := (hexc G M hM hmod hlo deleted hdeleted).errors a H ha hH hHF
  constructor
  · simpa only [show (5+3*(8:ℝ))=29 by norm_num] using
      replacement_error_algebra _ D A (meshWidth giant L) _ _ Sp
        (smoothGrowthFactor k₀ c₀ giant.μ L) ((meshIntervals giant L:ℝ)^2) ((M:ℝ)^a)
        (giantPrimeError K δ G deleted) 8 (Real.exp (-Real.exp (giant.target*L)))
        hD hA hb.mesh_pos.le hmass.1.1 (by positivity) hSp (Real.exp_nonneg _)
        (by positivity) (by positivity) hb.error_nonneg (by norm_num) hb.mesh_le_one
        hDF hAF (prime_grid_card_le G L hlen) hSpQ hex.1 hvarp hgrid'.1
  · simpa only [one_mul,show (5+3*(1:ℝ))=8 by norm_num] using
      replacement_error_algebra _ D A (meshWidth giant L) _ _ Sm
        (smoothGrowthFactor k₀ c₀ giant.μ L) ((meshIntervals giant L:ℝ)^2) ((M:ℝ)^a)
        (giantMixedError K δ G L deleted) 1 (Real.exp (-Real.exp (giant.target*L)))
        hD hA hb.mesh_pos.le hmass.2.1 (by positivity) hSm (Real.exp_nonneg _)
        (by positivity) (by positivity) (giantMixedError_nonneg hb.error_nonneg)
        (by norm_num) hb.mesh_le_one hDF hAF (mixed_grid_card_le G L hlen) hSmQ
        hex.2.2.1 hvarm hgrid'.2

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
