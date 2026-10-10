import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReplacementGeometryBasic
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCenters

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open Construction Conclusion ScaleBudget Filter

theorem eventually_giant_normalization {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (E : Finset ℕ),
      Real.exp (giant.a₀*L) ≤ G-1 → G ≤ Real.exp L/2 → E.card ≤ 2 →
      0 < Construction.logCellMass G E ∧
      (Construction.logCellMass G E)⁻¹ ≤ 2*G ∧
      (Construction.logCellMass G E)⁻¹ ≤ Real.exp (2*((bulkSize k L : ℝ)+1)) := by
  obtain ⟨G₀,hG₀⟩ := eventually_atTop.mp logCell_normalization_eventually
  have ht := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
    (show 0 < giant.a₀ by norm_num [giant]))
  filter_upwards [ht.eventually_ge_atTop G₀,eventually_ge_atTop (0 : ℝ)] with L hmin hL
  intro G E hlow hu hE
  have hGG : G₀ ≤ G := by
    change G₀ ≤ Real.exp (giant.a₀*L) at hmin
    linarith
  obtain ⟨hZ,_,hZi⟩ := hG₀ G hGG E hE
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hscale : 1 ≤ bulkScale k := one_le_pow₀ hk1
  have hfloor := (bulkSize_bounds k hL).1
  have hLbound : L ≤ 2*((bulkSize k L : ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_right hscale hL
    nlinarith [Nat.cast_nonneg (bulkSize k L) (α:=ℝ)]
  refine ⟨hZ,hZi,?_⟩
  exact hZi.trans ((show 2*G ≤ Real.exp L by linarith).trans (Real.exp_le_exp.mpr hLbound))

theorem selected_giant_normalization_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ M : ℕ, 0 < M → Real.log (M : ℝ) ≤ Real.exp (giant.μ*L) →
      HistoryGiantReplacementGeometry.GeometryBounds δ L₀ C.giantCenter M L ∧
      ∀ deleted : Finset ℕ, deleted.card ≤ 2 →
        0 < Construction.logCellMass C.giantCenter deleted ∧
        (Construction.logCellMass C.giantCenter deleted)⁻¹ ≤ 2*C.giantCenter ∧
        (Construction.logCellMass C.giantCenter deleted)⁻¹ ≤
          Real.exp (2*((bulkSize k L : ℝ)+1)) := by
  filter_upwards [eventually_giant_normalization hk,
    RepeatedPriorBounds.initial_cell_centers_eventually d Bs BD Bz hk,
    HistoryGiantReplacementGeometry.eventually_geometryBounds hδ L₀] with L hn hc hg
  intro E C hG hGu hcl hcu hb hd M hM hmod
  have hgeo := hg C.blockBase C.giantCenter M hG hcl hM hmod
  refine ⟨hgeo,?_⟩
  intro deleted hdeleted
  exact hn C.giantCenter deleted hgeo.lower_scale (hc E C hG hGu hcl hcu hb hd).1.2 hdeleted

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
