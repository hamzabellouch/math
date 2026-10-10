import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGiantDensityMassBasic
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedGiantDensityMass
open Construction Filter

theorem giant_density_masses_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      Real.exp ((1/20:ℝ)*L)-2 < G →
      1 < G ∧ 0 < Construction.logCellMass G ∅ ∧
      primeDensityMass G (Construction.logCellMass G ∅) ≤ 64 ∧
      mixedDensityMass G (Construction.logCellMass G ∅) ≤ 64 := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp logCell_normalization_eventually
  have ht : Tendsto (fun L : ℝ => Real.exp ((1/20:ℝ)*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/20))
  filter_upwards [ht.eventually_ge_atTop (max 4 (T₀+2))] with L hL
  intro G hG
  have hG2 : 2 ≤ G := by linarith [le_max_left (4:ℝ) (T₀+2)]
  have hGT : T₀ ≤ G := by linarith [le_max_right (4:ℝ) (T₀+2)]
  obtain ⟨hZ, _, hZi⟩ := hT₀ G hGT ∅ (by simp)
  exact ⟨by linarith, hZ, (primeDensityMass_bounds hG2 hZ hZi).2,
    (mixedDensityMass_bounds hG2 hZ hZi).2⟩

theorem selected_density_masses_eventually (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      1 < (C.giantCenter:ℝ) ∧ 0 < Construction.logCellMass C.giantCenter ∅ ∧
      PrimeCellFreezing.logCellMass
        (fun _ : Bool => (Construction.logCellMass C.giantCenter ∅)⁻¹)
        (fun _ => (C.giantCenter:ℝ)-1) (fun _ => (C.giantCenter:ℝ)+1) ≤ 64 ∧
      MixedCellIntegralFreezing.mixedLogMass 1 ((C.giantCenter:ℝ)-1)
        ((C.giantCenter:ℝ)+1) C.giantCenter smoothPartition
        (fun _ : Unit => (Construction.logCellMass C.giantCenter ∅)⁻¹)
        (fun _ => (C.giantCenter:ℝ)-1) (fun _ => (C.giantCenter:ℝ)+1) ≤ 64 := by
  filter_upwards [giant_density_masses_eventually] with L hL
  intro E C hblock hcenter
  exact hL C.giantCenter (by linarith)

theorem selected_density_errors_eventually (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      3*Real.exp (-Real.exp ((11/10000:ℝ)*L))*
        primeDensityMass C.giantCenter (Construction.logCellMass C.giantCenter ∅) ≤
          192*Real.exp (-Real.exp ((11/10000:ℝ)*L)) ∧
      3*Real.exp (-Real.exp ((11/10000:ℝ)*L))*
        mixedDensityMass C.giantCenter (Construction.logCellMass C.giantCenter ∅) ≤
          192*Real.exp (-Real.exp ((11/10000:ℝ)*L)) := by
  filter_upwards [selected_density_masses_eventually d Bs BD Bz k] with L hL
  intro E C hblock hcenter
  obtain ⟨_, _, hp, hm⟩ := hL E C hblock hcenter
  exact ⟨three_error_mass_le (Real.exp_nonneg _) hp,
    three_error_mass_le (Real.exp_nonneg _) hm⟩

end Ostmann.Arithmetic.HistorySelectedGiantDensityMass

end

end OAI
