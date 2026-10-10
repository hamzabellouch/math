import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetCost
import OAI.NumberTheory.Ostmann.Construction.LogCellPrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds
open PrimeCellReplacement LogCellPartition PrimeCellActualErrorBudget

theorem original_giant_principal_masses (M : ℕ) (hM : 0 < M) (m : ℕ)
    (G : ℝ) (E : Finset ℕ) (hG : 2 ≤ G) (hZ : 0 < Construction.logCellMass G E)
    (hinv : (Construction.logCellMass G E)⁻¹ ≤ Real.exp (2*((m:ℝ)+1))) :
    (0 ≤ principalMass M (fun _ : Bool=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G E) ∧
     principalMass M (fun _ : Bool=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G E) ≤ Real.exp (10*((m:ℝ)+1))) ∧
    (0 ≤ mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Construction.logCellMass G E) ∧
     mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Construction.logCellMass G E) ≤
        Real.exp (10*((m:ℝ)+1))) :=
  ⟨giant_principalMass_bounds M hM m hG hZ hinv,
    giant_mixedPrincipalMass_bounds M hM m hG hZ hinv⟩

theorem mass_envelope_le_smoothGrowth (k : ℕ) (σ L : ℝ) :
    Real.exp (10*((Conclusion.bulkSize k L:ℝ)+1)) ≤ smoothGrowthFactor k 10 σ L := by
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ 10*((Conclusion.bulkSize k L:ℝ)+1) := by positivity
  nlinarith [mul_nonneg hnonneg (Real.exp_nonneg (σ*L))]

theorem original_giant_principal_masses_smoothGrowth (k M : ℕ) (hM : 0 < M)
    (σ L G : ℝ) (E : Finset ℕ) (hG : 2 ≤ G) (hZ : 0 < Construction.logCellMass G E)
    (hinv : (Construction.logCellMass G E)⁻¹ ≤
      Real.exp (2*((Conclusion.bulkSize k L:ℝ)+1))) :
    (0 ≤ principalMass M (fun _ : Bool=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G E) ∧
     principalMass M (fun _ : Bool=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G E) ≤ smoothGrowthFactor k 10 σ L) ∧
    (0 ≤ mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Construction.logCellMass G E) ∧
     mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Construction.logCellMass G E) ≤
        smoothGrowthFactor k 10 σ L) := by
  obtain ⟨hp,hm⟩ := original_giant_principal_masses M hM (Conclusion.bulkSize k L) G E hG hZ hinv
  exact ⟨⟨hp.1,hp.2.trans (mass_envelope_le_smoothGrowth k σ L)⟩,
    ⟨hm.1,hm.2.trans (mass_envelope_le_smoothGrowth k σ L)⟩⟩

end Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds

end

end OAI
