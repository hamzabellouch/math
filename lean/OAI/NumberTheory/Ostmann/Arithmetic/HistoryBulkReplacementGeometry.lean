import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementGeometryBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementGeometryFrequency
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementGeometry
open Construction Conclusion HistoryCRTIntegration ScaleBudget Filter

def bulkModulus {l : ℕ} (h g : History l) (outside : List ℕ) (k : ℕ) : ℕ :=
  outside.prod * frequencyModulus h g (k + 2)

theorem selected_spectator_modulus_cap_eventually (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p : ℕ) ≤ Real.exp ((1 / 1000 : ℝ) * L)) →
      ∀ ds : Fin (2 * (bulkSize k L / 2)) → spectator.Sample,
      let outside := spectatorList spectator ds
      ∀ l ≤ k, ∀ h g : History l,
        h.Supported (frequencyBound Bs BD Bz k L) outside →
        g.Supported (frequencyBound Bs BD Bz k L) outside →
        0 < bulkModulus h g outside k ∧
          Real.log (bulkModulus h g outside k : ℝ) ≤ Real.exp (bulk.μ * L) := by
  filter_upwards [eventually_bulk_log_budget k (frequencyLogCoefficient Bs BD Bz k)
      (frequencyLogCoefficient_nonneg Bs BD Bz k),
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hbudget hm
  have hm' : 1 ≤ bulkSize k L := by exact_mod_cast hm
  intro spectator hspec ds
  dsimp only
  intro l hl h g hs gs
  have hprime : ∀ p ∈ spectatorList spectator ds, Nat.Prime p := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact spectator.prime (ds i).val (ds i).property
  have hlogs : ∀ p ∈ spectatorList spectator ds,
      Real.log (p : ℝ) ≤ Real.exp ((1 / 1000 : ℝ) * L) := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hspec (ds i)
  have hD : 0 < (spectatorList spectator ds).prod :=
    List.prod_pos (fun p hp => (hprime p hp).pos)
  have hQ := frequencyModulus_pos h g hs gs (k + 2)
  refine ⟨Nat.mul_pos hD hQ, ?_⟩
  rw [bulkModulus, Nat.cast_mul, Real.log_mul
    (by exact_mod_cast hD.ne') (by exact_mod_cast hQ.ne')]
  have hDlog := log_nat_product_le (spectatorList spectator ds)
    (Real.exp ((1 / 1000 : ℝ) * L)) (fun p hp => (hprime p hp).pos) hlogs
  have hcount : ((spectatorList spectator ds).length : ℝ) ≤ (bulkSize k L : ℝ) := by
    simp only [spectatorList, List.length_ofFn]
    exact_mod_cast (show 2 * (bulkSize k L / 2) ≤ bulkSize k L by omega)
  have hDlog' := hDlog.trans (mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _))
  have hQlog := frequencyModulus_log_le Bs BD Bz k L hl hm' h g hs gs
  apply (add_le_add hDlog' hQlog).trans
  convert hbudget using 1
  ring

theorem selected_spectator_geometryBounds_eventually (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) {dAP : ℝ} (hdAP : 0 < dAP) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p : ℕ) ≤ Real.exp ((1 / 1000 : ℝ) * L)) →
      ∀ ds : Fin (2 * (bulkSize k L / 2)) → spectator.Sample,
      let outside := spectatorList spectator ds
      ∀ l ≤ k, ∀ h g : History l,
        h.Supported (frequencyBound Bs BD Bz k L) outside →
        g.Supported (frequencyBound Bs BD Bz k L) outside →
        0 < bulkModulus h g outside k ∧
          GeometryBounds dAP L₀ (bulkModulus h g outside k) L := by
  filter_upwards [selected_spectator_modulus_cap_eventually Bs BD Bz hk,
    eventually_geometryBounds hdAP L₀] with L hcap hgeometry
  intro spectator hspec ds
  dsimp only
  intro l hl h g hs gs
  have hh := hcap spectator hspec ds l hl h g hs gs
  exact ⟨hh.1, hgeometry _ hh.1 hh.2⟩

end Ostmann.Arithmetic.HistoryBulkReplacementGeometry

end

end OAI
