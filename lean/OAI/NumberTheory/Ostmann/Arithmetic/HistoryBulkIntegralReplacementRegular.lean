import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementIntegrated
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralParameter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction HistoryBulkPriorGrid HistoryPrincipalIntegralAverage PrimeCellFreezing
open HistoryPrincipalIntegralParameter
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in

theorem bulk_sample_log_mem (L : ℝ) (E : Finset ℕ)
    (hZ : 0<harmonicPrimeMass (bulkPrimeBand L E))
    (p : ι→(bulkPrimeSource L E hZ).Sample) :
    (fun i=>Real.log ((p i).val:ℝ)) ∈
      logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L) := by
  intro i hi
  have hm := (mem_bulkClosedSupport L (p i).val).mp
    (bulkPrimeBand_subset_closed L E (p i).property)
  exact ⟨hm.2.1,hm.2.2⟩

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem sampled_scalar_continuousOn (L : ℝ) (E : Finset ℕ)
    (hZ : 0<harmonicPrimeMass (bulkPrimeBand L E)) (S : Set (κ→ℝ))
    (f : (κ→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContinuousOn (fun z : (κ→ℝ)×(ι→ℝ)=>
      f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))
      (S ×ˢ logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L)))
    (p : ι→(bulkPrimeSource L E hZ).Sample) :
    ContinuousOn (fun t=>f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ))) S := by
  have hh := hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun t ht=>⟨ht,bulk_sample_log_mem L E hZ p⟩)
  have he : (fun i=>Real.exp (Real.log ((p i).val:ℝ)))=(fun i=>((p i).val:ℝ)) := by
    funext i
    exact Real.exp_log (by exact_mod_cast ((bulkPrimeSource L E hZ).prime (p i).val (p i).property).pos)
  change ContinuousOn (fun t=>f (fun i=>Real.exp (t i))
    (fun i=>Real.exp (Real.log ((p i).val:ℝ)))) S at hh
  rw [he] at hh
  exact hh

omit [DecidableEq κ] in

theorem bulkMain_continuousOn (L : ℝ) (E : Finset ℕ) {M : ℕ} [NeZero M]
    (F : (ι→(ZMod M)ˣ)→ℂ) (S : Set (κ→ℝ)) (hS : IsCompact S)
    (f : (κ→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContinuousOn (fun z : (κ→ℝ)×(ι→ℝ)=>
      f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))
      (S ×ˢ logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L))) :
    ContinuousOn (fun t=>bulkMain L E F (f (fun i=>Real.exp (t i)))) S := by
  exact (primeIntegral_continuousOn hS (fun _ : ι=>bulkLogLower L)
    (fun _=>bulkLogUpper L) (fun _=>bulkNormalizer L E)
    (fun _=>Real.exp_pos _) (fun t=>f (fun i=>Real.exp (t i))) hf).mul continuousOn_const

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
