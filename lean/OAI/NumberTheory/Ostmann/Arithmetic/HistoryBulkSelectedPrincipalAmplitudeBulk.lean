import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantIntegerReferenceSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitudeDensity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude
open Construction Conclusion HistoryBulkIntegralReplacement HistoryBulkPriorGrid PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem bulkSample_log_mem (C : InitialSourceChoice d Bs BD Bz k L E)
    {ι : Type*} (u : ι→C.bulk.Sample) :
    (fun i=>Real.log ((u i).val:ℝ))∈
      logRectangle (fun _=>bulkLogLower L) (fun _=>bulkLogUpper L) := by
  intro i _
  exact harmonicBand_log_support C.bulkPositive (u i)

theorem bulkBounds_norm_original_sample (C : InitialSourceChoice d Bs BD Bz k L E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ℝ} {f : (ι→ℝ)→ℂ}
    (hf : BulkBounds k L A f) (u : ι→C.bulk.Sample) :
    ‖f (fun i=>((u i).val:ℝ))‖≤Real.exp (A*((bulkSize k L:ℝ)+1)) := by
  have h := hf.norm (fun i=>Real.log ((u i).val:ℝ)) (bulkSample_log_mem C u)
  have he : (fun i=>Real.exp (Real.log ((u i).val:ℝ)))=(fun i=>((u i).val:ℝ)) := by
    funext i
    exact Real.exp_log (by exact_mod_cast (C.bulk.prime (u i).val (u i).property).pos)
  rwa [he] at h

end Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude

end

end OAI
