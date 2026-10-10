import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction HistoryPairPattern HistoryActiveCoordinates HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open scoped ContDiff
attribute [local instance] Classical.propDecidable
variable {l : ℕ}

theorem jointInsert_exp (h k : History l) {κ ι : Type*}
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (hbackground : ∀i,0<background i)
    (u : κ → ℝ) (x : ι → ℝ) :
    jointInsert h k eG eB background (fun j=>Real.exp (u j)) (fun j=>Real.exp (x j))=
      fun i=>Real.exp (jointInsert h k eG eB (fun j=>Real.log (background j)) u x i) := by
  funext i
  by_cases hb : i∈bulkCoordinates h k <;> by_cases hg : i∈giantCoordinates h k <;>
    simp only [jointInsert,HistoryActiveCoordinates.insert,hb,hg,↓reduceDIte,Function.comp_apply,Real.exp_log (hbackground i)]

theorem jointInsert_contDiff (h k : History l) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>jointInsert h k eG eB background z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hb : i∈bulkCoordinates h k <;> by_cases hg : i∈giantCoordinates h k <;>
    simp only [jointInsert,HistoryActiveCoordinates.insert,hb,hg,↓reduceDIte,Function.comp_apply] <;> fun_prop

theorem log_contDiff_jointInsert (h k : History l) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k → ℝ) (hbackground : ∀i,0<background i)
    (f : (PairKey h k→ℝ)→ℂ)
    (hf : ContDiff ℝ ∞ (fun y : PairKey h k→ℝ=>f (fun i=>Real.exp (y i)))) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      f (jointInsert h k eG eB background (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) := by
  simpa only [Function.comp_def,←jointInsert_exp h k eG eB background hbackground] using
    hf.comp (jointInsert_contDiff h k eG eB (fun i=>Real.log (background i)))

theorem correctedPairedRealXi_joint_log_contDiff
    {V : ℕ→ℕ} {outside : List ℕ} (b s : ℕ) (X tb td G : ℝ) (hX : 0<X)
    (houtside : ∀q∈outside,0<q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ→ℝ) (cellKey : τ→PairKey h k)
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k→ℝ) (hbackground : ∀i,0<background i) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey
        (jointInsert h k eG eB background (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :=
  log_contDiff_jointInsert h k eG eB background hbackground _
    (correctedPairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks
      T U Hkeys Ukeys S cellCenter cellKey)

theorem correctedPairedRealXi_joint_log_continuous
    {V : ℕ→ℕ} {outside : List ℕ} (b s : ℕ) (X tb td G : ℝ) (hX : 0<X)
    (houtside : ∀q∈outside,0<q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ→ℝ) (cellKey : τ→PairKey h k)
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k→ℝ) (hbackground : ∀i,0<background i) :
    Continuous (fun z : (κ→ℝ)×(ι→ℝ)=>
      correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey
        (jointInsert h k eG eB background (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :=
  (correctedPairedRealXi_joint_log_contDiff b s X tb td G hX houtside h k hs ks
    T U Hkeys Ukeys S cellCenter cellKey eG eB background hbackground).continuous

theorem pairedRealXi_joint_log_contDiff
    {V : ℕ→ℕ} {outside : List ℕ} (b s : ℕ) (X tb td G : ℝ) (hX : 0<X)
    (houtside : ∀q∈outside,0<q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k→ℝ) (hbackground : ∀i,0<background i) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      pairedRealXi b s X tb td G h k hs ks
        (jointInsert h k eG eB background (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :=
  log_contDiff_jointInsert h k eG eB background hbackground _
    (pairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks)

theorem pairedRealXi_joint_log_continuous
    {V : ℕ→ℕ} {outside : List ℕ} (b s : ℕ) (X tb td G : ℝ) (hX : 0<X)
    (houtside : ∀q∈outside,0<q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (background : PairKey h k→ℝ) (hbackground : ∀i,0<background i) :
    Continuous (fun z : (κ→ℝ)×(ι→ℝ)=>
      pairedRealXi b s X tb td G h k hs ks
        (jointInsert h k eG eB background (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :=
  (pairedRealXi_joint_log_contDiff b s X tb td G hX houtside h k hs ks
    eG eB background hbackground).continuous

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
