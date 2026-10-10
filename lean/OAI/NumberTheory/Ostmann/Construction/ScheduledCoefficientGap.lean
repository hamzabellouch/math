import OAI.NumberTheory.Ostmann.Construction.ScheduledCompensationBounds
import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges

namespace OAI

/-! # The true initial cutoffs supply the coefficient-supported transfer gap -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem selected_scheduled_coefficient_gap
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hk : 1 ≤ k) (hm : 64 ≤ (spectatorBulkCount k L : ℝ))
    (hP : ∀ p ∈ P, p.Prime) (hG : 1 ≤ G) (hD : |Dlog - 2 * cd| ≤ 2)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (b d : ℕ) (sl sr : Fin d → P) (fallback : P)
    {I : Type} (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (φ : ℝ → ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (u : TreeLeafIndex n × Fin 4 → P)
    (right : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b) → P)
    (hright : ∀ i, (right i : ℕ) ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N Y hi D) Qb top (cs.drop (n + 1)) n (b + b) i)
    (p XR : ℕ) (w : ℤ) (hXR : Real.exp (G - 1) ≤ (XR : ℝ)) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    pivotBound (n + 1) = scheduledPivotBound G cs n →
    childBound (n + 1) = V n →
    movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
        g Dq S ψ X lo upper) φ (fun _ => G) n
      (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b) w
      (movingRestoreSample n (scheduledSmallLength (cs.drop (n + 1))) (b + b) u right) p XR ≠ 0 →
    2 * pivotBound (n + 1) * childBound (n + 1) < XR * (∏ i, (right i : ℕ)) := by
  intro width T W V hpivot hchild hcoeff
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hDl : 2 * cd - 2 ≤ Dlog := by linarith only [(abs_le.mp hD).1]
  have hDu : Dlog ≤ 2 * cd + 2 := by linarith only [(abs_le.mp hD).2]
  have hr := scheduled_original_retained_product_lower Subtype.val
    (fun x => (hP _ x.property).pos) b d top cs cb cd G Y width Dlog sl sr fallback
    q g Dq S ψ X lo upper outside μ childBound pivotBound V φ n (by omega) u right p XR w hXR hDl
    (fun j => scheduledSmallLower_prime_bound A B N hi top Y D Qb (cs.drop (n + 1)) n
      (b + b) j _ (hright _)) hcoeff
  have hg := selected_scheduled_rigidity_margin (top := top) (cb := cb) (width := width)
    k n hn hk hm hDu herror hBD hBz hcs
  have hgap := scheduled_integer_rigidity G Y cb cd width Dlog (spectatorBulkCount k L)
    top cs n (XR * ∏ i, (right i : ℕ)) hG (by dsimp only [width]; positivity) hbudget hr hg
  rwa [hpivot, hchild]

end Ostmann

end OAI
