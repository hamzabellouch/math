import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

lemma restore_zero_add (pins : Set V) (h k : Free pins → ℝ) (x : V) :
    restore pins (fun _ => 0) (h+k) x =
      restore pins (fun _ => 0) h x + restore pins (fun _ => 0) k x := by
  by_cases hx : x ∈ pins <;> simp [restore, hx]

lemma restore_zero_smul (pins : Set V) (c : ℝ) (h : Free pins → ℝ) (x : V) :
    restore pins (fun _ => 0) (c • h) x = c * restore pins (fun _ => 0) h x := by
  by_cases hx : x ∈ pins <;> simp [restore, hx]

lemma convex_zeroBody (G : SimpleGraph V) (pins : Set V) :
    Convex ℝ (conditionalBody G pins (fun _ => 0)) := by
  intro h hh k hk s t hs ht hst x y hxy
  simp only [restore_zero_add, restore_zero_smul]
  calc
    |s * restore pins (fun _ => 0) h x + t * restore pins (fun _ => 0) k x -
        (s * restore pins (fun _ => 0) h y + t * restore pins (fun _ => 0) k y)| =
      |s * (restore pins (fun _ => 0) h x-restore pins (fun _ => 0) h y) +
       t * (restore pins (fun _ => 0) k x-restore pins (fun _ => 0) k y)| := by congr 1; ring
    _ ≤ |s * (restore pins (fun _ => 0) h x-restore pins (fun _ => 0) h y)| +
       |t * (restore pins (fun _ => 0) k x-restore pins (fun _ => 0) k y)| := abs_add_le _ _
    _ ≤ s*1+t*1 := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]; gcongr; exacts [hh x y hxy,hk x y hxy]
    _ = 1 := by linarith

lemma neg_zeroBody (G : SimpleGraph V) (pins : Set V)
    {h : Free pins → ℝ} (hh : h ∈ conditionalBody G pins (fun _ => 0)) :
    -h ∈ conditionalBody G pins (fun _ => 0) := by
  have he := body_neg_preimage G pins (fun _ => 0)
  simp only [neg_zero] at he
  change h ∈ Neg.neg ⁻¹' conditionalBody G pins (fun _ => 0)
  rw [← he]
  exact hh

lemma compact_zeroBody [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (pins : Set V) (hp : pins.Nonempty) :
    IsCompact (conditionalBody G pins (fun _ => 0)) := by
  choose p hpin using hp
  let path (x : V) : G.Walk x p := Classical.choice (hc x p)
  let R (x : Free pins) : ℝ := (path x).length
  apply isCompact_Icc.of_isClosed_subset (closed_conditionalBody G pins _) (s := Icc (-R) R)
  intro h hh
  constructor <;> intro x
  · have hb := bound_along_walk G (restore pins (fun _ => 0) h) hh (path x)
    simpa [restore, x.2, hpin, R] using (abs_le.mp hb).1
  · have hb := bound_along_walk G (restore pins (fun _ => 0) h) hh (path x)
    simpa [restore, x.2, hpin, R] using (abs_le.mp hb).2

end ExtremalEdges

end

end OAI
