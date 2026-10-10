import OAI.Geometry.PeriodicTiling.VoxelMeasure
import OAI.Geometry.PeriodicTiling.ClosedCoverChains
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped ENNReal

def auxiliaryCube (m : ℕ) (c : Space 3) : Set (Space 3) :=
  Metric.closedBall c ((m : ℝ) / 2)

theorem auxiliaryCube_isClosed (m : ℕ) (c : Space 3) :
    IsClosed (auxiliaryCube m c) := Metric.isClosed_closedBall

theorem auxiliaryCube_measurableSet (m : ℕ) (c : Space 3) :
    MeasurableSet (auxiliaryCube m c) := (auxiliaryCube_isClosed m c).measurableSet

theorem auxiliaryCube_nonempty (m : ℕ) (c : Space 3) :
    (auxiliaryCube m c).Nonempty :=
  ⟨c, Metric.mem_closedBall_self (by positivity)⟩

theorem auxiliaryCube_volume (m : ℕ) (c : Space 3) :
    volume (auxiliaryCube m c) = ((m ^ 3 : ℕ) : ℝ≥0∞) := by
  rw [auxiliaryCube, closedBall_volume c (by positivity)]
  rw [show 2 * ((m : ℝ) / 2) = (m : ℝ) by ring]
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg m) 3, ENNReal.ofReal_natCast]
  simp only [Nat.cast_pow]

theorem auxiliaryCube_translate (m : ℕ) (c : Space 3) :
    {x : Space 3 | x - c ∈ auxiliaryCube m 0} = auxiliaryCube m c := by
  ext x
  simp only [mem_ofPred_eq, auxiliaryCube, Metric.mem_closedBall,
    dist_eq_norm, sub_zero]

theorem auxiliaryCube_aedisjoint {m : ℕ} (hm : 0 < m)
    {c c' : Space 3} (hsep : (m : ℝ) ≤ ‖c - c'‖) :
    AEDisjoint volume (auxiliaryCube m c) (auxiliaryCube m c') := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hballs : Disjoint (Metric.ball c ((m : ℝ) / 2))
      (Metric.ball c' ((m : ℝ) / 2)) := by
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    linarith
  exact hballs.aedisjoint.congr
    (closedBall_ae_eq_ball c (by positivity))
    (closedBall_ae_eq_ball c' (by positivity))

theorem auxiliaryCube_inter_norm_le {m : ℕ} {c c' : Space 3}
    (h : (auxiliaryCube m c ∩ auxiliaryCube m c').Nonempty) :
    ‖c' - c‖ ≤ (m : ℝ) := by
  obtain ⟨x, hx, hx'⟩ := h
  have hxle : dist x c ≤ (m : ℝ) / 2 := hx
  have hxle' : dist x c' ≤ (m : ℝ) / 2 := hx'
  have ht := dist_triangle c' x c
  rw [dist_comm c' x, dist_eq_norm c' c] at ht
  linarith

theorem auxiliaryCube_locallyFinite (m : ℕ) (C : Set (Space 3))
    (hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite) :
    LocallyFinite (fun c : C => auxiliaryCube m c) := by
  intro x
  have hindex : {c : C | (c : Space 3) ∈
      Metric.closedBall x ((m : ℝ) / 2 + 1)}.Finite := by
    have hf := Set.Finite.preimage
      (f := fun c : C => (c : Space 3)) Subtype.val_injective.injOn
      (hfin (Metric.closedBall x ((m : ℝ) / 2 + 1)) Metric.isBounded_closedBall)
    exact hf.subset fun c hc => ⟨c.property, hc⟩
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), hindex.subset ?_⟩
  rintro c ⟨y, hy, hyx⟩
  have hyc : dist y (c : Space 3) ≤ (m : ℝ) / 2 := hy
  have hyx' : dist y x < 1 := hyx
  change dist (c : Space 3) x ≤ (m : ℝ) / 2 + 1
  have ht := dist_triangle (c : Space 3) y x
  rw [dist_comm (c : Space 3) y] at ht
  linarith

theorem auxiliaryCube_cover_of_ae (m : ℕ) (C : Set (Space 3))
    (hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite)
    (hcover : ∀ᵐ x ∂volume, ∃ c : C, x ∈ auxiliaryCube m c) :
    ∀ x, ∃ c : C, x ∈ auxiliaryCube m c :=
  closed_locallyFinite_cover_of_ae volume (fun c : C => auxiliaryCube m c)
    (fun c => auxiliaryCube_isClosed m c) (auxiliaryCube_locallyFinite m C hfin) hcover

end PeriodicTilingThree

end

end OAI
