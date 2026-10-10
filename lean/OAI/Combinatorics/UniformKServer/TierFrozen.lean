import Mathlib
import OAI.Combinatorics.UniformKServer.LevelSeparation
import OAI.Combinatorics.UniformKServer.FirstEdits

namespace OAI

                                 
section

/-! Noninsertions change no actual tier key, including its recycled label. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance indexDecEqFrozen : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqFrozen : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem frozen (r : ℝ) (K : ℕ) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : ¬TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N)
    (ω : Fin N→TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    key r K q c (n.val+1) τ ω p=key r K q c n.val τ ω p := by
  have hb : TierLabels.birth r K q c n.val=none := by
    rw [TierLabels.birth,dite_eq_left n.isLt,ite_eq_right hn]
  have hl := @CooldownLabels.label_none (Fin N) (instDecidableEqFin N)
    (Fintype.card X*K^2) (TierLabels.reserved r K q c) (TierLabels.birth r K q c) n.val hb
  have hv : TierLifetimes.live r K q c (n.val+1) τ=TierLifetimes.live r K q c n.val τ := by
    rw [TierLifetimes.live,dite_eq_left n.isLt,ite_eq_right hn]
  unfold key TierKeyProcess.key TierLabels.labels
  rw [hl,hv]

end UniformKServer.TierLabeledKeys
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqFrozen : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqFrozen : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqFrozen : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem uncovered_difference {I : Type*} (a b : Option I) :
    KeyEdits.uncovered a-KeyEdits.uncovered b≤ indicator a b := by
  by_cases he : a=b
  · simp only [he,sub_self,indicator,ite_true,le_refl]
  · have ha := (KeyEdits.uncovered_bounds a).2
    have hb := (KeyEdits.uncovered_bounds b).1
    simp only [indicator,ite_eq_right he]
    linarith

def tierUncovered (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) : ℝ :=
  KeyEdits.uncovered (D.tierKey ω t i p)

theorem tierUncovered_nonneg (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) :
    0≤D.tierUncovered ω t i p := (KeyEdits.uncovered_bounds _).1

theorem tierUncovered_covered (D : Data X N H) (n : Fin N) (i : Fin H)
    (hi : D.qualify i n) (ω : Tape D) : D.tierUncovered ω (n.val+1) i (D.center n)=0 := by
  have h := tier_coverage D n i hi ω
  unfold tierUncovered
  cases hk : D.tierKey ω (n.val+1) i (D.center n) with
  | none => simp [hk] at h
  | some l => rfl

theorem tierUncovered_motion (D : Data X N H) (n : Fin N) (i : Fin H) (y : X) :
    D.r*D.law.expect (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y)≤
      if D.qualify i n then 0 else (4+2*Real.log (1+(D.K i:ℝ)^2))*dist (D.center n) y := by
  by_cases hq : D.qualify i n
  · rw [ite_eq_left hq]
    have hm := D.law.expect_mono (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y) (fun _=>0) (fun ω=>by
      rw [tierUncovered_covered D n i hq ω]
      simpa only [zero_sub,neg_nonpos] using tierUncovered_nonneg D ω (n.val+1) i y)
    rw [Law.expect_const] at hm
    exact mul_nonpos_of_nonneg_of_nonpos D.positive.le hm
  · rw [ite_eq_right hq]
    have hlam : 0≤Real.log (1+(D.K i:ℝ)^2) := Real.log_nonneg (by nlinarith [sq_nonneg (D.K i:ℝ)])
    by_cases hd : dist (D.center n) y<D.r/4
    · have hm := D.law.expect_mono _ _ (fun ω=>uncovered_difference
        (D.tierKey ω (n.val+1) i (D.center n)) (D.tierKey ω (n.val+1) i y))
      have hs := mul_le_mul_of_nonneg_left
        (hm.trans (tier_separation D (n.val+1) i (D.center n) y hd)) D.positive.le
      have he : D.r*(2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) y/D.r)=
          2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) y := by field_simp [ne_of_gt D.positive]
      rw [he] at hs
      exact hs.trans (by nlinarith [dist_nonneg (x:=D.center n) (y:=y)])
    · have hm := D.law.expect_mono (fun ω=>D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω (n.val+1) i y) (fun _=>1) (fun ω=>by
        have ha := (KeyEdits.uncovered_bounds (D.tierKey ω (n.val+1) i (D.center n))).2
        have hb := tierUncovered_nonneg D ω (n.val+1) i y
        change KeyEdits.uncovered _-_≤_
        linarith)
      rw [Law.expect_const] at hm
      have hs := mul_le_mul_of_nonneg_left hm D.positive.le
      have hd' := le_of_not_gt hd
      have hprod := mul_nonneg hlam (dist_nonneg (x:=D.center n) (y:=y))
      nlinarith

end UniformKServer.LevelMap.Data

end


end

end OAI
