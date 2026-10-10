import Mathlib
import OAI.Combinatorics.UniformKServer.TierLabeledEdits

namespace OAI

                                
section

/-! At a heavy request the inner ball has no short-edit error: the completed
heavy key shadows every short tier, while a qualifying tier covers that ball. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ} {J : Type*}
local instance indexDecEqInner : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqInner : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem coverage_near (r : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K) (q : Fin N→Prop)
    (c : Fin N→X) (n : Fin N) (hn : q n) (τ : TierLifetimes.Tape N)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (hp : dist (c n) p≤r/2) :
    (key r K q c (n.val+1) τ ω p).isSome=true := by
  obtain ⟨i,hi,hd⟩ := TierLifetimes.coverage r hr.le K (by omega) q c n hn τ
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hcover : (ω i).val (c i,p)=true := by
    apply TierRadius.cover_inner _ r hlam hr (ω i) _ _
    have ht := dist_triangle (c i) (c n) p
    rw [dist_comm (c i) (c n)] at ht
    linarith
  have hsome : (TierKeyProcess.key r K q c (n.val+1) τ ω p).isSome=true := by
    change (List.find? (fun j => (ω j).val (c j,p))
      ((TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·))).isSome=true
    rw [List.isSome_find?]
    exact List.any_eq_true.mpr ⟨i,(mem_sort _).mpr hi,hcover⟩
  simpa only [key,Option.isSome_map] using hsome

theorem annular_stationary (r γ : ℝ) (hr : 0<r) (hγ : γ≤1/2) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (heavy : Prop)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J)
    (he : heavy→dist (c n) p≤γ*r→∀ τ, (earlier τ).isSome=true) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)+
        KeyEdits.uncovered (key r K q c (n.val+1) τ ω p)-KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      98/(K:ℝ)*(if dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) then 1 else 0) := by
  by_cases hh : heavy ∧ dist (c n) p≤γ*r
  · have hp : dist (c n) p≤r/2 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    have hz (τ : TierLifetimes.Tape N) := coverage_near r hr K hK q c n hn.1 τ ω p hp
    have hn' : ¬(dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p)) := by aesop
    simp only [ite_eq_right hn',mul_zero]
    calc
      _ ≤ (TierLifetimes.law K hq).expect (fun _ => 0) := by
        apply (TierLifetimes.law K hq).expect_mono
        intro τ
        cases heq : earlier τ with
        | none => have := he hh.1 hh.2 τ; simp [heq] at this
        | some j =>
          rw [KeyEdits.shadowed]
          cases hzkey : key r K q c (n.val+1) τ ω p with
          | none => have hzt := hz τ; simp [hzkey] at hzt
          | some i =>
            have hu := (KeyEdits.uncovered_bounds (key r K q c n.val τ ω p)).1
            simpa only [KeyEdits.uncovered,Option.isNone_some,Bool.false_eq_true,ite_false,
              zero_add,zero_sub,neg_nonpos] using hu
      _ = _ := Law.expect_const _ _
  · have hc : ¬heavy ∨ γ*r<dist (c n) p := by
      by_cases h : heavy
      · exact Or.inr (lt_of_not_ge (fun hp => hh ⟨h,hp⟩))
      · exact Or.inl h
    have h := stationary r hr K hK hq q c n hn ω p earlier label later
    by_cases hp : dist (c n) p≤22*r
    · have hcond : dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) := ⟨hp,hc⟩
      simpa only [ite_eq_left hp,ite_eq_left hcond,mul_one,show (2:ℝ)*(49/(K:ℝ))=98/(K:ℝ) by ring] using h
    · simpa only [ite_eq_right hp,ite_eq_right (not_and_of_not_left _ hp),mul_zero] using h


theorem annular_mover (r γ : ℝ) (hr : 0<r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (heavy : Prop)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J)
    (he : heavy→dist (c n) p≤γ*r→∀ τ, (earlier τ).isSome=true) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)-
        KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      49/(K:ℝ)*(if dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) then 1 else 0) := by
  by_cases hh : heavy ∧ dist (c n) p≤γ*r
  · have hn' : ¬(dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p)) := by aesop
    simp only [ite_eq_right hn',mul_zero]
    calc
      _ ≤ (TierLifetimes.law K hq).expect (fun _ => 0) := by
        apply (TierLifetimes.law K hq).expect_mono
        intro τ
        cases heq : earlier τ with
        | none => have := he hh.1 hh.2 τ; simp [heq] at this
        | some j =>
          rw [KeyEdits.shadowed]
          simpa only [zero_sub,neg_nonpos] using
            (KeyEdits.uncovered_bounds (key r K q c n.val τ ω p)).1
      _ = _ := Law.expect_const _ _
  · have hc : ¬heavy ∨ γ*r<dist (c n) p := by
      by_cases h : heavy
      · exact Or.inr (lt_of_not_ge (fun hp => hh ⟨h,hp⟩))
      · exact Or.inl h
    have h := mover r hr K hK hq q c n hn ω p earlier label later
    by_cases hp : dist (c n) p≤22*r
    · simpa only [ite_eq_left hp,ite_eq_left (And.intro hp hc),mul_one] using h
    · simpa only [ite_eq_right hp,ite_eq_right (not_and_of_not_left _ hp),mul_zero] using h

end UniformKServer.TierLabeledKeys

end


end

end OAI
