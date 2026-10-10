import Mathlib
import OAI.Probability.Ballisticity.Crossings.CoordinateHitExact
import OAI.Probability.Ballisticity.Estimates.CurvePrefix

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma curveWordEvent_cons_mem {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x u : Lattice d) (w : List (Lattice d)) (X : Path d) :
    X ∈ curveWordEvent ℓ f b B H x (u::w) ↔ ∃ n,
      X ∈ CurvePrefixAt ℓ f x b B H n ∧ X n=x+u ∧
      (fun k => X (n+k)) ∈ curveWordEvent ℓ f b B H (x+u) w := by
  simp only [curveWordEvent,Set.mem_iUnion,Set.mem_inter_iff,FutureEvent,Set.mem_ofPred_eq]
  apply exists_congr; intro n
  by_cases hn : X n=x+u
  · simp [hn]
  · simp [hn]

lemma curveWordEvent_disjoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x : Lattice d) (w v : List (Lattice d))
    (hlen : w.length=v.length) (hne : w≠v) :
    Disjoint (curveWordEvent ℓ f b B H x w) (curveWordEvent ℓ f b B H x v) := by
  induction w generalizing x v with
  | nil => cases v <;> simp_all
  | cons u w ih =>
    cases v with
    | nil => simp at hlen
    | cons u' w' =>
      apply Set.disjoint_left.mpr
      intro X hX hY
      obtain ⟨n,hn,hxu,hxt⟩ := (curveWordEvent_cons_mem ℓ f b B H x u w X).mp hX
      obtain ⟨m,hm,hxu',hxt'⟩ := (curveWordEvent_cons_mem ℓ f b B H x u' w' X).mp hY
      have hnm : n=m := by
        by_contra h
        exact Set.disjoint_left.mp (curvePrefixAt_disjoint ℓ f x b B H h) hn hm
      subst m
      have huu : u=u' := add_left_cancel (hxu.symm.trans hxu')
      subst u'
      exact Set.disjoint_left.mp (ih (x+u) w' (by simpa using hlen)
        (fun h => hne (congrArg (List.cons u) h))) hxt hxt'

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma coordinate_hitAt_recordPrefix {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ} (hH : 0 < H)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n) :
    (fun j => X j-x) ∈ RecordIndexPrefix (realPosition (step e)) H n := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0=0 := by simp [Y,h0]
  have hheight := coordinate_hitAt_exact e x X h0 hnn H n hX
  have hadd (u v : Lattice d) : signedHeight e (u-v)=signedHeight e u-signedHeight e v := by
    simp only [signedHeight,Pi.sub_apply]
    split_ifs <;> ring
  have hfirst : Y ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · simp only [Y,hadd,hheight,add_sub_cancel_left]
    · intro j hj
      have hh := (hX.2 j hj).2
      change dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(H:ℝ) at hh
      rw [signedHeight_projection,signedHeight_projection] at hh
      change signedHeight e (X j-x) < (H:ℤ)
      rw [hadd]
      exact_mod_cast (show (signedHeight e (X j):ℝ)-(signedHeight e x:ℝ) < (H:ℝ) by linarith)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hh := hfirst.1
    rw [hn0,hy0] at hh
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero] at hh
    omega
  have hrec := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) H n Y hfirst
  have hsteps (j : ℕ) : signedHeight e (Y (j+1)) ≤ signedHeight e (Y j)+1 := by
    obtain ⟨g,hg⟩ := hnn j
    have he : Y (j+1)=Y j+step g := by dsimp [Y]; rw [hg]; abel
    rw [he]
    exact signedHeight_step_le e _ g
  have hcount := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Y hsteps hrec
  rw [hfirst.1,hy0,show signedHeight e (0:Lattice d)=0 by simp [signedHeight],zero_add] at hcount
  have hr : Y ∈ RecordIndexPrefix ℓ H n := by
    refine ⟨hn,hrec,by exact_mod_cast hcount.symm,?_⟩
    intro j hj
    have hh : dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hX.2 j hj).1
      · have hh := hX.1
        change dot (realPosition x) ℓ+(H:ℝ) ≤ dot (realPosition (X j)) ℓ at hh
        linarith [show (0:ℝ) ≤ H by positivity]
    change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j-x)) ℓ
    rw [dot_realPosition_sub]
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,sub_nonneg] using hh
  exact hr

lemma recordPrefix_lower {d : ℕ} (ℓ : Vector d) (X : Path d) {H n j : ℕ}
    (hX : X ∈ RecordIndexPrefix ℓ H n) (hj : j ≤ H) :
    ∃ a ≤ n, X ∈ RecordOrZeroPrefix ℓ j a := by
  classical
  by_cases hj0 : j = 0
  · exact ⟨0,Nat.zero_le _,by simp [RecordOrZeroPrefix,hj0]⟩
  have hex : ∃ a, j ≤ recordCount ℓ X a := ⟨n,by rw [hX.2.2.1]; exact hj⟩
  let a := Nat.find hex
  have ha : j ≤ recordCount ℓ X a := Nat.find_spec hex
  have han : a ≤ n := Nat.find_min' hex (by rw [hX.2.2.1]; exact hj)
  have ha0 : 0 < a := by
    by_contra! hn
    have he : a = 0 := Nat.eq_zero_of_le_zero hn
    simp only [he,recordCount_zero] at ha
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha0)
  have hklt : recordCount ℓ X k < j := Nat.lt_of_not_ge
    (Nat.find_min hex (by omega))
  have hrec : StrictRecord ℓ X a := by
    by_contra hn
    rw [hk,recordCount_succ,ite_eq_right (by simpa only [hk,Nat.succ_eq_add_one] using hn),Nat.add_zero] at ha
    omega
  have hc : recordCount ℓ X a = j := by
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)]
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)] at ha
    omega
  refine ⟨a,han,?_⟩
  rw [RecordOrZeroPrefix,ite_eq_right hj0]
  exact ⟨ha0,hrec,hc,fun k hk => hX.2.2.2 k (hk.trans han)⟩

lemma curvePrefix_iff {d : ℕ} (e f : Direction d) (x : Lattice d) (b : ℕ → ℝ)
    (z : ℝ) {H : ℕ} (hH : 0 < H) (X : Path d)
    (h0 : X 0 = x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ CurvePrefix (realPosition (step e)) f x b z H ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition (realPosition (step e)) j
        (fun k => X k-x))-b j| ≤ z := by
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine ⟨Set.mem_iUnion.mpr ⟨n,hn.1⟩,?_⟩
    intro j hj
    obtain ⟨a,ha,hr,hb⟩ := hn.2 j hj
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hb
  · rintro ⟨hX,hbound⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine Set.mem_iUnion.mpr ⟨n,hn,?_⟩
    intro j hj
    obtain ⟨a,ha,hr⟩ := recordPrefix_lower _ (fun k => X k-x)
      (coordinate_hitAt_recordPrefix e x X h0 hnn hH hn) hj
    refine ⟨a,ha,hr,?_⟩
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hbound j hj

end DirectionalTransience

end

end

end OAI
