import Mathlib
import OAI.Combinatorics.UniformKServer.RadiusRoster
import OAI.Combinatorics.UniformKServer.PiFirstHit
import OAI.Combinatorics.UniformKServer.TierRadius

namespace OAI

                               
section

/-! The actual persistent-radius tape controls all roster keys at once;
conditioning on arbitrary independent lifetimes leaves these estimates valid. -/
noncomputable section
namespace UniformKServer.TierKeys
open FiniteProbability Finset
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [LinearOrder I] {X : Type} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def key (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r) (p : X) : Option I :=
  is.find? (fun i => (ω i).val (c i,p))

omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_mem (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r)
    (p : X) (i : I) (hi : key lam r is c ω p=some i) : i ∈ is := by
  exact List.mem_of_find?_eq_some hi

omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_covers (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r)
    (p : X) (i : I) (hi : key lam r is c ω p=some i) : (ω i).val (c i,p)=true := by
  exact List.find?_some (p:=fun j => (ω j).val (c j,p)) hi

omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_cons (lam r : ℝ) (is : List I) (i : I) (c : I → X)
    (ω : I → TierRadius.Sample (X:=X) lam r) (p : X) :
    key lam r (i::is) c ω p=if (ω i).val (c i,p) then some i else key lam r is c ω p := by
  unfold key
  rw [List.find?_cons]
  cases (ω i).val (c i,p) <;> rfl

omit [Fintype I] [LinearOrder I] in
theorem disagreement (lam r : ℝ) (is : List I) (hn : is.Nodup) (c : I → X)
    (ω : I → TierRadius.Sample (X:=X) lam r) (x y : X) :
    FirstHit.firstPi (fun i => TierRadius.entry lam r (c i) x y) is ω=
      decide (key lam r is c ω x ≠ key lam r is c ω y) := by
  induction is with
  | nil => simp [FirstHit.firstPi,key]
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    have hx : key lam r is c ω x ≠ some i := fun h => hi (key_mem lam r is c ω x i h)
    have hy : key lam r is c ω y ≠ some i := fun h => hi (key_mem lam r is c ω y i h)
    have he := ih hn
    change (if (ω i).val (c i,x) || (ω i).val (c i,y) then
      (ω i).val (c i,x) != (ω i).val (c i,y) else
      FirstHit.firstPi (fun j => TierRadius.entry lam r (c j) x y) is ω)=_
    simp_rw [key_cons]
    cases hleft : (ω i).val (c i,x) <;> cases hright : (ω i).val (c i,y)
    · simpa only [Bool.false_or,Bool.false_eq_true,ite_false] using he
    · simp [hx]
    · simp [Ne.symm hy]
    · simp

theorem separation (S : Finset I) (is : List I) (c : I → X) (K : ℕ) (hK : 2 ≤ K)
    (r : ℝ) (hr : 0 < r) (x y : X) (hxy : dist x y < r/4) (hn : is.Nodup)
    (hsub : ∀ i ∈ is, i ∈ S) (hage : ∀ i ∈ is, ChronologicalRoster.age S c r i < K^2) :
    let lam := Real.log (1+(K:ℝ)^2)
    (Law.pi (fun _ : I => TierRadius.law (X:=X) lam r)).expect
      (fun ω => if key lam r is c ω x ≠ key lam r is c ω y then (1:ℝ) else 0) ≤
      2*lam*dist x y/r := by
  dsimp only
  let lam := Real.log (1+(K:ℝ)^2)
  let E := fun i => TierRadius.entry lam r (c i) x y
  let P : I → Prop := fun i => dist (c i) x ≤ 2*r ∨ dist (c i) y ≤ 2*r
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0<K)
  have hsq : 0 < (K:ℝ)^2 := sq_pos_of_pos hKr
  have hlam : 0 < lam := Real.log_pos (by linarith)
  have hexp : Real.exp lam-1=(K:ℝ)^2 := by rw [Real.exp_log (by positivity)]; ring
  have hcount := RadiusRoster.candidate_count S is c r (K^2) x y hr.le (by linarith) hn hsub hage
  have hb := FirstHit.first_hit_support is E P (lam*dist x y/r) (1/(K:ℝ)^2)
    (by positivity) (by positivity)
    (by intro i _ _; simpa only [hexp] using TierRadius.local_bound lam r hlam hr (c i) x y)
    (by
      intro i _ hi
      exact TierRadius.hit_zero lam r hlam hr (c i) x y
        (le_of_not_ge (not_or.mp hi).1) (le_of_not_ge (not_or.mp hi).2))
  have he (ω : I → TierRadius.Sample (X:=X) lam r) :
      (if key lam r is c ω x ≠ key lam r is c ω y then (1:ℝ) else 0)=
      (if FirstHit.firstPi E is ω then 1 else 0) := by
    rw [disagreement lam r is hn c ω x y]
    simp
  rw [Law.expect_congr _ _ _ he]
  have hpi : (Law.pi (fun _ : I => TierRadius.law (X:=X) lam r)).expect
      (fun ω => if FirstHit.firstPi E is ω then (1:ℝ) else 0)=
      (FirstHit.experiment (is.map E)).expect (fun ω => if FirstHit.firstSeparates _ ω then 1 else 0) :=
    FirstHit.pi_expect_first E is hn
  rw [hpi]
  have hcr : ((is.filter (fun i => decide (P i))).length:ℝ) ≤ (K:ℝ)^2 := by exact_mod_cast hcount
  have hfrac : ((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hsq).mpr hcr
  have hdec (i : I) : @decide (P i) (Classical.propDecidable (P i))=decide (P i) := by
    exact congrArg (@decide (P i)) (Subsingleton.elim _ _)
  simp only [hdec] at hb
  calc
    _ ≤ (lam*dist x y/r)*(1+((is.filter (fun i => decide (P i))).length:ℝ)*(1/(K:ℝ)^2)) := hb
    _ ≤ (lam*dist x y/r)*2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end UniformKServer.TierKeys

end


end

end OAI
