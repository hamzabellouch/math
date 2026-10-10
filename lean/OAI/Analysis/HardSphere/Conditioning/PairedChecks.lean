import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalCheck

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I P : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace P]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2}) (real : I→Prop)
attribute [local instance] Classical.propDecidable

def ownedPairCheck (owner : I→I) (get : I→P×P→P) (hget : ∀i,Measurable (get i))
    (i j : I) : LocalCheck (fun _ : I ↦ P×P) where
  support := {owner i,owner j}
  nonempty := ⟨owner i,by simp⟩
  arity := by simpa using Finset.card_insert_le (owner i) ({owner j} : Finset I)
  pass x := i≠j→ real i→ real j→avoid (get i (x (owner i))) (get j (x (owner j)))
  measurable_pass := by
    by_cases hij : i=j
    · simp [hij]
    by_cases hi : real i
    · by_cases hj : real j
      · simp only [ne_eq,hij,not_false_eq_true,hi,hj,true_implies]
        exact hm.preimage (f:=fun x : I→P×P ↦ (get i (x (owner i)),get j (x (owner j)))) (by fun_prop)
      · simp [hj]
    · simp [hi]
  depends x y h := by rw [h (owner i) (by simp),h (owner j) (by simp)]

def primaryPairCheck (i j : I) : LocalCheck (fun _ : I ↦ P) where
  support := {i,j}
  nonempty := ⟨i,by simp⟩
  arity := by simpa using Finset.card_insert_le i ({j} : Finset I)
  pass x := i≠j→ real i→ real j→avoid (x i) (x j)
  measurable_pass := by
    by_cases hij : i=j
    · simp [hij]
    by_cases hi : real i
    · by_cases hj : real j
      · simp only [ne_eq,hij,not_false_eq_true,hi,hj,true_implies]
        exact hm.preimage (f:=fun x : I→P ↦ (x i,x j)) (by fun_prop)
      · simp [hj]
    · simp [hi]
  depends x y h := by rw [h i (by simp),h j (by simp)]

def pairedRouteChecks (S : Finset I) (σ : Equiv.Perm I) : Bool×I×I → LocalCheck (fun _ : I ↦ P×P)
  | (false,i,j) => ownedPairCheck avoid hm real id (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst) i j
  | (true,i,j) => ownedPairCheck avoid hm real σ (fun k p ↦ if k∈S then p.2 else p.1)
      (fun k ↦ by split_ifs <;> fun_prop) i j

omit [Fintype I] in
lemma paired_check_primary (S : Finset I) (σ : Equiv.Perm I) (U : Finset I) (x z : I→P) :
    checkWeight (pairedRouteChecks avoid hm real S σ) U (fun i ↦ (x i,z i)) ≤
      checkWeight (fun p : I×I ↦ primaryPairCheck avoid hm real p.1 p.2) U x := by
  by_cases h : x∈retainedEvent (fun p : I×I ↦ primaryPairCheck avoid hm real p.1 p.2) U
  · have he : checkWeight (fun p : I×I ↦ primaryPairCheck avoid hm real p.1 p.2) U x = 1 := by simp [checkWeight,h]
    rw [he]
    exact checkWeight_le_one _ _ _
  · have hn : (fun i ↦ (x i,z i))∉retainedEvent (pairedRouteChecks avoid hm real S σ) U := by
      intro hp
      apply h
      intro c hc
      exact hp (false,c.1,c.2) hc
    simp only [checkWeight,Set.indicator_of_notMem hn,Set.indicator_of_notMem h,le_refl]

omit [Fintype I] in
lemma perm_mem_of_fix_outside (S : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉S→σ i=i) (i : I) : σ i∈S ↔ i∈S := by
  constructor
  · intro h
    by_contra hi
    rw [hσ i hi] at h
    contradiction
  · intro hi
    by_contra hn
    have he : σ (σ i)=σ i := hσ (σ i) hn
    have he' : σ i=i := σ.injective he
    exact hn (he'.symm ▸ hi)

omit [Fintype I] in
lemma paired_outside_checks (S o : Finset I) (hso : Disjoint S o) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉S→σ i=i) (x z : I→P)
    (hx : x∈retainedEvent (fun p : I×I ↦ primaryPairCheck avoid hm real p.1 p.2) o) :
    (fun i ↦ (x i,z i))∈retainedEvent (pairedRouteChecks avoid hm real S σ) o := by
  intro c hc
  obtain ⟨b,i,j⟩ := c
  cases b
  · exact hx (i,j) hc
  · have hi : σ i∈o := hc (by simp [pairedRouteChecks,ownedPairCheck])
    have hj : σ j∈o := hc (by simp [pairedRouteChecks,ownedPairCheck])
    have hin : i∉S := fun his ↦ Finset.disjoint_left.mp hso ((perm_mem_of_fix_outside S σ hσ i).mpr his) hi
    have hjn : j∉S := fun hjs ↦ Finset.disjoint_left.mp hso ((perm_mem_of_fix_outside S σ hσ j).mpr hjs) hj
    have hio : i∈o := by simpa only [hσ i hin] using hi
    have hjo : j∈o := by simpa only [hσ j hjn] using hj
    have hre := hx (i,j) (by simpa only [primaryPairCheck,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hio hjo)
    simpa only [pairedRouteChecks,ownedPairCheck,primaryPairCheck,hin,hjn,ite_false,hσ i hin,hσ j hjn] using hre

lemma paired_full_event (S : Finset I) (σ : Equiv.Perm I) (x z : I→P) :
    (fun i ↦ (x i,z i))∈retainedEvent (pairedRouteChecks avoid hm real S σ) Finset.univ ↔
    (∀i j,i≠j→ real i→ real j→avoid (x i) (x j)) ∧
    (∀i j,i≠j→ real i→ real j→avoid (if i∈S then z (σ i) else x (σ i))
      (if j∈S then z (σ j) else x (σ j))) := by
  constructor
  · intro h
    exact ⟨fun i j ↦ h (false,i,j) (Finset.subset_univ _),fun i j ↦ h (true,i,j) (Finset.subset_univ _)⟩
  · rintro ⟨h₁,h₂⟩ ⟨b,i,j⟩ _
    cases b
    · exact h₁ i j
    · exact h₂ i j

end HardSphere.Comparison

end
end

end

end OAI
