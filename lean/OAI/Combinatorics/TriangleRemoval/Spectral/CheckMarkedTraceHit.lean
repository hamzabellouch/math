import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.CheckMarkedTrace

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R A C : Type*}

theorem checkMarkedTrace_hit_source (ν : K → PMF V) (P : R → Prop)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support)
    (hh : ∃ r ∈ z.2.2, P r) :
    ∃ a ∈ as, ∃ x ∈ (fresh ν a.2).support, ∃ r ∈ x.2.2, P r := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    simp only [he,List.not_mem_nil,false_and,exists_false] at hh
  | cons a as ih =>
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      exact ⟨a,List.mem_cons_self,x,hx,hh⟩
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      obtain ⟨r,hr,hP⟩ := hh
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨a,List.mem_cons_self,x,hx,r,hr,hP⟩
      · obtain ⟨b,hb,w,hw,r,hr,hP⟩ := ih hy ⟨r,hr,hP⟩
        exact ⟨b,List.mem_cons_of_mem _ hb,w,hw,r,hr,hP⟩

theorem checkMarkedTrace_two_hit [DecidableEq A] (ν : K → PMF V)
    (P Q : R → Prop) (key : C → A) (program : C → ExposureTree K V (Bool × Bool × List R))
    (a b : A) (hab : a ≠ b) (cs : List C) (hnd : (cs.map key).Nodup)
    (hP : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → key c = a ∧ z.2.1 = true)
    (hQ : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, Q r) → key c = b ∧ z.2.1 = true)
    {z : Bool × Bool × List R}
    (hz : z ∈ (fresh ν (checkMarkedTrace
      (cs.map (fun c => (decide (key c = a ∨ key c = b),program c))))).support)
    (hp : ∃ r ∈ z.2.2, P r) (hq : ∃ r ∈ z.2.2, Q r) : z.2.1 = true := by
  induction cs generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [List.map_nil,checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | cons c cs ih =>
    obtain ⟨hc,hnd⟩ := List.nodup_cons.mp hnd
    have hcne : ∀ c' ∈ cs, key c ≠ key c' := by
      intro c' hc' he
      exact hc (List.mem_map.mpr ⟨c',hc',he.symm⟩)
    have hPt := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
    have hQt := fun c' hc' => hQ c' (List.mem_cons_of_mem _ hc')
    have hsrc (U : R → Prop) (v : A)
        (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
          (∃ r ∈ x.2.2, U r) → key c' = v ∧ x.2.1 = true)
        {w : Bool × Bool × List R}
        (hw : w ∈ (fresh ν (checkMarkedTrace
          (cs.map (fun c => (decide (key c = a ∨ key c = b),program c))))).support)
        (hh : ∃ r ∈ w.2.2, U r) : key c ≠ v := by
      obtain ⟨d,hd,x,hx,hh⟩ := checkMarkedTrace_hit_source ν U _ hw hh
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      have he := (hu c' hc' x hx hh).1
      intro hv
      exact hcne c' hc' (hv.trans he.symm)
    rw [List.map_cons,checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have hpx := hP c List.mem_cons_self x hx
    have hqx := hQ c List.mem_cons_self x hx
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      exact (hab ((hpx hp).1.symm.trans (hqx hq).1)).elim
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hp' : (∃ r ∈ x.2.2, P r) ∨ (∃ r ∈ y.2.2, P r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hp
      have hq' : (∃ r ∈ x.2.2, Q r) ∨ (∃ r ∈ y.2.2, Q r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hq
      have hone (v other : A) (hvother : v ≠ other) (hcv : key c = other)
          (heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = v)
          (U : R → Prop)
          (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
            (∃ r ∈ x.2.2, U r) → key c' = v ∧ x.2.1 = true)
          (hh : ∃ r ∈ y.2.2, U r) : y.2.1 = true := by
        apply (checkMarkedTrace_one_hit ν U _ _ _ hy hh).2
        · apply List.pairwise_map.mpr
          have hpw : cs.Pairwise (fun x y => key x ≠ key y) := by
            simpa only [List.Nodup,List.pairwise_map] using hnd
          apply List.pairwise_iff_get.mpr
          intro i j hij
          have hi := (List.pairwise_iff_get.mp hpw) i j hij
          intro hd
          simp only [decide_eq_true_eq] at hd
          simp only [decide_eq_false_iff_not]
          intro he
          exact hi (((heq _ (List.get_mem ..)).mp hd).trans
            ((heq _ (List.get_mem ..)).mp he).symm)
        · intro d hd w hw hh'
          obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
          obtain ⟨he,hg⟩ := hu c' hc' w hw hh'
          exact ⟨decide_eq_true ((heq c' hc').mpr he),hg⟩
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
      · exact (hab ((hpx hp').1.symm.trans (hqx hq').1)).elim
      · obtain ⟨hca,hgood⟩ := hpx hp'
        have heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = b := by
          intro c' hc'
          have hh : key c' ≠ a := fun he => hcne c' hc' (hca.trans he.symm)
          simp only [hh,false_or]
        have hygood := hone b a (Ne.symm hab) hca heq Q hQt hq'
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · obtain ⟨hcb,hgood⟩ := hqx hq'
        have heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = a := by
          intro c' hc'
          have hh : key c' ≠ b := fun he => hcne c' hc' (hcb.trans he.symm)
          simp only [hh,or_false]
        have hygood := hone a b hab hcb heq P hPt hp'
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · have hca := hsrc P a hPt hy hp'
        have hcb := hsrc Q b hQt hy hq'
        have hgood := ih hnd hPt hQt hy hp' hq'
        simp only [hca,hcb,false_or,decide_false,Bool.not_false,
          Bool.true_or,Bool.true_and,hgood]

end SharpTerminalLeave.ExposureTree

end

end OAI
