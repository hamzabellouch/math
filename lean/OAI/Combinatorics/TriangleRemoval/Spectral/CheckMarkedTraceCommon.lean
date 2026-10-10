import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.CheckMarkedTraceHit

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

theorem checkMarkedTrace_common_hit [DecidableEq A] (ν : K → PMF V)
    (P Q : R → Prop) (key : C → A) (program : C → ExposureTree K V (Bool × Bool × List R))
    (a : A) (cs : List C) (hnd : (cs.map key).Nodup)
    (hP : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → key c = a)
    (hQ : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, Q r) → key c = a)
    (hG : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → (∃ r ∈ z.2.2, Q r) → z.2.1 = true)
    {z : Bool × Bool × List R}
    (hz : z ∈ (fresh ν (checkMarkedTrace
      (cs.map (fun c => (decide (key c = a),program c))))).support)
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
    have hGt := fun c' hc' => hG c' (List.mem_cons_of_mem _ hc')
    have hnone (he : key c = a) :
        (cs.map (fun c => (decide (key c = a),program c))).any Prod.fst = false := by
      apply List.any_eq_false.mpr
      intro d hd
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      simp only [decide_eq_true_eq]
      exact fun h => hcne c' hc' (he.trans h.symm)
    have hsrc (U : R → Prop)
        (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
          (∃ r ∈ x.2.2, U r) → key c' = a)
        {w : Bool × Bool × List R}
        (hw : w ∈ (fresh ν (checkMarkedTrace
          (cs.map (fun c => (decide (key c = a),program c))))).support)
        (hh : ∃ r ∈ w.2.2, U r) : key c ≠ a := by
      obtain ⟨d,hd,x,hx,hh⟩ := checkMarkedTrace_hit_source ν U _ hw hh
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      have he := hu c' hc' x hx hh
      intro hv
      exact hcne c' hc' (hv.trans he.symm)
    rw [List.map_cons,checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      have hgood := hG c List.mem_cons_self x hx hp hq
      have he := hP c List.mem_cons_self x hx hp
      simp only [hgood,hnone he,Bool.or_true,Bool.not_false,Bool.and_self]
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hp' : (∃ r ∈ x.2.2, P r) ∨ (∃ r ∈ y.2.2, P r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hp
      have hq' : (∃ r ∈ x.2.2, Q r) ∨ (∃ r ∈ y.2.2, Q r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hq
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
      · have hgood := hG c List.mem_cons_self x hx hp' hq'
        have he := hP c List.mem_cons_self x hx hp'
        have hygood := checkMarkedTrace_no_demands ν _ (hnone he) hy
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · exact ((hsrc Q hQt hy hq') (hP c List.mem_cons_self x hx hp')).elim
      · exact ((hsrc P hPt hy hp') (hQ c List.mem_cons_self x hx hq')).elim
      · have hca := hsrc P hPt hy hp'
        have hgood := ih hnd hPt hQt hGt hy hp' hq'
        simp only [hca,decide_false,Bool.not_false,Bool.true_or,Bool.true_and,hgood]

end SharpTerminalLeave.ExposureTree

end

end OAI
