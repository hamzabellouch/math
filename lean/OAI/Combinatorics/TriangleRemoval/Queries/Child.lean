import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.FreshLogExposeLabeled
import OAI.Combinatorics.TriangleRemoval.Spectral.FreshLogCheckNone3

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section TraceParents
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def QueryCall.Child (H : τ → Finset ι) (c a : QueryCall ι τ) : Prop :=
  ∃ p ∈ gridCandidates H c.focus c.parent,
    a = ⟨p :: c.address, (H p.2).erase p.1, some p.2⟩

noncomputable def QueryCall.RootedTrace (H : τ → Finset ι)
    (c : QueryCall ι τ) (cs : List (QueryCall ι τ)) : Prop :=
  c ∈ cs ∧ ∀ a ∈ cs, a = c ∨ ∃ p ∈ cs, p.Child H a

theorem tracedGridQuery_parents (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N))
    {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    c.RootedTrace H z.1.2 := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have he : y = ((true,[c]),[]) := by
      simpa [ExposureTree.freshLog] using hy
    subst y
    constructor
    · simp
    · intro a ha
      exact Or.inl (List.mem_singleton.mp ha)
  | succ d ih =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxv := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd
      (gridCandidates H c.focus c.parent).toList hx).1
    let P : List (QueryCall ι τ) → Prop := fun cs =>
      ∀ a ∈ cs, ∃ p ∈ c :: cs, p.Child H a
    have h0 : P [] := by intro a ha; simp at ha
    have happend : ∀ a b, P a → P b → P (a ++ b) := by
      intro a b ha hb x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p,hp,hpx⟩ := ha x hx
        refine ⟨p,?_,hpx⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)
      · obtain ⟨p,hp,hpx⟩ := hb x hx
        refine ⟨p,?_,hpx⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)
    have hall : P w.1.2 := by
      apply ExposureTree.freshLog_checkNoneTrace_append ν P h0 happend _ ?_ hw
      intro A hA q hq
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hA
      have hp' : p ∈ x.1 := (List.mergeSort_perm _ _).mem_iff.mp hp
      have hcand : p.1 ∈ gridCandidates H c.focus c.parent := by
        have hmem : p.1 ∈ x.1.map Prod.fst := List.mem_map.mpr ⟨p,hp',rfl⟩
        rw [hxv] at hmem
        exact Finset.mem_toList.mp hmem
      split_ifs at hq with hpk
      · have ht := ih p.2.val
          ⟨p.1 :: c.address, (H p.1.2).erase p.1.1, some p.1.2⟩ hq
        intro a ha
        rcases ht.2 a ha with rfl | ⟨b,hb,hba⟩
        · exact ⟨c,by simp, p.1,hcand,rfl⟩
        · exact ⟨b,List.mem_cons_of_mem _ hb,hba⟩
      · have he : q = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hq
        simpa only [he] using h0
    constructor
    · simp
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr (hall a ha)

theorem QueryCall.Child.address_length {H : τ → Finset ι} {c a : QueryCall ι τ}
    (h : c.Child H a) : a.address.length = c.address.length + 1 := by
  obtain ⟨p,_,rfl⟩ := h
  rfl

end TraceParents
end SharpTerminalLeave

end

end OAI
