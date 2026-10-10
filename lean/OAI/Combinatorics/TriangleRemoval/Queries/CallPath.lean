import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.FreshLogExposeLabeled
import OAI.Combinatorics.TriangleRemoval.Spectral.FreshLogCheckNone
import OAI.Combinatorics.TriangleRemoval.Process.PathRequired

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section LegalPathCover
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def callAtPath (H : τ → Finset ι) : QueryCall ι τ → List (ι × τ) → QueryCall ι τ
  | c, [] => c
  | c, a :: as => callAtPath H ⟨a :: c.address,(H a.2).erase a.1,some a.2⟩ as

omit [Fintype τ] [DecidableEq τ] in
lemma callAtPath_address (H : τ → Finset ι) (c : QueryCall ι τ) (p : List (ι × τ)) :
    (callAtPath H c p).address = p.reverse ++ c.address := by
  induction p generalizing c with
  | nil => simp [callAtPath]
  | cons a as ih => simp only [callAtPath,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

noncomputable def legalPaths (H : τ → Finset ι) : ℕ → Finset ι → Option τ → Finset (List (ι × τ))
  | 0, _, _ => {[]}
  | d+1, focus, parent => insert [] ((gridCandidates H focus parent).biUnion
      (fun a => (legalPaths H d ((H a.2).erase a.1) (some a.2)).image (List.cons a)))

lemma mem_legalPaths (H : τ → Finset ι) (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (p : List (ι × τ)) : p ∈ legalPaths H d focus parent ↔
      LegalQueryPath H focus parent p ∧ p.length ≤ d := by
  induction d generalizing focus parent p with
  | zero => cases p <;> simp [legalPaths,LegalQueryPath]
  | succ d ih =>
    cases p with
    | nil => simp [legalPaths,LegalQueryPath]
    | cons a as =>
      simp only [legalPaths,Finset.mem_insert,List.cons_ne_nil,Finset.mem_biUnion,
        Finset.mem_image,false_or,List.cons.injEq,LegalQueryPath,List.length_cons]
      constructor
      · rintro ⟨b,hb,t,ht,hba,rfl⟩
        subst b
        obtain ⟨hl,hn⟩ := (ih _ _ _).mp ht
        exact ⟨⟨hb,hl⟩,by omega⟩
      · rintro ⟨⟨ha,hl⟩,hn⟩
        exact ⟨a,ha,as,(ih _ _ _).mpr ⟨hl,by omega⟩,rfl,rfl⟩

theorem tracedGridQuery_legal_path (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, ∃ p ∈ legalPaths H d c.focus c.parent, a = callAtPath H c p := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have he : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    subst y
    intro a ha
    have he : a = c := by simpa using ha
    subst a
    exact ⟨[],by simp [legalPaths],rfl⟩
  | succ d ih =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxv := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
    have hh := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => ∃ p ∈ legalPaths H (d+1) c.focus c.parent,
        a = callAtPath H c p) _ (by
          intro A hA z hz
          obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
          have hq' : q ∈ x.1 := (List.mergeSort_perm _ _).mem_iff.mp hq
          have hcand : q.1 ∈ gridCandidates H c.focus c.parent := by
            have hm : q.1 ∈ x.1.map Prod.fst := List.mem_map.mpr ⟨q,hq',rfl⟩
            rw [hxv] at hm
            exact Finset.mem_toList.mp hm
          split_ifs at hz with hqk
          · intro a ha
            obtain ⟨p,hp,he⟩ := ih _ _ hz a ha
            refine ⟨q.1 :: p,?_,he⟩
            apply Finset.mem_insert_of_mem
            apply Finset.mem_biUnion.mpr
            exact ⟨q.1,hcand,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
          · have he : z = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hz
            simp [he]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[],Finset.mem_insert_self _ _,rfl⟩
    · exact hh a ha

end LegalPathCover
end SharpTerminalLeave

end

end OAI
