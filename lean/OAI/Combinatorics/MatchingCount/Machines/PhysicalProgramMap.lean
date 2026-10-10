import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgram
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma Realizes.congr {P : Program} {input : Tape Symbol} {f g : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) (he : ∀ w,f.mean w=g.mean w) : P.Realizes input g N := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,fun w=>(hm w).trans (he w),hc⟩
lemma Realizes.mono {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N S : ℕ}
    (h : P.Realizes input f N) (hn : N≤S) : P.Realizes input f S := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,hm,hc.trans hn⟩
lemma seq_realizes_map {A : Type} (P R : Program) (input : Tape Symbol) (f : Experiment A)
    (enc : A→Tape Symbol) (g : A→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input (f.map enc) N) (hR : f.All (fun a=>R.Realizes (enc a) (g a) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  have hR' : (f.map enc).All (fun T=>R.Realizes T (R.earlyTapes S T) S) := by
    rw [Experiment.all_map]
    exact hR.mono (fun a ha=>⟨R.earlyTapes S (enc a),ha.early.1,fun _=>rfl,earlyTapes_cost R S (enc a)⟩)
  apply (seq_realizes P R input (f.map enc) (R.earlyTapes S) N S hP hR').congr
  intro w
  rw [Experiment.mean_bind,Experiment.mean_map,Experiment.mean_bind]
  exact f.mean_congr_all _ _ (hR.mono (fun a ha=>ha.early.2 w))
end MatchingFPRAS.PhysicalPost.Program

end OAI
