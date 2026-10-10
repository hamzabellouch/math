import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeMachine

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing

variable {J K : Type} [DecidableEq J] [DecidableEq K]
def map (P : Proc J) (e : J ↪ K) : Proc K :=
  ⟨P.Label,StackLens.program e (StackLens.Lens.identity Store) P.code⟩
lemma exec_map (P : Proc J) (e : J ↪ K) (S T : Stack J) (F : Stack K) (n : ℕ)
    (h : Exec P S T n) :
    Exec (map P e) (StackEmbedding.extend e S F) (StackEmbedding.extend e T F) n := by
  obtain ⟨k,hk,he⟩:=h
  refine ⟨k,hk,?_⟩
  have hh := StackLens.run_cfg e (StackLens.Lens.identity Store) P.code F none k
    ⟨some default,none,S⟩
  rw [he] at hh
  exact hh
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc

variable {R S : Type} [DecidableEq R] [DecidableEq S]
def mapStack (e : R ↪ S) : K R ↪ K S := e.sumMap (Function.Embedding.refl _)
noncomputable def extendEnv (e : R ↪ S) (E : Env R) (F : Env S) : Env S :=
  by
    classical
    exact fun s=>if h : ∃ r,e r=s then E h.choose else F s
omit [DecidableEq R] [DecidableEq S] in
lemma extend_on [DecidableEq R] [DecidableEq S] (e : R ↪ S) (E : Env R) (F : Env S) (r : R) :
    extendEnv e E F (e r)=E r := by
  classical
  have h : ∃ a,e a=e r:=⟨r,rfl⟩
  simp only [extendEnv,dite_eq_left h]
  rw [e.injective h.choose_spec]
omit [DecidableEq R] [DecidableEq S] in
lemma extend_off [DecidableEq R] [DecidableEq S] (e : R ↪ S) (E : Env R) (F : Env S) (s : S)
    (h : ¬∃ r,e r=s) : extendEnv e E F s=F s := by
  classical
  simp only [extendEnv,dite_eq_right h]
lemma encode_extend (e : R ↪ S) (E : Env R) (F : Env S) :
    StackEmbedding.extend (mapStack e) (encodeEnv E) (encodeEnv F)=encodeEnv (extendEnv e E F) := by
  funext k
  cases k with
  | inr k =>
    have hh:=StackEmbedding.extend_on (mapStack e) (encodeEnv E) (encodeEnv F) (.inr k)
    simpa [mapStack,encodeEnv] using hh
  | inl k =>
    by_cases h : ∃ r,e r=k
    · obtain ⟨r,rfl⟩:=h
      rw [show Sum.inl (e r)=mapStack e (.inl r) from rfl,
        StackEmbedding.extend_on]
      change encode (E r)=encode (extendEnv e E F (e r))
      rw [extend_on]
    · have ho : ¬∃ r,mapStack e r=Sum.inl k := by
        rintro ⟨r,hr⟩
        cases r with
        | inl r => exact h ⟨r,Sum.inl.inj hr⟩
        | inr r => cases hr
      rw [StackEmbedding.extend_off _ _ _ _ ho]
      simp only [encodeEnv,extend_off e E F k h]

def mapProc (P : Proc (K R)) (e : R ↪ S) : Proc (K S) := RegisterProc.map P (mapStack e)
lemma mapProc_exec (P : Proc (K R)) (e : R ↪ S) (E E' : Env R) (F : Env S) (n : ℕ)
    (h : Exec P (encodeEnv E) (encodeEnv E') n) :
    Exec (mapProc P e) (encodeEnv (extendEnv e E F)) (encodeEnv (extendEnv e E' F)) n := by
  have hh:=RegisterProc.exec_map P (mapStack e) (encodeEnv E) (encodeEnv E') (encodeEnv F) n h
  simpa only [encode_extend,mapProc] using hh
lemma extend_same (e : R ↪ S) (F : Env S) : extendEnv e (F ∘ e) F=F := by
  funext k
  by_cases h : ∃ r,e r=k
  · obtain ⟨r,rfl⟩:=h
    exact extend_on e (F ∘ e) F r
  · exact extend_off e (F ∘ e) F k h
lemma mapProc_exec_on (P : Proc (K R)) (e : R ↪ S) (E' : Env R) (F : Env S) (n : ℕ)
    (h : Exec P (encodeEnv (F ∘ e)) (encodeEnv E') n) :
    Exec (mapProc P e) (encodeEnv F) (encodeEnv (extendEnv e E' F)) n := by
  simpa only [extend_same] using mapProc_exec P e (F ∘ e) E' F n h
end MatchingFPRAS.TreeMachine

end OAI
