import OAI.Computability.FiniteCompiler.SelfReference
import OAI.GroupTheory.BooneHigman.Contracted

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
 theorem grade_le_twice_length (w : List (Letter S Γ Q)) : grade w≤2*w.length := by
  induction w with
  | nil => simp [grade,Path.grade]
  | cons a w ih =>
    have ha : Path.letterGrade (gradeCell (S:=S) (Γ:=Γ)) a≤2 := by
      cases a <;> simp [Path.letterGrade,gradeCell]
      all_goals rename_i c; cases c.1 <;> simp [Cleanup.grade]
    simpa [grade,Path.grade,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_comm] using Nat.add_le_add ha ih

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem normal_zero_context
    (hdecode : ∀ g a, A.output g=some a → g=A.input a)
    {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m) (hr : Realizes A M f)
    (a b u : List (Letter S Γ Q)) (hm : grade (a ++ u ++ b) ≤ m)
    (hz : normal A M (fun w => partValue (f w)) u=[.zero]) :
    normal A M (fun w => partValue (f w)) (a++u++b)=[.zero] := by
  have he : normal A M (fun w => partValue (f w)) u=normal A M (fun w => partValue (f w)) [.zero] := by
    simpa using hz
  have hb : grade (a ++ [.zero] ++ b) ≤ m := by
    simp only [grade_append] at *
    have h0 : grade ([.zero] : List (Letter S Γ Q))=0 := rfl
    rw [h0]
    omega
  rw [normal_context A M hdecode h.totalize (Realizes.computesAt A M hr h) he a b hm hb]
  simpa using normal_contains_omega A M (fun w => partValue (f w)) a b
end Compiler.Word

namespace Bootstrap
namespace Projection
variable {A B C D : Type*}
@[simp] theorem left_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    left (w.map (Sum.map f g))=(left w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact congrArg (f a :: ·) ih
    | inr b => exact ih
@[simp] theorem right_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    right (w.map (Sum.map f g))=(right w).map g := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact ih
    | inr b => exact congrArg (g b :: ·) ih
end Projection

namespace ZeroProduct
variable {A C D : Type*} [DecidableEq C]
def test (z : C) (f : List A → C) (g : List A → D) (w : List A) : Option (C×D) :=
  if f w=z then none else some (f w,g w)

 theorem contextual (z : C) (f : List A → C) (g : List A → D) (n : ℕ)
    (hf : ∀ a b u v,(a++u++b).length≤n → (a++v++b).length≤n → f u=f v → f (a++u++b)=f (a++v++b))
    (hz : ∀ a b u,(a++u++b).length≤n → f u=z → f (a++u++b)=z)
    (hg : ∀ a b u v,g u=g v → g (a++u++b)=g (a++v++b)) :
    Static.Contextual (test z f g) n := by
  intro a b u v hu hv he
  by_cases huf : f u=z
  · have hvf : f v=z := by
      by_contra hc
      simp [test,huf,hc] at he
    simp only [test,hz a b u hu huf,hz a b v hv hvf,ite_true]
  · have hvf : f v≠z := by
      intro hc
      simp [test,huf,hc] at he
    have hei : f u=f v ∧ g u=g v := by simpa [test,huf,hvf] using he
    simp only [test,hf a b u v hu hv hei.1,hg a b u v hei.2]

 theorem ideal (z : C) (f : List A → C) (g : List A → D) (n : ℕ)
    (hz : ∀ a b u,(a++u++b).length≤n → f u=z → f (a++u++b)=z) :
    Static.ZeroIdeal (test z f g) n := by
  intro a b u hu he
  have hf : f u=z := by simpa [test] using he
  simp only [test,hz a b u hu hf,ite_true]
end ZeroProduct
end Bootstrap

namespace PartialAffine
 theorem value_context {u v : List Letter} (h : value u=value v) (a b : List Letter) :
    value (a++u++b)=value (a++v++b) := by
  simp only [value,List.map_append,List.prod_append] at *
  rw [h]
 theorem testedClass_context {u v : List Letter} (h : testedClass u=testedClass v) (a b : List Letter) :
    testedClass (a++u++b)=testedClass (a++v++b) :=
  (testedClass_eq_iff _ _).mpr (value_context ((testedClass_eq_iff _ _).mp h) a b)
end PartialAffine
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance
local instance (n : ℕ) : Fintype (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : LinearOrder (Compiler.Control.Sector Sigma (Bool×Γ) (ParameterMachine.State Q n)) :=
  finiteOrder (T:=Sigma) (Γ:=Γ) (Q:=Q) n

abbrev terminalAlphabet := UniversalMachine.restrict (ParameterMachine.alphabet A)
abbrev terminalMachine (n : ℕ) := ParameterMachine.machine A M (.inr ()) n

noncomputable def finiteValue (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) : List (Tested.X Sigma Γ Q) :=
  (Word.normal (terminalAlphabet A) (terminalMachine A M n) (fun w => partValue (raw n w)) (Projection.left w)).map
    (Word.letterMap (encode n))
noncomputable def finiteClass (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :=
  ZeroProduct.test [.zero] (finiteValue A M n) (fun w => PartialAffine.testedClass (Projection.right w)) w

omit [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q] in
 theorem projection_grade (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    Word.grade (Projection.left w)≤2*w.length :=
  (Word.grade_le_twice_length _).trans (Nat.mul_le_mul_left 2 (Projection.left_length w))

omit [Primcodable Γ] in
 theorem finiteTest_eq (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hw : w.length≤j) :
    finiteTest A M n w=Part.some (finiteClass A M n w) := by
  have hg := (projection_grade n w).trans (Nat.mul_le_mul_left 2 hw)
  simp only [finiteTest,testT,Tested.family,includeY,Projection.left_map,Projection.right_map,List.map_id]
  rw [codedNormal_map,Word.partialNormal_eq_some _ _ h _ hg]
  simp only [Part.map_some,finiteClass,ZeroProduct.test,finiteValue,Tested.combine,
    terminalAlphabet,terminalMachine]
  rfl

omit [Primcodable Γ] in
 theorem finiteValue_zero (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    finiteValue A M n w=[.zero] ↔
      Word.normal (terminalAlphabet A) (terminalMachine A M n) (fun w => partValue (raw n w)) (Projection.left w)=[.zero] := by
  change List.map (Word.letterMap (encode n)) _=List.map (Word.letterMap (encode n)) [.zero] ↔ _
  exact (List.map_injective_iff.mpr (Word.letterMap_injective _ (encode_injective n))).eq_iff

omit [Primcodable Γ] in
 theorem finiteValue_context (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a)
    (a b u v : List (FiniteY (Γ:=Γ) (Q:=Q) n))
    (hu : (a++u++b).length≤j) (hv : (a++v++b).length≤j)
    (he : finiteValue A M n u=finiteValue A M n v) :
    finiteValue A M n (a++u++b)=finiteValue A M n (a++v++b) := by
  have hh := List.map_injective_iff.mpr (Word.letterMap_injective (encode n) (encode_injective n)) he
  have hgu := (projection_grade n (a++u++b)).trans (Nat.mul_le_mul_left 2 hu)
  have hgv := (projection_grade n (a++v++b)).trans (Nat.mul_le_mul_left 2 hv)
  simp only [Projection.left_append] at hgu hgv
  simp only [finiteValue,Projection.left_append]
  congr 1
  exact Word.normal_context (terminalAlphabet A) (terminalMachine A M n) hd h.totalize
    (Word.Realizes.computesAt _ _ hr h) hh _ _ hgu hgv

omit [Primcodable Γ] in
 theorem finiteValue_ideal (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a)
    (a b u : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hu : (a++u++b).length≤j)
    (he : finiteValue A M n u=[.zero]) : finiteValue A M n (a++u++b)=[.zero] := by
  apply (finiteValue_zero A M n _).mpr
  have hh := (finiteValue_zero A M n u).mp he
  have hgu := (projection_grade n (a++u++b)).trans (Nat.mul_le_mul_left 2 hu)
  simp only [Projection.left_append] at hgu ⊢
  exact Word.normal_zero_context (terminalAlphabet A) (terminalMachine A M n) hd h hr _ _ _ hgu hh

omit [Primcodable Γ] in
 theorem finiteClass_context (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    Static.Contextual (finiteClass A M n) j := by
  apply ZeroProduct.contextual
  · exact finiteValue_context A M n j h hr hd
  · exact finiteValue_ideal A M n j h hr hd
  · intro a b u v he
    simpa only [Projection.right_append] using PartialAffine.testedClass_context he (Projection.right a) (Projection.right b)

omit [Primcodable Γ] in
 theorem finiteClass_ideal (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    Static.ZeroIdeal (finiteClass A M n) j :=
  ZeroProduct.ideal _ _ _ _ (finiteValue_ideal A M n j h hr hd)

omit [Primcodable Γ] in
 theorem finiteClass_nil (n : ℕ) : finiteClass A M n []≠none := by
  simp [finiteClass,ZeroProduct.test,finiteValue,Projection.left]

omit [Primcodable Γ] in
 theorem search_value_eq (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hw : w.length≤j) :
    Search.value (finiteTest A M n) w=finiteClass A M n w := by
  have hh := finiteTest_eq A M n j h w hw
  have hd : (finiteTest A M n w).Dom := by rw [hh]; trivial
  have hm := Search.value_mem hd
  simpa only [hh,Part.mem_some_iff] using hm

omit [Primcodable Γ] in
 theorem tests_bounded (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j → (finiteTest A M n w).Dom) ∧
      Search.value (finiteTest A M n) []≠none ∧
      Static.Contextual (Search.value (finiteTest A M n)) j ∧
      Static.ZeroIdeal (Search.value (finiteTest A M n)) j := by
  refine ⟨fun w hw => ?_,?_,?_,?_⟩
  · rw [finiteTest_eq A M n j h w hw]; trivial
  · rw [search_value_eq A M n j h [] (by simp)]
    exact finiteClass_nil A M n
  · intro a b u v hu hv he
    have hul : u.length≤j := by simp only [List.length_append] at hu; omega
    have hvl : v.length≤j := by simp only [List.length_append] at hv; omega
    rw [search_value_eq A M n j h u hul,search_value_eq A M n j h v hvl] at he
    rw [search_value_eq A M n j h _ hu,search_value_eq A M n j h _ hv]
    exact finiteClass_context A M n j h hr hd a b u v hu hv he
  · intro a b u hu he
    have hul : u.length≤j := by simp only [List.length_append] at hu; omega
    rw [search_value_eq A M n j h u hul] at he
    rw [search_value_eq A M n j h _ hu]
    exact finiteClass_ideal A M n j h hr hd a b u hu he

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]
@[simp] theorem partialNormal_nil (f : List S → Part (List S)) : partialNormal A M f []=Part.some [] := by
  simp [partialNormal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.partialSource,RawRuns.plan,RawRuns.execute]
end Compiler.Word

namespace Bootstrap
namespace Static
variable {A Q : Type*} (q : List A → Option Q)
 theorem contextual_zero : Contextual q 0 := by
  intro a b u v hu hv he
  have ha : a=[] := by simpa using (show a.length=0 from by simp only [List.length_append] at hu; omega)
  have hb : b=[] := by simpa using (show b.length=0 from by simp only [List.length_append] at hu; omega)
  simpa [ha,hb] using he
 theorem zeroIdeal_zero : ZeroIdeal q 0 := by
  intro a b u hu he
  have ha : a=[] := by simpa using (show a.length=0 from by simp only [List.length_append] at hu; omega)
  have hb : b=[] := by simpa using (show b.length=0 from by simp only [List.length_append] at hu; omega)
  simpa [ha,hb] using he
end Static

namespace Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)
local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance
local instance (n : ℕ) : LinearOrder (Compiler.Control.Sector Sigma (Bool×Γ) (ParameterMachine.State Q n)) :=
  finiteOrder (T:=Sigma) (Γ:=Γ) (Q:=Q) n

omit [Primcodable Γ] in
 theorem finiteTest_nil (n : ℕ) : finiteTest A M n []=Part.some (finiteClass A M n []) := by
  simp only [finiteTest,testT,Tested.family,includeY,List.map_nil,Projection.left]
  have hh := codedNormal_map A M (.inr ()) (terminalAlphabet A) n (fun p => raw p.1 p.2) ([] : List (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)))
  simp only [List.map_nil,Word.partialNormal_nil,Part.map_some] at hh
  simp only [List.filterMap_nil]
  rw [hh]
  simp [finiteClass,ZeroProduct.test,finiteValue,Projection.left,Projection.right,Tested.combine]

omit [Primcodable Γ] in
 theorem finite_search_nil (n : ℕ) : Search.value (finiteTest A M n) []=finiteClass A M n [] := by
  have hd : (finiteTest A M n []).Dom := by rw [finiteTest_nil]; trivial
  simpa only [finiteTest_nil,Part.mem_some_iff] using Search.value_mem hd

omit [Primcodable Γ] in
 theorem tests_zero (n : ℕ) :
    (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤0 → (finiteTest A M n w).Dom) ∧
      Search.value (finiteTest A M n) []≠none ∧
      Static.Contextual (Search.value (finiteTest A M n)) 0 ∧
      Static.ZeroIdeal (Search.value (finiteTest A M n)) 0 := by
  refine ⟨?_,?_,Static.contextual_zero _,Static.zeroIdeal_zero _⟩
  · intro w hw
    have hw : w=[] := by simpa using hw
    subst w
    rw [finiteTest_nil]; trivial
  · rw [finite_search_nil]
    exact finiteClass_nil A M n

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
 theorem group_search_value (n : ℕ) (w : List (Z k)) :
    Search.value (testG s n) w=some (WordProblem.testedClass s w) := by
  have hm := Search.value_mem (f:=testG s n) (w:=w) (show (testG s n w).Dom from True.intro)
  simpa only [testG,Part.mem_some_iff] using hm

 theorem group_tests (n j : ℕ) :
    Search.value (testG s n) []≠none ∧
      Static.Contextual (Search.value (testG s n)) j ∧
      Static.ZeroIdeal (Search.value (testG s n)) j := by
  refine ⟨by simp [group_search_value],?_,?_⟩
  · intro a b u v hu hv he
    simp only [group_search_value,Option.some.injEq] at he ⊢
    apply (WordProblem.testedClass_eq_iff s _ _).mpr
    have hh := (WordProblem.testedClass_eq_iff s _ _).mp he
    simp only [WordProblem.evalWord_append]
    rw [hh]
  · intro a b u hu he
    simp only [group_search_value,Option.some_ne_none] at he

end Source
end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem quota_smaller (k n j : ℕ) (hj : 0<j) :
    2*(j/(width (Γ:=Γ) (Q:=Q) k n+1))<j := by
  have hd : 3≤width (Γ:=Γ) (Q:=Q) k n+1 := by unfold width; omega
  have hp := Nat.mul_le_mul_right (j/(width (Γ:=Γ) (Q:=Q) k n+1)) hd
  have hq := Nat.div_mul_le_self j (width (Γ:=Γ) (Q:=Q) k n+1)
  rw [Nat.mul_comm (width (Γ:=Γ) (Q:=Q) k n+1)] at hp
  omega

omit [Primcodable Γ] in
 theorem all_budgets (n : ℕ) (fixed : raw n=tableNormal (tables s A M n))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s A M n) j ∧ PartialBudget (raw n) j := by
  apply bootstrap_length_induction (r:=fun a b : Sigma => a<b)
    (InvImage.wf Fin.val Nat.lt_wfRel.wf) (tables s A M n) (raw n) fixed
  · intro j m hjm rk hrk rn hrn
    exact stable s A M n hjm hrk hrn
  · intro j ih
    have ht :
        (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j/(width (Γ:=Γ) (Q:=Q) k n+1) → (finiteTest A M n w).Dom) ∧
          Search.value (finiteTest A M n) []≠none ∧
          Static.Contextual (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)) ∧
          Static.ZeroIdeal (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)) := by
      rcases Nat.eq_zero_or_pos j with rfl|hj
      · simpa using tests_zero A M n
      · exact tests_bounded A M n _ (ih _ (quota_smaller k n j hj)) hr hd
    have hg := group_tests s n (j/(width (Γ:=Γ) (Q:=Q) k n+1))
    exact good_of_tests s A M n j ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hg.1 hg.2.1 hg.2.2

 theorem exists_total_fixed_point
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))
    (hr : ∀ n, Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    ∃ n, raw n=tableNormal (tables s A M n) ∧
      ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s A M n) j ∧ PartialBudget (raw n) j := by
  obtain ⟨n,hn⟩ := exists_fixed_point s A M h
  exact ⟨n,hn,all_budgets s A M n hn (hr n) hd⟩

end

section
open Compiler Compiler.Simulator MachineRealization

/-- The actual finite machine used uniformly in the source bootstrap.  Every
    field is constructed below from partial recursiveness of the universal
    word evaluator; none is an assumption on an input group. -/
structure Family where
  Γ : Type
  Q : Type
  [finiteΓ : Fintype Γ]
  [finiteQ : Fintype Q]
  [decΓ : DecidableEq Γ]
  [decQ : DecidableEq Q]
  [codeΓ : Primcodable Γ]
  [codeQ : Primcodable Q]
  A : Alphabet (Sigma ⊕ Unit) Γ
  M : Machine Q Γ
  decode : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a
  realizes : ∀ n,Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n)

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

 theorem exists_family : Nonempty Family := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,dΓ,A,M,hd,hr⟩ := UniversalMachine.exists_parameter_machine partrec_raw
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  let : DecidableEq Γ := dΓ
  let : Primcodable Γ := Effect.finitePrimcodable Γ
  let : Primcodable Q := Effect.finitePrimcodable Q
  exact ⟨⟨Γ,Q,A,M,UniversalMachine.restrict_decode (ParameterMachine.alphabet A) (ParameterMachine.output_decode A hd),hr⟩⟩

noncomputable def family : Family := exists_family.some

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
 theorem source_bootstrap
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1)) :
    ∃ n, raw n=tableNormal (tables s family.A family.M n) ∧
      ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s family.A family.M n) j ∧ PartialBudget (raw n) j :=
  exists_total_fixed_point s family.A family.M h family.realizes family.decode

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)
local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance
local instance (n : ℕ) : Fintype (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance

def base (n j : ℕ) : List (List Sigma × List Sigma) :=
  Base.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero j

omit [Primcodable Γ] in
 theorem tables_members (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    RulesEq rs (Selectors.process (a:=markers) (base s A M n j) (Selectors.stages markers.zero) j j) := by
  rw [tables_eq_finite] at hrs
  exact Uniform.tables_members_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (finiteLetters n) (zLetters k) (mem_finiteLetters n)
    (by intro x; simp [zLetters,Static.letters]) (finiteTest A M n) (testG s n) hrs

omit [Primcodable Γ] in
 theorem tables_absorb (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    Absorbs rs markers.zero := by
  have hh := Selectors.process_contains (a:=markers) (base s A M n j) (Selectors.stages markers.zero) j j
  have hz := Base.absorbs (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero j
  intro b
  exact ⟨(tables_members s A M n j hrs _).mpr (hh _ (hz b).1),
    (tables_members s A M n j hrs _).mpr (hh _ (hz b).2)⟩

omit [Primcodable Γ] in
 theorem tables_short (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,1<p.1.length := by
  intro p hp
  have hp := (tables_members s A M n j hrs p).mp hp
  rcases Selectors.process_members hp with hp | ⟨i,hi,hp⟩
  · rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp|hp|hp
    · obtain ⟨b,(he|he),_⟩ := (Base.mem_absorption markers.zero).mp hp <;> rw [he] <;> simp
    · apply Static.table_short _ (wf_relT n) _ _ _ hp
      change 1<width (Γ:=Γ) (Q:=Q) k n+1
      unfold width; omega
    · apply Static.table_short _ (wf_relG k) _ _ _ hp
      change 1<width (Γ:=Γ) (Q:=Q) k n+1
      unfold width; omega
  · obtain ⟨w,_,he,_⟩ := (Selectors.mem_rules markers).mp hp
    rw [he]
    simp only [Selectors.Markers.wrap,Envelopes.length_frame]
    omega

omit [Primcodable Γ] in
 theorem tables_isolateT (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
      (Search.value (finiteTest A M n)) markers.zero j ∨ ∃ b∈p.1,b∉(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relT n) (Search.value (finiteTest A M n))
    (fun p hp => Base.isolate_left (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero
      (codeT_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) (codes_disjoint (Γ:=Γ) (Q:=Q) k n) hp)
    (codeT_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) _ _ _
  exact (tables_members s A M n j hrs p).mp hp

omit [Primcodable Γ] in
 theorem tables_staticT (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈tables s A M n ((width (Γ:=Γ) (Q:=Q) k n+1)*j)) :
    ∀ p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
      (Search.value (finiteTest A M n)) markers.zero j,p∈rs := by
  intro p hp
  apply (tables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inl
  change p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
    (Search.value (finiteTest A M n)) markers.zero (((width (Γ:=Γ) (Q:=Q) k n+1)*j)/(width (Γ:=Γ) (Q:=Q) k n+1))
  simpa using hp

omit [Primcodable Γ] in
 theorem tables_isolateG (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j ∨ ∃ b∈p.1,b∉(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relG k) (Search.value (testG s n)) ?_
    (codeG_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) _ _ _ ((tables_members s A M n j hrs p).mp hp)
  intro p hp
  rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (Base.mem_absorption markers.zero).mp hp
    exact Or.inr ⟨markers.zero,by rcases hb with h|h <;> simp [h],codeG_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)⟩
  · obtain ⟨hn,hs⟩ := Static.table_support _ (wf_relT n) _ _ hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,fun hc => Set.disjoint_left.mp (codes_disjoint (Γ:=Γ) (Q:=Q) k n) (hs b hb) hc⟩
  · exact Or.inl (Static.table_mono _ (wf_relG k) _ _ (Nat.div_le_self j _) hp)

omit [Primcodable Γ] in
 theorem tables_staticG (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈tables s A M n ((width (Γ:=Γ) (Q:=Q) k n+1)*j)) :
    ∀ p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j,p∈rs := by
  intro p hp
  apply (tables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inr
  change p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
    (Search.value (testG s n)) markers.zero (((width (Γ:=Γ) (Q:=Q) k n+1)*j)/(width (Γ:=Γ) (Q:=Q) k n+1))
  simpa using hp

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Selectors
variable {S : Type*} [DecidableEq S] [Primcodable S]

/-- Every nonzero irreducible ordered tuple receives its literal selector.
    The finite processing stage is chosen beyond the complete selector word. -/
theorem tuple_selected_rulesEq (a : Markers S) (T : ℕ → Part (List (List S × List S)))
    (bases : ℕ → List (List S × List S))
    (hT : ∀ n,∃ rs∈T n,RulesEq rs (process (a:=a) (bases n) (stages a.zero) n n))
    {ws : List (List S)} (hne : ws≠[]) (hd : ws.Nodup) (hz : ∀ w∈ws,a.zero∉w)
    (hi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w) :
    ∃ N,∀ w∈ws,Quotient.present T (a.wrap N w)=
      Quotient.present T (if ws.head?=some w then [] else [a.zero]) := by
  let j := Encodable.encode ws
  let N := sizes a.zero j
  let n := 3*N+2
  have he : (stages a.zero j).bodies=ws := tuples_complete a.zero hne hd hz
  have hsize : (stages a.zero j).size=N := rfl
  have hjN : j<N := index_lt_size a.zero j
  have hNn : N≤n := by omega
  have hjn : j<n := lt_of_lt_of_le hjN hNn
  have hlen (w : List S) (hw : w∈ws) : w.length<N := by
    apply body_lt_size a.zero j
    change w∈(stages a.zero j).bodies
    rw [he]
    exact hw
  obtain ⟨rs,hrs,heq⟩ := hT n
  have hall : allowed (process (a:=a) (bases n) (stages a.zero) n j) (stages a.zero j)=true := by
    apply allowed_iff.mpr
    intro w hw
    have hw' : w∈ws := he ▸ hw
    have nh := hi w hw' n rs hrs (le_trans (Nat.le_of_lt (hlen w hw')) hNn)
    intro v hv
    apply nh v
    rw [step_rulesEq heq]
    exact step_mono (process_mono (bases n) (stages a.zero) n (Nat.le_of_lt hjn)) hv
  refine ⟨N,?_⟩
  intro w hw
  have hp : (a.wrap N w,if ws.head?=some w then [] else [a.zero])∈rules a
      (stages a.zero j).size (stages a.zero j).bodies := by
    rw [he,hsize]
    exact (mem_rules a).mpr ⟨w,hw,rfl,rfl⟩
  have hmem := selected_mem hjn (hsize ▸ hNn) hall _ hp
  apply PresentedMonoid.mk_eq_mk_of_rel
  refine ⟨n,rs,hrs,(heq _).mpr hmem,?_⟩
  change (a.wrap N w).length≤n
  simp only [Markers.wrap,Envelopes.length_frame]
  have := hlen w hw
  omega

end Selectors
namespace Quotient
variable {S : Type*} [DecidableEq S] [Primcodable S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

/-- Source selectors for the stabilized quotient, with the distinguished element
    first in the tuple. Not an extra algebraic assumption on that quotient. -/
theorem selectors_rulesEq (a : Selectors.Markers S) (bases : ℕ → List (List S × List S))
    (hT : ∀ n,∃ rs∈T n,RulesEq rs (Selectors.process (a:=a) (bases n) (Selectors.stages a.zero) n n))
    (hz : ∀ n rs,rs∈T n → Absorbs rs a.zero)
    (X : Finset (Mon T)) (hX : present T [a.zero]∉X) (x : Mon T) (hx : x∈X) :
    ∃ L R : Mon T,L*x*R=1 ∧ ∀ y∈X,y≠x → L*y*R=present T [a.zero] := by
  classical
  let xs := x::(X.erase x).toList
  have xsne : xs≠[] := List.cons_ne_nil _ _
  have xsd : xs.Nodup := List.nodup_cons.mpr ⟨by simp,Finset.nodup_toList _⟩
  have xsmem (y : Mon T) : y∈xs ↔ y∈X := by
    simp only [xs,List.mem_cons,Finset.mem_toList,Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_,hh⟩)
      · exact hx
      · exact hh
    · intro hh
      by_cases he : y=x
      · exact Or.inl he
      · exact Or.inr ⟨he,hh⟩
  let rep := representative T
  have hrep : Function.Injective rep := representative_injective T wf good stable
  let ws := xs.map rep
  have hwsne : ws≠[] := by simp [ws,xs]
  have hwsd : ws.Nodup := xsd.map hrep
  have hwsz : ∀ w∈ws,a.zero∉w := by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
    exact representative_avoids_zero T wf good stable a.zero y
      (fun he => hX (he ▸ (xsmem y).mp hy)) hz
  have hwsi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w := by
    intro w hw n rs hrs hlen
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hw
    exact representative_irreducible T wf good stable y hrs hlen
  obtain ⟨N,hN⟩ := Selectors.tuple_selected_rulesEq a T bases hT hwsne hwsd hwsz hwsi
  let L := present T (a.d::List.replicate N a.l)
  let R := present T (List.replicate N a.r++[a.h])
  have heq (y : Mon T) : present T (a.wrap N (rep y))=L*y*R := by
    change present T (a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h]))=_
    have he : a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h])=
      (a.d::List.replicate N a.l)++rep y++(List.replicate N a.r++[a.h]) := by simp [List.append_assoc]
    rw [he,present_append,present_append,present_representative T wf good stable]
  refine ⟨L,R,?_,?_⟩
  · have hw : rep x∈ws := List.mem_map.mpr ⟨x,(xsmem x).mpr hx,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    simpa only [ws,xs,List.map_cons,List.head?_cons,ite_true,present_nil] using hs
  · intro y hy hyx
    have hw : rep y∈ws := List.mem_map.mpr ⟨y,(xsmem y).mpr hy,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    have hne : ws.head?≠some (rep y) := by
      simp only [ws,xs,List.map_cons,List.head?_cons]
      exact fun equality => hyx (hrep (Option.some.inj equality)).symm
    simpa only [ite_eq_right hne] using hs

end Quotient
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

noncomputable def index : ℕ := (source_bootstrap s h).choose
abbrev processor := tables s family.A family.M (index s h)

theorem index_fixed : raw (index s h)=tableNormal (processor s h) := (source_bootstrap s h).choose_spec.1

theorem index_good (j : ℕ) : GoodTable (r:=fun a b : Sigma => a<b) (processor s h) j :=
  ((source_bootstrap s h).choose_spec.2 j).1

theorem index_budget (j : ℕ) : PartialBudget (raw (index s h)) j :=
  ((source_bootstrap s h).choose_spec.2 j).2

theorem index_stable : ∀ j m : ℕ, j ≤ m → ∀ rs∈processor s h j,∀ rt∈processor s h m,Selectors.BoundedEq rs rt j := by
  intro j m hjm rs hrs rt hrt
  exact stable s family.A family.M (index s h) hjm hrs hrt

theorem wf_sigma : WellFounded (fun a b : Sigma => a<b) := InvImage.wf Fin.val Nat.lt_wfRel.wf

abbrev H := Quotient.Mon (processor s h)

noncomputable instance hMonoidWithZero : MonoidWithZero (H s h) :=
  Quotient.monoidWithZero (processor s h) markers.zero (index_good s h 2).choose_spec.1
    (tables_absorb s family.A family.M (index s h) 2 (index_good s h 2).choose_spec.1)

theorem zero_H : (0 : H s h)=Quotient.present (processor s h) [markers.zero] := rfl

theorem one_ne_zero_H : (1 : H s h)≠0 :=
  Quotient.present_nil_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)

instance hNontrivial : Nontrivial (H s h) := ⟨⟨1,0,one_ne_zero_H s h⟩⟩

theorem computable_wordProblem_H :
    ComputablePred (fun p : List Sigma × List Sigma =>
      Quotient.present (processor s h) p.1=Quotient.present (processor s h) p.2) :=
  Quotient.computable_wordProblem (processor s h) wf_sigma (index_good s h) (index_stable s h)
    ((partrec_tables s family.A family.M h).comp (Computable.const (index s h)) Computable.id)

theorem selectors_H (X : Finset (H s h)) (hX : (0:H s h)∉X) (x : H s h) (hx : x∈X) :
    ∃ L R : H s h,L*x*R=1 ∧ ∀ y∈X,y≠x → L*y*R=0 := by
  apply Quotient.selectors_rulesEq (processor s h) wf_sigma (index_good s h) (index_stable s h) markers
    (base s family.A family.M (index s h)) ?_ ?_ X hX x hx
  · intro j
    obtain ⟨rs,hrs,_⟩ := index_good s h j
    exact ⟨rs,hrs,tables_members s family.A family.M (index s h) j hrs⟩
  · intro j rs hrs
    exact tables_absorb s family.A family.M (index s h) j hrs

 theorem group_code_eq_iff (u v : List (Z k)) :
    Quotient.present (processor s h) ((finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).encode u)=
      Quotient.present (processor s h) ((finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).encode v) ↔
        evalWord s u=evalWord s v := by
  have hh := Quotient.present_encode_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (wf_relG k)
    (Search.value (testG s (index s h))) markers.zero
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolateG s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_staticG s family.A family.M (index s h) j hrs)
    (fun j => (group_tests s (index s h) j).2.1)
    (fun j => (group_tests s (index s h) j).2.2)
    (group_tests s (index s h) 0).1
    (codeG_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) u v
  simpa only [group_search_value,Option.some.injEq,WordProblem.testedClass_eq_iff] using hh

def groupEval : FreeMonoid (Z k) →* G where
  toFun w := evalWord s w.toList
  map_one' := rfl
  map_mul' u v := WordProblem.evalWord_append s u.toList v.toList

 theorem groupEval_surjective (hs : Subgroup.closure (Set.range s)=⊤) : Function.Surjective (groupEval s) := by
  intro g
  obtain ⟨w,hw⟩ := FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hs g
  refine ⟨FreeMonoid.ofList (FreeGroup.toWord w),?_⟩
  change evalWord s (FreeGroup.toWord w)=g
  rw [WordProblem.evalWord_eq_lift,FreeGroup.mk_toWord]
  exact hw

noncomputable def groupEmbedding (hs : Subgroup.closure (Set.range s)=⊤) : G →* H s h :=
  Quotient.descendCode (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (groupEval s)
    (groupEval_surjective s hs) (group_code_eq_iff s h)

 theorem groupEmbedding_injective (hs : Subgroup.closure (Set.range s)=⊤) :
    Function.Injective (groupEmbedding s h hs) :=
  Quotient.descendCode_injective (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (groupEval s)
    (groupEval_surjective s hs) (group_code_eq_iff s h)

abbrev KAlphabet := terminalAlphabet family.A
abbrev KMachine := terminalMachine family.A family.M (index s h)
abbrev K := Word.Presentation KAlphabet (KMachine s h)

local instance : Primcodable (ParameterMachine.State family.Q (index s h)) := Effect.finitePrimcodable _
local instance : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  Effect.codeOrder _

noncomputable instance kMonoidWithZero : MonoidWithZero (K s h) := Word.monoidWithZero KAlphabet (KMachine s h)

theorem zero_K : (0 : K s h)=Word.present KAlphabet (KMachine s h) [.zero] := rfl

theorem one_ne_zero_K : (1 : K s h)≠0 :=
  Word.present_nil_ne_omega KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j))

instance kNontrivial : Nontrivial (K s h) := ⟨⟨1,0,one_ne_zero_K s h⟩⟩

/-- The displayed literal presentation for K has a finite alphabet and finitely
    many relators; every side of a relator has length at most four. -/
theorem finite_relations_K :
    {p : List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) ×
      List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) |
        Word.Rule KAlphabet (KMachine s h) p.1 p.2}.Finite :=
  Word.rules_finite KAlphabet (KMachine s h)

theorem computable_wordProblem_K :
    ComputablePred (fun p : List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) ×
      List (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) =>
        Word.present KAlphabet (KMachine s h) p.1=Word.present KAlphabet (KMachine s h) p.2) :=
  Word.computable_wordProblem KAlphabet (KMachine s h) (Effect.primrec_codeOrder _)
    (partrec_raw.comp (Computable.const (index s h)) Computable.id) (index_budget s h)
    family.decode (family.realizes (index s h))

theorem realizes_processor : Word.Realizes KAlphabet (KMachine s h) (tableNormal (processor s h)) :=
  index_fixed s h ▸ family.realizes (index s h)

noncomputable def copyEmbedding : H s h →ₙ* K s h :=
  Quotient.rawMap (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)

theorem copyEmbedding_injective : Function.Injective (copyEmbedding s h) :=
  Quotient.rawMap_injective (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)

theorem copyEmbedding_ne_one (x : H s h) : copyEmbedding s h x≠1 :=
  Quotient.rawMap_ne_one (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

theorem copyEmbedding_ne_zero (x : H s h) : copyEmbedding s h x≠0 :=
  Quotient.rawMap_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

instance hFG : Monoid.FG (H s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Quotient.Rel (processor s h))) PresentedMonoid.surjective_mk

instance kFG : Monoid.FG (K s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Word.Rel KAlphabet (KMachine s h))) PresentedMonoid.surjective_mk

noncomputable def groupUnitsEmbedding (hs : Subgroup.closure (Set.range s)=⊤) : G →* (H s h)ˣ :=
  (groupEmbedding s h hs).toHomUnits

theorem groupUnitsEmbedding_injective (hs : Subgroup.closure (Set.range s)=⊤) :
    Function.Injective (groupUnitsEmbedding s h hs) := by
  intro x y hxy
  exact groupEmbedding_injective s h hs (congrArg Units.val hxy)

abbrev SmallAlgebra (𝕜 : Type*) [CommRing 𝕜] := Contracted.Algebra 𝕜 (H s h)
abbrev BigAlgebra (𝕜 : Type*) [CommRing 𝕜] := Contracted.Algebra 𝕜 (K s h)

theorem smallAlgebra_simple (𝕜 : Type*) [Field 𝕜] : IsSimpleRing (SmallAlgebra s h 𝕜) :=
  Contracted.simple_of_selectors (selectors_H s h)

noncomputable def algebraEmbedding (𝕜 : Type*) [CommRing 𝕜] :
    SmallAlgebra s h 𝕜 →ₙₐ[𝕜] BigAlgebra s h 𝕜 := Contracted.embedding (copyEmbedding s h)

theorem algebraEmbedding_injective (𝕜 : Type*) [CommRing 𝕜] [Nontrivial 𝕜] :
    Function.Injective (algebraEmbedding s h 𝕜) :=
  Contracted.embedding_injective (copyEmbedding s h) (copyEmbedding_injective s h) (copyEmbedding_ne_zero s h)

theorem one_not_in_smallAlgebra (𝕜 : Type*) [CommRing 𝕜] [Nontrivial 𝕜] :
    (1 : BigAlgebra s h 𝕜)∉Set.range (algebraEmbedding s h 𝕜) :=
  Contracted.one_not_mem_range (copyEmbedding s h) (copyEmbedding_ne_one s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.ContractedPresentation

section
variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

def word : FreeMonoid S →* FreeAlgebra k S := FreeMonoid.lift (FreeAlgebra.ι k)

def Rel (a b : FreeAlgebra k S) : Prop :=
  (∃ u v, rel u v ∧ a=word k S u ∧ b=word k S v) ∨ (a=word k S z ∧ b=0)

abbrev Presentation := RingQuot (Rel k S rel z)

def generator (x : S) : Presentation k S rel z :=
  RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)

theorem word_generator (u : FreeMonoid S) :
    FreeMonoid.lift (generator k S rel z) u=RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  have hh : FreeMonoid.lift (generator k S rel z)=
      (RingQuot.mkAlgHom k (Rel k S rel z)).toMonoidHom.comp (word k S) := by
    apply FreeMonoid.hom_eq
    intro x
    rfl
  exact DFunLike.congr_fun hh u

def monoidEval : M →* Presentation k S rel z :=
  (PresentedMonoid.lift (generator k S rel z) (by
    intro a b hab
    rw [word_generator,word_generator]
    exact RingQuot.mkAlgHom_rel k (Or.inl ⟨a,b,hab,rfl,rfl⟩))).comp e.symm.toMonoidHom

theorem monoidEval_mk (u : FreeMonoid S) :
    monoidEval k S rel e z (e (PresentedMonoid.mk rel u))=
      RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  unfold monoidEval
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  exact word_generator k S rel z u

include hz in
theorem monoidEval_zero : monoidEval k S rel e z 0=0 := by
  rw [←hz,monoidEval_mk]
  have he := RingQuot.mkAlgHom_rel k (s:=Rel k S rel z) (Or.inr ⟨rfl,rfl⟩)
  simpa only [map_zero] using he

def toPresentation : Contracted.Algebra k M →ₐ[k] Presentation k S rel z :=
  let f := MonoidAlgebra.lift k (Presentation k S rel z) M (monoidEval k S rel e z)
  let hf : f (MonoidAlgebra.single (0:M) 1)=0 := by
    rw [MonoidAlgebra.lift_single,one_smul,monoidEval_zero k S rel e z hz]
  let g := Contracted.lift f.toNonUnitalAlgHom hf
  { g with
    map_one' := by
      change g (Contracted.quotient k M 1)=1
      exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
    commutes' := by
      intro r
      change g (algebraMap k (Contracted.Algebra k M) r)=_
      rw [Algebra.algebraMap_eq_smul_one,map_smul]
      have he : g 1=1 := by
        change g (Contracted.quotient k M 1)=1
        exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
      rw [he,Algebra.algebraMap_eq_smul_one] }

@[simp] theorem toPresentation_basis (m : M) (r : k) :
    toPresentation k S rel e z hz (Contracted.basis k M m r)=r • monoidEval k S rel e z m := by
  exact MonoidAlgebra.lift_single _ _ _

def monoidBasis : M →* Contracted.Algebra k M where
  toFun m := Contracted.basis k M m 1
  map_one' := Contracted.basis_identity k M
  map_mul' a b := by rw [Contracted.basis_mul,one_mul]

def freeEval : FreeAlgebra k S →ₐ[k] Contracted.Algebra k M :=
  FreeAlgebra.lift k (fun x => monoidBasis k (e (PresentedMonoid.of rel x)))

theorem freeEval_word (u : FreeMonoid S) :
    freeEval k S rel e (word k S u)=Contracted.basis k M (e (PresentedMonoid.mk rel u)) 1 := by
  have hh : (freeEval k S rel e).toMonoidHom.comp (word k S)=
      (monoidBasis k).comp (e.toMonoidHom.comp (PresentedMonoid.mk rel)) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [word,freeEval]
    rfl
  exact DFunLike.congr_fun hh u

include hz in
theorem freeEval_respects : ∀ ⦃a b⦄, Rel k S rel z a b → freeEval k S rel e a=freeEval k S rel e b := by
  intro a b hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [freeEval_word,freeEval_word,PresentedMonoid.mk_eq_mk_of_rel hu]
  · rw [freeEval_word,hz,Contracted.basis_zero,map_zero]

def fromPresentation : Presentation k S rel z →ₐ[k] Contracted.Algebra k M :=
  RingQuot.liftAlgHom k ⟨freeEval k S rel e,freeEval_respects k S rel e z hz⟩

@[simp] theorem fromPresentation_mk (a : FreeAlgebra k S) :
    fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) a)=freeEval k S rel e a := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

end

variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

theorem from_to_basis (m : M) (r : k) :
    fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.basis k M m r))=
      Contracted.basis k M m r := by
  obtain ⟨u,hu⟩ := PresentedMonoid.surjective_mk (e.symm m)
  have hm : m=e (PresentedMonoid.mk rel u) := by rw [hu,e.apply_symm_apply]
  rw [hm,toPresentation_basis,map_smul,monoidEval_mk,fromPresentation_mk,freeEval_word]
  simp [Contracted.basis,←map_smul]

theorem from_to : (fromPresentation k S rel e z hz).comp (toPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply DFunLike.ext
  intro a
  obtain ⟨a,rfl⟩ := (Contracted.zeroIdeal k M).ringCon.mkₐ_surjective (α:=k) a
  change fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.quotient k M a))=Contracted.quotient k M a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single m r => exact from_to_basis k S rel e z hz m r

theorem to_from : (toPresentation k S rel e z hz).comp (fromPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  change toPresentation k S rel e z hz
    (fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)))=_
  rw [fromPresentation_mk]
  change toPresentation k S rel e z hz
    (FreeAlgebra.lift k _ (FreeAlgebra.ι k x))=_
  rw [FreeAlgebra.lift_ι_apply]
  change toPresentation k S rel e z hz
    (Contracted.basis k M (e (PresentedMonoid.mk rel (FreeMonoid.of x))) 1)=_
  rw [toPresentation_basis,one_smul,monoidEval_mk]
  rfl

/-- Exact finite algebra presentation: replace the monoid equations by the same
    free-algebra equations and set a representative of monoid zero equal to zero. -/
def equivalence : Presentation k S rel z ≃ₐ[k] Contracted.Algebra k M :=
  AlgEquiv.ofAlgHom (fromPresentation k S rel e z hz) (toPresentation k S rel e z hz)
    (from_to k S rel e z hz) (to_from k S rel e z hz)

theorem finite_relations (hrel : {p : FreeMonoid S × FreeMonoid S | rel p.1 p.2}.Finite) :
    {p : FreeAlgebra k S × FreeAlgebra k S | Rel k S rel z p.1 p.2}.Finite := by
  apply ((hrel.image (fun p => (word k S p.1, word k S p.2))).union
    (Set.finite_singleton (word k S z,0))).subset
  rintro ⟨a,b⟩ hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨(u,v),hu,rfl⟩
  · exact Or.inr rfl

end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev AlgebraGenerators := Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))

def AlgebraRelations : FreeAlgebra k (AlgebraGenerators s h) → FreeAlgebra k (AlgebraGenerators s h) → Prop :=
  ContractedPresentation.Rel k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h)) [.zero]

/-- The source algebra B has precisely the literal compiler equations and a zero equation. -/
def algebraPresentation : RingQuot (AlgebraRelations s h k) ≃ₐ[k] BigAlgebra s h k :=
  ContractedPresentation.equivalence k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h))
    (MulEquiv.refl (K s h)) [.zero] rfl

theorem algebraRelations_finite :
    {p : FreeAlgebra k (AlgebraGenerators s h) × FreeAlgebra k (AlgebraGenerators s h) |
      AlgebraRelations s h k p.1 p.2}.Finite :=
  ContractedPresentation.finite_relations k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h))
    [.zero] (finite_relations_K s h)

theorem algebraGenerators_finite : Finite (AlgebraGenerators s h) := inferInstance

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section
namespace FiniteAlgebraicEnvelopes.ContractedPresentation
variable (k S : Type*) [CommRing k] (rel : FreeAlgebra k S → FreeAlgebra k S → Prop)

def quotientGenerators (x : S) : RingQuot rel := RingQuot.mkAlgHom k rel (FreeAlgebra.ι k x)

theorem quotientGenerators_generate : Algebra.adjoin k (Set.range (quotientGenerators k S rel))=⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift,AlgHom.range_eq_top]
  have he : FreeAlgebra.lift k (quotientGenerators k S rel)=RingQuot.mkAlgHom k rel := by
    apply FreeAlgebra.hom_ext
    funext x
    rw [Function.comp_apply,Function.comp_apply,FreeAlgebra.lift_ι_apply]
    rfl
  rw [he]
  exact RingQuot.mkAlgHom_surjective k rel

variable {A : Type*} [Ring A] [Algebra k A]

theorem equivalenceGenerators_generate (e : RingQuot rel ≃ₐ[k] A) :
    Algebra.adjoin k (Set.range (fun x => e (quotientGenerators k S rel x)))=⊤ := by
  rw [show Set.range (fun x => e (quotientGenerators k S rel x))=e '' Set.range (quotientGenerators k S rel) from Set.range_comp _ _]
  change Algebra.adjoin k (e.toAlgHom '' Set.range (quotientGenerators k S rel))=⊤
  rw [←AlgHom.map_adjoin,quotientGenerators_generate,Algebra.map_top,AlgHom.range_eq_top]
  exact e.surjective
end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

def bigGenerators : Set (BigAlgebra s h k) := Set.range (fun x => algebraPresentation s h k
  (ContractedPresentation.quotientGenerators k _ (AlgebraRelations s h k) x))

theorem bigGenerators_finite : (bigGenerators s h k).Finite := Set.finite_range _

theorem bigGenerators_generate : Algebra.adjoin k (bigGenerators s h k)=⊤ :=
  ContractedPresentation.equivalenceGenerators_generate k _ _ (algebraPresentation s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.ZeroProduct
variable (K P : Type*) [MonoidWithZero K] [Monoid P]

/-- Collapse precisely the pairs whose first coordinate is zero. This quotient
    is the zero product `(K \ {0}) × P ⊔ {0}` from the algebra construction. -/
def cong : Con (K × P) where
  r a b := a=b ∨ a.1=0 ∧ b.1=0
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by intro a b h; rcases h with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    trans := by
      intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      exact Or.inr ⟨hab.1,hbc.2⟩ }
  mul' := by
    intro a b c d hab hcd
    rcases hab with rfl | hab
    · rcases hcd with rfl | hcd
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [hcd.1],by simp [hcd.2]⟩
    · exact Or.inr ⟨by simp [hab.1],by simp [hab.2]⟩

abbrev Mon := (cong K P).Quotient

def pair : K × P →* Mon K P := (cong K P).mk'

instance : Zero (Mon K P) := ⟨pair K P (0,1)⟩

 theorem pair_eq_iff (a b : K × P) : pair K P a=pair K P b ↔ a=b ∨ a.1=0 ∧ b.1=0 :=
  (cong K P).eq

 theorem pair_zero (p : P) : pair K P (0,p)=0 :=
  (pair_eq_iff K P _ _).mpr (Or.inr ⟨rfl,rfl⟩)

 theorem pair_eq_zero (a : K × P) : pair K P a=0 ↔ a.1=0 := by
  rw [show (0 : Mon K P)=pair K P (0,1) from rfl,pair_eq_iff]
  constructor
  · rintro (h | h)
    · exact congrArg Prod.fst h
    · exact h.1
  · exact fun h => Or.inr ⟨h,rfl⟩

 theorem pair_surjective : Function.Surjective (pair K P) := by
  intro a
  induction a using Con.induction_on
  exact ⟨_,rfl⟩

instance : MonoidWithZero (Mon K P) where
  __ := (inferInstance : Monoid (Mon K P))
  zero := pair K P (0,1)
  zero_mul a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P (0,1)*pair K P a=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (zero_mul _)
  mul_zero a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P a*pair K P (0,1)=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (mul_zero _)

 theorem pair_one [Nontrivial K] : (1 : Mon K P)≠0 := by
  intro h
  have : pair K P (1,1)=0 := h
  have hh := (pair_eq_zero K P _).mp this
  exact one_ne_zero hh

instance [Nontrivial K] : Nontrivial (Mon K P) := ⟨⟨1,0,pair_one K P⟩⟩

/-- A precise normal-form identification with the set in the manuscript. -/
noncomputable def toOption (a : Mon K P) : Option ({k : K // k≠0} × P) := by
  classical
  exact Con.liftOn a (fun b => if h : b.1=0 then none else some (⟨b.1,h⟩,b.2)) (by
    intro a b hab
    rcases hab with rfl | hab
    · rfl
    · simp [hab.1,hab.2])

noncomputable def fromOption : Option ({k : K // k≠0} × P) → Mon K P
  | none => 0
  | some (k,p) => pair K P (k,p)

theorem toOption_pair (k : K) (p : P) :
    toOption K P (pair K P (k,p))=(@dite _ (k=0) (Classical.propDecidable _) (fun _ => none) (fun h => some (⟨k,h⟩,p))) := rfl

theorem toOption_zero : toOption K P 0=none := by
  change toOption K P (pair K P (0,1))=none
  rw [toOption_pair]; simp

noncomputable def equiv : Mon K P ≃ Option ({k : K // k≠0} × P) where
  toFun := toOption K P
  invFun := fromOption K P
  left_inv := by
    classical
    intro a
    obtain ⟨⟨k,p⟩,rfl⟩ := pair_surjective K P a
    rw [toOption_pair]
    by_cases hk : k=0
    · subst k; simpa [fromOption] using (pair_zero K P p).symm
    · simp [fromOption,hk]
  right_inv := by
    classical
    intro a
    cases a with
    | none => exact toOption_zero K P
    | some a =>
      change toOption K P (pair K P (a.1,a.2))=some a
      rw [toOption_pair]; simp [a.1.property]

end FiniteAlgebraicEnvelopes.ZeroProduct

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

abbrev T := FiniteAlgebraicEnvelopes.ZeroProduct.Mon (K s h) PartialAffine.monoid
abbrev TLetter := FiniteY (Γ:=family.Γ) (Q:=family.Q) (index s h)
abbrev TCode := finiteCodeT (Γ:=family.Γ) (Q:=family.Q) k (index s h)
abbrev TClass := finiteClass family.A family.M (index s h)
abbrev TTest := Search.value (finiteTest family.A family.M (index s h))

local instance : DecidableEq (Tested.X Sigma family.Γ family.Q) := inferInstance
local instance : DecidableEq (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) := inferInstance
local instance : DecidableEq (TLetter s h) := inferInstance
local instance : Fintype (TLetter s h) := inferInstance

local instance : LinearOrder (Control.Sector Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  finiteOrder (T:=Sigma) (Γ:=family.Γ) (Q:=family.Q) (index s h)

def tPairEval : FreeMonoid (TLetter s h) →* K s h × PartialAffine.monoid where
  toFun w := (Word.present KAlphabet (KMachine s h) (Projection.left w.toList),PartialAffine.wordValue (Projection.right w.toList))
  map_one' := rfl
  map_mul' u v := by
    apply Prod.ext
    · simp only [FreeMonoid.toList_mul,Projection.left_append]
      rfl
    · apply Subtype.ext
      simp [PartialAffine.wordValue,PartialAffine.value]

def tEval : FreeMonoid (TLetter s h) →* T s h :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair (K s h) PartialAffine.monoid).comp (tPairEval s h)

 theorem tPairEval_surjective : Function.Surjective (tPairEval s h) := by
  rintro ⟨x,y⟩
  obtain ⟨u,rfl⟩ := Word.present_surjective KAlphabet (KMachine s h) x
  obtain ⟨v,rfl⟩ := PartialAffine.wordValue_surjective y
  refine ⟨FreeMonoid.ofList (u.map Sum.inl++v.map Sum.inr),?_⟩
  simp [tPairEval,Projection.left,Projection.right,List.filterMap_map]

 theorem tEval_surjective : Function.Surjective (tEval s h) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair_surjective _ _).comp (tPairEval_surjective s h)

 theorem finiteValue_eq_iff (u v : List (TLetter s h)) :
    finiteValue family.A family.M (index s h) u=finiteValue family.A family.M (index s h) v ↔
      Word.present KAlphabet (KMachine s h) (Projection.left u)=Word.present KAlphabet (KMachine s h) (Projection.left v) := by
  rw [finiteValue,finiteValue,(List.map_injective_iff.mpr (Word.letterMap_injective _ (MachineRealization.ParameterCode.encode_injective (index s h)))).eq_iff]
  exact (Word.present_eq_iff_normal KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j)) _ _).symm

 theorem finiteValue_eq_zero (w : List (TLetter s h)) :
    finiteValue family.A family.M (index s h) w=[.zero] ↔
      Word.present KAlphabet (KMachine s h) (Projection.left w)=(0 : K s h) := by
  rw [finiteValue_zero,zero_K,Word.present_eq_iff_normal KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j)),Word.normal_omega]

 theorem tClass_eq_iff (u v : List (TLetter s h)) :
    TClass s h u=TClass s h v ↔ tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  change ZeroProduct.test _ _ _ u=ZeroProduct.test _ _ _ v ↔
    FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _=FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_iff]
  change ZeroProduct.test _ _ _ u=ZeroProduct.test _ _ _ v ↔
    (Word.present KAlphabet (KMachine s h) (Projection.left u),PartialAffine.wordValue (Projection.right u))=
      (Word.present KAlphabet (KMachine s h) (Projection.left v),PartialAffine.wordValue (Projection.right v)) ∨
       Word.present KAlphabet (KMachine s h) (Projection.left u)=0 ∧ Word.present KAlphabet (KMachine s h) (Projection.left v)=0
  rw [Prod.ext_iff,←finiteValue_eq_iff s h,←finiteValue_eq_zero s h,←finiteValue_eq_zero s h]
  have hp : PartialAffine.wordValue (Projection.right u)=PartialAffine.wordValue (Projection.right v) ↔
      PartialAffine.testedClass (Projection.right u)=PartialAffine.testedClass (Projection.right v) := by
    rw [PartialAffine.testedClass_eq_iff]
    exact Subtype.ext_iff
  rw [hp]
  by_cases hu : finiteValue family.A family.M (index s h) u=[Path.Letter.zero] <;>
    by_cases hv : finiteValue family.A family.M (index s h) v=[Path.Letter.zero] <;>
    simp [ZeroProduct.test,hu,hv]
  aesop

 theorem tClass_eq_none (w : List (TLetter s h)) : TClass s h w=none ↔ tEval s h (FreeMonoid.ofList w)=0 := by
  change ZeroProduct.test _ _ _ w=none ↔ FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _=0
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_zero]
  change ZeroProduct.test _ _ _ w=none ↔ Word.present KAlphabet (KMachine s h) (Projection.left w)=0
  rw [←finiteValue_eq_zero s h]
  simp [ZeroProduct.test]

 theorem tTest_eq_class (w : List (TLetter s h)) : TTest s h w=TClass s h w :=
  search_value_eq family.A family.M (index s h) w.length (index_budget s h (2*w.length)) w le_rfl

 theorem tTest_properties (j : ℕ) : TTest s h []≠none ∧ Static.Contextual (TTest s h) j ∧ Static.ZeroIdeal (TTest s h) j :=
  (tests_bounded family.A family.M (index s h) j (index_budget s h (2*j))
    (family.realizes (index s h)) family.decode).2

 theorem t_code_eq_iff (u v : List (TLetter s h)) :
    Quotient.present (processor s h) ((TCode s h).encode u)=Quotient.present (processor s h) ((TCode s h).encode v) ↔
      tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  rw [Quotient.present_encode_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_isolateT s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1 (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp))]
  rw [tTest_eq_class,tTest_eq_class,tClass_eq_iff]

noncomputable def kappa : T s h →* H s h :=
  Quotient.descendCode (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h)

 theorem kappa_injective : Function.Injective (kappa s h) :=
  Quotient.descendCode_injective (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h)

 theorem kappa_word (w : List (TLetter s h)) : kappa s h (tEval s h (FreeMonoid.ofList w))=
    Quotient.present (processor s h) ((TCode s h).encode w) :=
  Quotient.descendCode_apply (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h) w

end

open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))
local instance : DecidableEq (Tested.X Sigma family.Γ family.Q) := inferInstance
local instance : DecidableEq (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) := inferInstance
local instance : DecidableEq (TLetter s h) := inferInstance
local instance : Fintype (TLetter s h) := inferInstance

 theorem t_normal (w : List (TLetter s h)) :
    Quotient.normal (processor s h) ((TCode s h).encode w)=
      Static.output (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero w :=
  Quotient.normal_encode (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_isolateT s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1 w

 theorem tTest_eq_iff (u v : List (TLetter s h)) :
    TTest s h u=TTest s h v ↔ tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  rw [tTest_eq_class,tTest_eq_class,tClass_eq_iff]

 theorem tTest_eq_none (w : List (TLetter s h)) :
    TTest s h w=none ↔ tEval s h (FreeMonoid.ofList w)=0 := by
  rw [tTest_eq_class,tClass_eq_none]

 theorem kappa_zero : kappa s h 0=0 := by
  obtain ⟨w,hw⟩ := tEval_surjective s h 0
  have hq : TTest s h w.toList=none := (tTest_eq_none s h w.toList).mpr hw
  rw [←hw]
  change kappa s h (tEval s h (FreeMonoid.ofList w.toList))=0
  rw [kappa_word,Quotient.present_normal (processor s h) wf_sigma (index_good s h) (index_stable s h),t_normal]
  simp only [Static.output,hq,ite_true]
  rfl

/-- The source's separator is the seventh letter, distinct from both code
    alphabets, all four selector markers, and the zero letter. -/
def separator : H s h := Quotient.present (processor s h) [6]

 theorem separator_avoid_T : (6:Sigma)∉(TCode s h).Alphabet := by
  intro hh
  have hh := codeT_alphabet (Γ:=family.Γ) (Q:=family.Q) k (index s h) hh
  norm_num [Fin.ext_iff] at hh

 theorem separator_avoid_G : (6:Sigma)∉(finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).Alphabet := by
  intro hh
  have hh := codeG_alphabet (Γ:=family.Γ) (Q:=family.Q) k (index s h) hh
  norm_num [Fin.ext_iff] at hh

 theorem tables_isolate_separator (j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈processor s h j) :
    ∀ p∈rs,p∈Static.table (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero j ∨
      ∃ b∈p.1,b∉(TCode s h).Alphabet ∧ b≠6 := by
  intro p hp
  apply Selectors.process_isolate_separator markers (TCode s h) (wf_relT (index s h)) (TTest s h) 6 ?_
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide) _ _ _
    ((tables_members s family.A family.M (index s h) j hrs p).mp hp)
  intro p hp
  exact Base.isolate_separator (TCode s h) (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h))
    (wf_relT (index s h)) (wf_relG k) (TTest s h) (Search.value (testG s (index s h))) markers.zero (6:Sigma)
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide)
    (separator_avoid_G s h)
    (codes_disjoint (Γ:=family.Γ) (Q:=family.Q) k (index s h)) hp

 theorem separator_word (u v : List (TLetter s h)) :
    kappa s h (tEval s h (FreeMonoid.ofList u))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v))=
      Quotient.present (processor s h) ((TCode s h).encode u++6::(TCode s h).encode v) := by
  rw [kappa_word,kappa_word]
  simp only [separator,←Quotient.present_append,List.append_assoc,List.singleton_append]

 theorem separator_nonzero (x y : T s h) (hx : x≠0) (hy : y≠0) :
    kappa s h x*separator s h*kappa s h y≠0 := by
  obtain ⟨u,rfl⟩ := tEval_surjective s h x
  obtain ⟨v,rfl⟩ := tEval_surjective s h y
  change kappa s h (tEval s h (FreeMonoid.ofList u.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v.toList))≠0
  rw [separator_word,zero_H]
  exact Quotient.present_separator_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero (6:Sigma)
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolate_separator s h j hrs)
    (fun j rs hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1
    (separator_avoid_T s h)
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide)
    (fun he => hx ((tTest_eq_none s h _).mp he)) (fun he => hy ((tTest_eq_none s h _).mp he))

 theorem separator_injective : Function.Injective
    (fun p : {x : T s h // x≠0} × {x : T s h // x≠0} => kappa s h p.1*separator s h*kappa s h p.2) := by
  rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩ ⟨⟨x',hx'⟩,⟨y',hy'⟩⟩ he
  obtain ⟨u,rfl⟩ := tEval_surjective s h x
  obtain ⟨v,rfl⟩ := tEval_surjective s h y
  obtain ⟨u',rfl⟩ := tEval_surjective s h x'
  obtain ⟨v',rfl⟩ := tEval_surjective s h y'
  change kappa s h (tEval s h (FreeMonoid.ofList u.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v.toList))=
    kappa s h (tEval s h (FreeMonoid.ofList u'.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v'.toList)) at he
  rw [separator_word,separator_word] at he
  have hh := (Quotient.present_separator_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero (6:Sigma)
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolate_separator s h j hrs)
    (fun j rs hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1
    (separator_avoid_T s h)
    (fun he => hx ((tTest_eq_none s h u.toList).mp he)) (fun he => hy ((tTest_eq_none s h v.toList).mp he))
    (fun he => hx' ((tTest_eq_none s h u'.toList).mp he)) (fun he => hy' ((tTest_eq_none s h v'.toList).mp he))).mp he
  exact Prod.ext (Subtype.ext ((tTest_eq_iff s h _ _).mp hh.1)) (Subtype.ext ((tTest_eq_iff s h _ _).mp hh.2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section
namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
variable {k H J : Type*} [CommRing k] [MonoidWithZero H] [MonoidWithZero J]

theorem coefficient_map (c : H →*₀ J) (hc : Function.Injective c)
    (h : H) (hh : h≠0) (x : Algebra k H) :
    coefficient (c h) (fun he => hh (hc (he.trans c.map_zero.symm))) (map (k:=k) c x)=coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) _ (map c (quotient k H f))=coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
  | single g r =>
    change coefficient (c h) _ (map c (basis k H g r))=coefficient h hh (basis k H g r)
    rw [map_basis,coefficient_basis,coefficient_basis]
    congr 1
    exact propext hc.eq_iff

theorem map_injective (c : H →*₀ J) (hc : Function.Injective c) :
    Function.Injective (map (k:=k) c) := by
  intro x y he
  apply coefficient_ext
  intro h hh
  rw [←coefficient_map c hc h hh,←coefficient_map c hc h hh,he]
end FiniteAlgebraicEnvelopes.Contracted

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

def kappa₀ : T s h →*₀ H s h := { kappa s h with map_zero' := kappa_zero s h }

def kappaAlgebra (𝕜 : Type*) [CommRing 𝕜] : Contracted.Algebra 𝕜 (T s h) →ₐ[𝕜] SmallAlgebra s h 𝕜 :=
  Contracted.map (kappa₀ s h)

theorem kappaAlgebra_injective (𝕜 : Type*) [CommRing 𝕜] : Function.Injective (kappaAlgebra s h 𝕜) :=
  Contracted.map_injective (kappa₀ s h) (kappa_injective s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.ZeroProduct
open scoped TensorProduct
open Contracted
variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

def left₀ : K →*₀ Mon K P where
  toFun a := pair K P (a,1)
  map_one' := map_one (pair K P)
  map_mul' a b := by simpa using (pair K P).map_mul (a,1) (b,1)
  map_zero' := pair_zero K P 1

def rightBasis : P →* Contracted.Algebra k (Mon K P) where
  toFun p := basis k (Mon K P) (pair K P (1,p)) 1
  map_one' := by
    rw [show pair K P (1,1)=1 from map_one (pair K P)]
    exact basis_identity k (Mon K P)
  map_mul' a b := by
    rw [basis_mul,one_mul,←map_mul]
    simp only [Prod.mk_mul_mk,one_mul]

def leftAlgebra : Contracted.Algebra k K →ₐ[k] Contracted.Algebra k (Mon K P) := Contracted.map (left₀ K P)
def rightAlgebra : MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  MonoidAlgebra.lift k _ P (rightBasis k K P)

@[simp] theorem leftAlgebra_basis (a : K) (r : k) :
    leftAlgebra k K P (basis k K a r)=basis k (Mon K P) (pair K P (a,1)) r :=
  Contracted.map_basis (left₀ K P) a r

@[simp] theorem rightAlgebra_single (p : P) (r : k) :
    rightAlgebra k K P (MonoidAlgebra.single p r)=basis k (Mon K P) (pair K P (1,p)) r := by
  rw [rightAlgebra,MonoidAlgebra.lift_single]
  change r • quotient k (Mon K P) (MonoidAlgebra.single (pair K P (1,p)) 1)=_
  rw [←map_smul]
  simp [basis]

theorem left_right_commute (x : Contracted.Algebra k K) (y : MonoidAlgebra k P) :
    Commute (leftAlgebra k K P x) (rightAlgebra k K P y) := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k K).ringCon.mkₐ_surjective (α:=k) x
  change leftAlgebra k K P (quotient k K f)*rightAlgebra k K P y=
    rightAlgebra k K P y*leftAlgebra k K P (quotient k K f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
  | single a r =>
    change leftAlgebra k K P (basis k K a r)*rightAlgebra k K P y=
      rightAlgebra k K P y*leftAlgebra k K P (basis k K a r)
    rw [leftAlgebra_basis]
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
    | single p t =>
      simp only [rightAlgebra_single,basis_mul,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]
      rw [mul_comm r t]

def tensorMap : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  Algebra.TensorProduct.lift (leftAlgebra k K P) (rightAlgebra k K P) (left_right_commute k K P)

@[simp] theorem tensorMap_basis (a : K) (p : P) (r t : k) :
    tensorMap k K P (basis k K a r ⊗ₜ[k] MonoidAlgebra.single p t)=
      basis k (Mon K P) (pair K P (a,p)) (r*t) := by
  rw [tensorMap,Algebra.TensorProduct.lift_tmul,leftAlgebra_basis,rightAlgebra_single,basis_mul,←map_mul]
  simp

def nonzeroPair (a : {a : K // a≠0} × P) : {t : Mon K P // t≠0} :=
  ⟨pair K P (a.1,a.2),fun he => a.1.property ((pair_eq_zero K P _).mp he)⟩

theorem nonzeroPair_bijective : Function.Bijective (nonzeroPair K P) := by
  constructor
  · rintro ⟨⟨a,ha⟩,p⟩ ⟨⟨b,hb⟩,q⟩ he
    have hh := (pair_eq_iff K P _ _).mp (congrArg Subtype.val he)
    rcases hh with hh | hh
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun t : K×P => t.2) hh)
    · exact (ha hh.1).elim
  · rintro ⟨t,ht⟩
    obtain ⟨⟨a,p⟩,rfl⟩ := pair_surjective K P t
    have ha : a≠0 := fun he => ht ((pair_eq_zero K P _).mpr he)
    exact ⟨(⟨a,ha⟩,p),rfl⟩

def nonzeroEquiv : ({a : K // a≠0} × P) ≃ {t : Mon K P // t≠0} :=
  Equiv.ofBijective (nonzeroPair K P) (nonzeroPair_bijective K P)

def tensorBasis := (monoidBasis (k:=k) (H:=K)).tensorProduct (MonoidAlgebra.basis P k)

def tensorLinearEquiv : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P ≃ₗ[k] Contracted.Algebra k (Mon K P) :=
  (tensorBasis k K P).equiv (monoidBasis (k:=k) (H:=Mon K P)) (nonzeroEquiv K P)

theorem tensorMap_linear : (tensorMap k K P).toLinearMap=(tensorLinearEquiv k K P).toLinearMap := by
  apply (tensorBasis k K P).ext
  rintro ⟨a,p⟩
  change tensorMap k K P ((tensorBasis k K P) (a,p))=tensorLinearEquiv k K P ((tensorBasis k K P) (a,p))
  rw [tensorLinearEquiv,Module.Basis.equiv_apply]
  simp only [tensorBasis,Module.Basis.tensorProduct_apply,monoidBasis_apply]
  change tensorMap k K P (basis k K a 1 ⊗ₜ[k] MonoidAlgebra.single p 1)=_
  rw [tensorMap_basis,one_mul]
  rfl

theorem tensorMap_bijective : Function.Bijective (tensorMap k K P) := by
  change Function.Bijective (tensorMap k K P).toLinearMap
  rw [tensorMap_linear]
  exact (tensorLinearEquiv k K P).bijective

def tensorEquiv : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P ≃ₐ[k] Contracted.Algebra k (Mon K P) :=
  AlgEquiv.ofBijective (tensorMap k K P) (tensorMap_bijective k K P)

end FiniteAlgebraicEnvelopes.ZeroProduct

end

end OAI
