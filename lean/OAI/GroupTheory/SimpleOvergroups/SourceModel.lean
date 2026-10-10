import Mathlib
import OAI.GroupTheory.SimpleOvergroups.CodeEmbedding
import OAI.GroupTheory.SimpleOvergroups.CompilerSemantics
import OAI.GroupTheory.SimpleOvergroups.ContextualCompiler
import OAI.GroupTheory.SimpleOvergroups.SemanticProduct
import OAI.GroupTheory.SimpleOvergroups.SemanticTests

namespace OAI


namespace SimpleFInftyOvergroups.SourceModel
noncomputable section
open scoped Classical FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames

abbrev family := ContextualEncoding.Source.family
abbrev Sigma := ContextualEncoding.Source.Sigma
abbrev P₂ := IdempotentNames.Index (ZMod 2)
abbrev P₃ := IdempotentNames.Index (ZMod 3)
abbrev Syntax := ContextualEncoding.Source.Syntax (Γ:=family.Γ) (Q:=family.Q)
local instance : Primcodable (ZMod 2) := Effect.finitePrimcodable _
local instance : Primcodable (ZMod 3) := Effect.finitePrimcodable _
local instance : DecidableRel ContextualEncoding.Source.rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance : Std.Trichotomous ContextualEncoding.Source.rel := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬ Encodable.encode a < Encodable.encode b at hab
  change ¬ Encodable.encode b < Encodable.encode a at hba
  omega⟩

abbrev Symbols (k : ℕ) := ContextualEncoding.Source.Symbols (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) k
abbrev Keys (k : ℕ) := ContextualEncoding.Source.Keys (Γ:=family.Γ) (Q:=family.Q) k
local instance (k : ℕ) (i : Fin 3) : Primcodable (Symbols k i) :=
  ContextualEncoding.Source.instPrimcodableSymbols i
local instance (k : ℕ) (i : Fin 3) : Primcodable (Keys k i) :=
  ContextualEncoding.Source.instPrimcodableKeys i
abbrev code (k : ℕ) := ContextualEncoding.Source.code (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) (k:=k)
abbrev search (k : ℕ) := ContextualEncoding.Source.search (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) (k:=k)
abbrev wf := ContextualEncoding.Source.wf_rel

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

include h in
theorem bootstrap : ∃ index,
    ContextualEncoding.Source.raw index = tableNormal
      (ContextualEncoding.Source.tables s family.A family.M
        (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) index) ∧
    ∀ n, GoodTable (r:=ContextualEncoding.Source.rel)
      (ContextualEncoding.Source.tables s family.A family.M
        (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) index) n ∧
      PartialBudget (ContextualEncoding.Source.raw index) n :=
  ContextualEncoding.Source.exists_total_fixed_point s family.A family.M
    IdempotentNames.name IdempotentNames.name family.decode family.realizes
    IdempotentNames.idempotent IdempotentNames.idempotent h

def index : ℕ := (bootstrap s h).choose
abbrev tests := fun i => ContextualEncoding.Source.test s family.A family.M
  (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) i (index s h)
abbrev processor := ContextualEncoding.Source.tables s family.A family.M
  (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) (index s h)
abbrev value := fun i => Search.value (tests s h i)

theorem index_fixed : ContextualEncoding.Source.raw (index s h) = tableNormal (processor s h) :=
  (bootstrap s h).choose_spec.1
 theorem index_good (n : ℕ) : GoodTable (r:=ContextualEncoding.Source.rel) (processor s h) n :=
  ((bootstrap s h).choose_spec.2 n).1
 theorem index_budget (n : ℕ) : PartialBudget (ContextualEncoding.Source.raw (index s h)) n :=
  ((bootstrap s h).choose_spec.2 n).2
 theorem table_eq {n : ℕ} {rs : List (List Sigma × List Sigma)} (hr : rs ∈ processor s h n) :
    rs = Families.table (code k) (search k) wf (value s h) none n :=
  FamilyProgram.compute_eq (code k) (search k) none (tests s h) wf hr
 theorem index_stable : ∀ j n, j ≤ n → ∀ rj ∈ processor s h j, ∀ rn ∈ processor s h n,
    Selectors.BoundedEq rj rn j := by
  intro j n hjn rj hrj rn hrn
  exact FamilyProgram.stable (code k) (search k) none (tests s h) wf hjn hrj hrn
 theorem tables_short (n : ℕ) (rs) (hr : rs ∈ processor s h n) : ∀ p ∈ rs, 1 < p.1.length := by
  rw [table_eq s h hr]
  exact fun _ hp => Families.table_short (code k) (search k) wf (value s h) none hp
 theorem tables_absorb (n : ℕ) (rs) (hr : rs ∈ processor s h n) : Absorbs rs none := by
  rw [table_eq s h hr]
  exact Families.absorbs (code k) (search k) wf (value s h) none n
 theorem certificate (n : ℕ) (i : Fin 3) : TestCertificate (code k i) (tests s h i) n :=
  ContextualEncoding.Source.certificate s family.A family.M
    IdempotentNames.name IdempotentNames.name family.decode family.realizes
    IdempotentNames.idempotent IdempotentNames.idempotent (index s h) n
    (index_budget s h _) i
 theorem tables_isolate (i : Fin 3) (n : ℕ) (rs) (hr : rs ∈ processor s h n) :
    ∀ p ∈ rs, p ∈ CodeTable.table (code k i) (search k i) wf (value s h i) none n ∨
      ∃ a ∈ p.1, a ∉ (code k i).alphabet := by
  rw [table_eq s h hr]
  exact fun _ hp => Families.isolate (code k) (search k) wf (value s h) none i
    (ThreeCodes.zero_avoids i _) (fun j hij => ThreeCodes.disjoint hij _ _) hp
 theorem tables_static (i : Fin 3) (n : ℕ) (rs) (hr : rs ∈ processor s h n) :
    ∀ p ∈ CodeTable.table (code k i) (search k i) wf (value s h i) none n, p ∈ rs := by
  rw [table_eq s h hr]
  exact fun _ hp => (Families.mem_table (code k) (search k) wf (value s h) none).mpr (.inr ⟨i,hp⟩)

abbrev L := Quotient.Mon (processor s h)
instance lMonoidWithZero : MonoidWithZero (L s h) :=
  Quotient.monoidWithZero (processor s h) none (index_good s h 2).choose_spec.1
    (tables_absorb s h 2 _ (index_good s h 2).choose_spec.1)
 theorem one_ne_zero_L : (1 : L s h) ≠ 0 :=
  Quotient.present_nil_ne_zero (processor s h) wf (index_good s h) (index_stable s h) none
    (tables_short s h)
instance lNontrivial : Nontrivial (L s h) := nontrivial_of_ne _ _ (one_ne_zero_L s h)

 theorem normal_code (i : Fin 3) (w : List (Symbols k i)) :
    Quotient.normal (processor s h) ((code k i).encode w) =
      CodeTable.output (code k i) wf (value s h i) none w :=
  CodeQuotient.normal_encode (processor s h) wf (index_good s h) (index_stable s h)
    (code k i) (search k i) wf (value s h i) none (tables_short s h)
    (tables_isolate s h i) (tables_static s h i)
    (fun n => (certificate s h n i).contextual) (fun n => (certificate s h n i).ideal)
    (certificate s h 0 i).nonzero w

 theorem code_eq_iff (i : Fin 3) (u v : List (Symbols k i)) :
    Quotient.present (processor s h) ((code k i).encode u) =
      Quotient.present (processor s h) ((code k i).encode v) ↔ value s h i u = value s h i v :=
  CodeQuotient.present_encode_iff (processor s h) wf (index_good s h) (index_stable s h)
    (code k i) (search k i) wf (value s h i) none (tables_short s h)
    (tables_isolate s h i) (tables_static s h i)
    (fun n => (certificate s h n i).contextual) (fun n => (certificate s h n i).ideal)
    (certificate s h 0 i).nonzero (ThreeCodes.zero_avoids i _) u v

 theorem code_zero (i : Fin 3) (w : List (Symbols k i)) (hw : value s h i w = none) :
    Quotient.present (processor s h) ((code k i).encode w) = (0 : L s h) := by
  apply (Quotient.present_eq_iff (processor s h) wf (index_good s h) (index_stable s h) _ _).mpr
  rw [normal_code s h i w,CodeTable.output,ite_eq_left hw]
  obtain ⟨rs,hrs,_⟩ := index_good s h 1
  symm
  exact Quotient.normal_eq_self (processor s h) wf (index_good s h) (index_stable s h) hrs
    (Quotient.irreducible_of_short (fun p hp => tables_short s h 1 rs hrs p hp))

abbrev KAlphabet := ContextualEncoding.Source.terminalAlphabet family.A
abbrev KMachine := ContextualEncoding.Source.terminalMachine family.A family.M (index s h)
abbrev K := Word.Presentation KAlphabet (KMachine s h)
local instance : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  ParameterCode.finiteOrder (index s h)
instance kMonoidWithZero : MonoidWithZero (K s h) := Word.monoidWithZero KAlphabet (KMachine s h)
abbrev normalPresentation := CommonCompiler.normalPresentation family.A family.M (.inr ()) KAlphabet
  (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h) (family.realizes (index s h))
abbrev calculus := CommonCompiler.calculus family.A family.M (.inr ()) KAlphabet
  (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h 0) (family.realizes (index s h))
instance kNontrivial : Nontrivial (K s h) :=
  CommonCompiler.nontrivial family.A family.M (.inr ()) KAlphabet
    (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h) (family.realizes (index s h))

abbrev B := Contracted.Algebra (ZMod 2) (K s h)
abbrev Astar := Contracted.Algebra (ZMod 2) (L s h)
instance bRing : Ring (B s h) := inferInstance
instance bNontrivial : Nontrivial (B s h) := inferInstance
instance bAlgebra : Algebra (ZMod 2) (B s h) := inferInstance
instance aRing : Ring (Astar s h) := inferInstance
instance aNontrivial : Nontrivial (Astar s h) := inferInstance
instance aAlgebra : Algebra (ZMod 2) (Astar s h) := inferInstance

def π : SemanticMatrix.Raw (ZMod 2) Syntax →ₐ[ZMod 2] B s h :=
  (normalPresentation s h).algebraMap (ZMod 2)
def σ : B s h → SemanticMatrix.Raw (ZMod 2) Syntax :=
  (normalPresentation s h).sectionMap (ZMod 2)
 theorem σ_injective : Function.Injective (σ s h) := (normalPresentation s h).sectionMap_injective _
 theorem π_surjective : Function.Surjective (π s h) := (normalPresentation s h).algebraMap_surjective _
 theorem section_collect (a : SemanticMatrix.Raw (ZMod 2) Syntax) :
    σ s h (π s h a) = (calculus s h).collect (ZMod 2) a :=
  (normalPresentation s h).section_algebraMap _ (calculus s h) rfl rfl a
 theorem normal_full (w : List Syntax) :
    ((normalPresentation s h).normal (FreeMonoid.ofList w)).toList ∈
      ContextualEncoding.Source.normal family.A family.M (index s h) w :=
  CommonCompiler.service_full family.A family.M (.inr ()) KAlphabet (index s h) family.decode
    (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h (Word.grade w)) (family.realizes (index s h)) w le_rfl

 theorem value_eq_of_mem {i : Fin 3} {w : List (Symbols k i)} {q : Option (Keys k i)}
    (hq : q ∈ tests s h i w) : value s h i w = q :=
  Part.mem_unique (Search.value_mem (Part.dom_iff_mem.mpr ⟨q,hq⟩)) hq

 theorem group_value (w : List (Symbols k 0)) :
    value s h 0 w = some (WordProblem.testedClass s w) :=
  value_eq_of_mem s h (Part.mem_some _)

 theorem group_code_eq_iff (u v : List (Symbols k 0)) :
    Quotient.present (processor s h) ((code k 0).encode u) =
      Quotient.present (processor s h) ((code k 0).encode v) ↔
      FiniteAlgebraicEnvelopes.evalWord s u = FiniteAlgebraicEnvelopes.evalWord s v := by
  rw [code_eq_iff s h,group_value,group_value,Option.some.injEq,WordProblem.testedClass_eq_iff]

 def codeG (hs : Subgroup.closure (Set.range s) = ⊤) : G →* L s h :=
  CodeQuotient.descendCode (code k 0) (Bootstrap.Source.groupEval s)
    (Bootstrap.Source.groupEval_surjective s hs) (group_code_eq_iff s h)
 theorem codeG_injective (hs : Subgroup.closure (Set.range s) = ⊤) :
    Function.Injective (codeG s h hs) :=
  CodeQuotient.descendCode_injective (code k 0) (Bootstrap.Source.groupEval s)
    (Bootstrap.Source.groupEval_surjective s hs) (group_code_eq_iff s h)

 abbrev ProdMon := SemanticProduct.Mon (K:=K s h)
 abbrev productEval := SemanticProduct.evaluation (normalPresentation s h)
 theorem product_value (w : List (Symbols k 1)) :
    value s h 1 w = SemanticProduct.value (normalPresentation s h) w :=
  value_eq_of_mem s h (SemanticProduct.full (normalPresentation s h)
    (ContextualEncoding.Source.normal family.A family.M (index s h)) (normal_full s h) w)
 theorem product_code_eq_iff (u v : List (Symbols k 1)) :
    Quotient.present (processor s h) ((code k 1).encode u) =
      Quotient.present (processor s h) ((code k 1).encode v) ↔
      productEval s h (FreeMonoid.ofList u) = productEval s h (FreeMonoid.ofList v) := by
  rw [code_eq_iff s h,product_value,product_value,SemanticProduct.value_eq_iff]
 def codeProduct : ProdMon s h →* L s h :=
  CodeQuotient.descendCode (code k 1) (productEval s h)
    (SemanticProduct.evaluation_surjective (normalPresentation s h)) (product_code_eq_iff s h)
 theorem codeProduct_injective : Function.Injective (codeProduct s h) :=
  CodeQuotient.descendCode_injective (code k 1) (productEval s h)
    (SemanticProduct.evaluation_surjective (normalPresentation s h)) (product_code_eq_iff s h)
 theorem codeProduct_zero : codeProduct s h 0 = 0 := by
  obtain ⟨w,hw⟩ := SemanticProduct.evaluation_surjective (normalPresentation s h) 0
  rw [←hw]
  change codeProduct s h ((productEval s h) (FreeMonoid.ofList w.toList))=0
  rw [codeProduct,CodeQuotient.descendCode_apply]
  apply code_zero
  rw [product_value]
  exact (SemanticProduct.value_eq_none (normalPresentation s h) w.toList).mpr hw
 def codeProduct₀ : ProdMon s h →*₀ L s h :=
  { codeProduct s h with map_zero' := codeProduct_zero s h }

 abbrev Acting := SourceEnlargement.Double.W (StageConstruction.Q (B s h))
 abbrev Points := SourceEnlargement.Double.Y
   (Q:=StageConstruction.Q (B s h)) (X:=StageConstruction.X (B s h))
 abbrev ActionMon := SourceActionMonoid.M (Acting s h) (Points s h)
 def actionEval : FreeMonoid (Symbols k 2) →* ActionMon s h :=
  SemanticTests.evaluation (π s h) (σ s h) (σ_injective s h) (calculus s h)
 theorem action_value (w : List (Symbols k 2)) :
    value s h 2 w = (SemanticTests.N₂ (calculus s h)).totalTest
      (SemanticTests.I (π s h) (σ s h) (σ_injective s h) (calculus s h)).gkey
      (SemanticTests.I (π s h) (σ s h) (σ_injective s h) (calculus s h)).xkey w :=
  value_eq_of_mem s h (SemanticTests.full (π s h) (σ s h) (σ_injective s h) (calculus s h)
    (section_collect s h) (ContextualEncoding.Source.normal family.A family.M (index s h))
    (normal_full s h) w)
 theorem action_code_eq_iff (u v : List (Symbols k 2)) :
    Quotient.present (processor s h) ((code k 2).encode u) =
      Quotient.present (processor s h) ((code k 2).encode v) ↔
      actionEval s h (FreeMonoid.ofList u) = actionEval s h (FreeMonoid.ofList v) := by
  apply (code_eq_iff s h 2 u v).trans
  have hk := SemanticTests.keys_eq_iff (π s h) (σ s h) (σ_injective s h) (calculus s h) u v
  exact ((congrArg₂ Eq (action_value s h u) (action_value s h v)).to_iff).trans hk
 theorem actionEval_surjective : Function.Surjective (actionEval s h) :=
  SemanticTests.evaluation_surjective (π s h) (σ s h) (σ_injective s h) (calculus s h)
    (π_surjective s h)
 def codeAction : ActionMon s h →* L s h :=
  CodeQuotient.descendCode (code k 2) (actionEval s h)
    (actionEval_surjective s h) (action_code_eq_iff s h)
 theorem codeAction_injective : Function.Injective (codeAction s h) :=
  CodeQuotient.descendCode_injective (code k 2) (actionEval s h)
    (actionEval_surjective s h) (action_code_eq_iff s h)
 theorem codeAction_zero : codeAction s h 0 = 0 := by
  have hw : actionEval s h (FreeMonoid.ofList [.inr (.inr none)])=0 := rfl
  calc
    codeAction s h 0 = codeAction s h (actionEval s h
        (FreeMonoid.ofList [.inr (.inr none)])) := congrArg (codeAction s h) hw.symm
    _ = Quotient.present (processor s h) ((code k 2).encode [.inr (.inr none)]) :=
      CodeQuotient.descendCode_apply (code k 2) (actionEval s h)
        (actionEval_surjective s h) (action_code_eq_iff s h) _
    _ = 0 := code_zero s h 2 _ (by rw [action_value]; rfl)
 def codeAction₀ : ActionMon s h →*₀ L s h :=
  { codeAction s h with map_zero' := codeAction_zero s h }

end
end SimpleFInftyOvergroups.SourceModel

end OAI
