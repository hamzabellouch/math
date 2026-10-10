import Mathlib
import OAI.Computability.FiniteCompiler.Quotients
import OAI.Computability.FiniteCompiler.SelfReference
import OAI.Computability.FiniteCompiler.UniformPaths
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.BooneHigman.PartialAffine
import OAI.GroupTheory.BooneHigman.WordProblem
import OAI.GroupTheory.SimpleOvergroups.TruncatedAlgebra

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

namespace GroupFamily
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)

def test (w : List (Fin k × Bool)) : Part (Option (List (Fin k × Bool))) :=
  Part.some (some (WordProblem.testedClass s w))

theorem partrec_test (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    Partrec (test s) :=
  (Primrec.option_some.to_comp.comp (WordProblem.computable_testedClass s h)).partrec

theorem context {u v : List (Fin k × Bool)} (h : WordProblem.testedClass s u = WordProblem.testedClass s v)
    (a b : List (Fin k × Bool)) :
    WordProblem.testedClass s (a++u++b) = WordProblem.testedClass s (a++v++b) := by
  apply (WordProblem.testedClass_eq_iff s _ _).mpr
  simp only [WordProblem.evalWord_append]
  rw [(WordProblem.testedClass_eq_iff s _ _).mp h]
end GroupFamily

namespace ProductFamily
variable {A : Type*}
abbrev Letter (A : Type*) := A ⊕ PartialAffine.Letter
abbrev Key (A : Type*) := List A × List PartialAffine.Letter

def cost (c : A → ℕ) : Letter A → ℕ := Sum.elim c (fun _ => 0)
def wordCost (c : A → ℕ) (w : List (Letter A)) : ℕ := (w.map (cost c)).sum

@[simp] theorem wordCost_append (c : A → ℕ) (u v : List (Letter A)) :
    wordCost c (u++v) = wordCost c u + wordCost c v := by simp [wordCost]

theorem wordCost_projection (c : A → ℕ) (w : List (Letter A)) :
    wordCost c w = ((Projection.left w).map c).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp only [wordCost, List.map_cons, cost, Sum.elim_inl, Sum.elim_inr,
      List.sum_cons, Projection.left, List.filterMap_cons, List.map_cons, List.sum_cons, zero_add]
    · exact congrArg (c _ + ·) ih
    · exact ih

variable [DecidableEq A]
def combine (zero : List A) (q : Key A) : Option (Key A) :=
  if q.1 = zero then none else some q

def test (zero : List A) (f : List A → Part (List A)) (w : List (Letter A)) :
    Part (Option (Key A)) :=
  (f (Projection.left w)).map (fun u => combine zero (u,PartialAffine.testedClass (Projection.right w)))

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

def normal (w : List (Letter A)) : List A :=
  (C.normal (FreeMonoid.ofList (Projection.left w))).toList

def value (w : List (Letter A)) : Option (Key A) :=
  combine C.omega.toList (normal C w,PartialAffine.testedClass (Projection.right w))

def grade (w : List (Letter A)) : ℕ := C.grade (FreeMonoid.ofList (Projection.left w))

omit [DecidableEq A] in
@[simp] theorem grade_nil : grade C [] = 0 := C.grade_one
omit [DecidableEq A] in
@[simp] theorem grade_append (u v : List (Letter A)) : grade C (u++v) = grade C u + grade C v := by
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append, C.grade_mul]

omit [DecidableEq A] in
theorem grade_cost (g : A → ℕ) (hg : ∀ u, C.grade (FreeMonoid.ofList u) = (u.map g).sum)
    (w : List (Letter A)) : grade C w = wordCost g w := by
  rw [grade, hg, wordCost_projection]

omit [DecidableEq A] in
theorem normal_context {u v : List (Letter A)} (h : normal C u = normal C v)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) (hv : grade C (a++v++b) ≤ m) :
    normal C (a++u++b) = normal C (a++v++b) := by
  apply congrArg FreeMonoid.toList
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append] at hu hv ⊢
  exact C.context (FreeMonoid.toList.injective h) _ _ hu hv

omit [DecidableEq A] in
theorem normal_zero_context {u : List (Letter A)} (h : normal C u = C.omega.toList)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) :
    normal C (a++u++b) = C.omega.toList := by
  apply congrArg FreeMonoid.toList
  have he : C.normal (FreeMonoid.ofList (Projection.left u)) = C.normal C.omega := by
    rw [C.normal_omega]
    exact FreeMonoid.toList.injective h
  have hb : C.grade (FreeMonoid.ofList (Projection.left a) * C.omega * FreeMonoid.ofList (Projection.left b)) ≤ m := by
    simp only [grade, Projection.left_append, FreeMonoid.ofList_append, C.grade_mul] at hu
    simp only [C.grade_mul, C.grade_omega]
    omega
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append] at hu ⊢
  exact (C.context he _ _ hu hb).trans (C.absorbs _ _)

theorem value_context {u v : List (Letter A)} (h : value C u = value C v)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) (hv : grade C (a++v++b) ≤ m) :
    value C (a++u++b) = value C (a++v++b) := by
  by_cases hz : normal C u = C.omega.toList
  · have hvz : normal C v = C.omega.toList := by
      by_contra hvz
      simp [value, combine, hz, hvz] at h
    simp only [value, combine, normal_zero_context C hz a b hu,
      normal_zero_context C hvz a b hv, ite_true]
  · have hvz : normal C v ≠ C.omega.toList := by
      intro hvz
      simp [value, combine, hz, hvz] at h
    have he : normal C u = normal C v ∧
        PartialAffine.testedClass (Projection.right u) = PartialAffine.testedClass (Projection.right v) := by
      simpa only [value,combine,ite_eq_right hz,ite_eq_right hvz,Option.some.injEq,Prod.mk.injEq] using h
    have hcontext : PartialAffine.testedClass (Projection.right (a++u++b)) =
        PartialAffine.testedClass (Projection.right (a++v++b)) := by
      apply (PartialAffine.testedClass_eq_iff _ _).mpr
      have hmaps := (PartialAffine.testedClass_eq_iff _ _).mp he.2
      simp only [PartialAffine.value] at hmaps
      simp only [Projection.right_append, PartialAffine.value, List.map_append, List.prod_append]
      rw [hmaps]
    simp only [value, normal_context C he.1 a b hu hv, hcontext]

theorem value_zero_context {u : List (Letter A)} (h : value C u = none)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) : value C (a++u++b) = none := by
  have hz : normal C u = C.omega.toList := by simpa [value,combine] using h
  simp only [value,combine,normal_zero_context C hz a b hu,ite_true]

@[simp] theorem value_nil : value C [] ≠ none := by
  have hn : normal C [] ≠ C.omega.toList := by
    intro h
    have he := FreeMonoid.toList.injective h
    exact C.omega_ne_one (by simpa only [Projection.left, List.filterMap_nil, FreeMonoid.ofList_nil, C.normal_one] using he.symm)
  simp only [value,combine,ite_eq_right hn,ne_eq,Option.some_ne_none,not_false_eq_true]

theorem test_full {f : List A → Part (List A)} {d : ℕ} (w : List (Letter A))
    (hw : grade C w ≤ d)
    (hf : ∀ u, C.grade (FreeMonoid.ofList u) ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    value C w ∈ test C.omega.toList f w :=
  (Part.mem_map_iff _).mpr ⟨_,hf _ hw,rfl⟩

variable [Primcodable A]
theorem primrec_combine (zero : List A) : Primrec (combine zero) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const _)) (Primrec.const none)
    (Primrec.option_some.comp Primrec.id)

omit [DecidableEq A] in
theorem primrec_cost {c : A → ℕ} (hc : Primrec c) : Primrec (cost c) :=
  Effect.primrec_sumElim hc (Primrec.const 0)

theorem partrec_test {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
    (zero : List A) (hf : Partrec₂ f) : Partrec₂ (fun p => test zero (f p)) := by
  have hp : Partrec₂ (fun p (w : List (Letter A)) => f p (Projection.left w)) :=
    hf.comp Computable.fst (Projection.primrec_left.to_comp.comp Computable.snd)
  exact (hp.map ((primrec_combine zero).to_comp.comp
    (Computable.snd.pair (PartialAffine.computable_testedClass.comp
      (Projection.primrec_right.to_comp.comp (Computable.snd.comp Computable.fst))))).to₂).to₂
end ProductFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
