import Mathlib
import OAI.Computability.FiniteCompiler.Effectivity
import OAI.Computability.FiniteCompiler.Selectors
import OAI.GroupTheory.BooneHigman.TreeCoherence
import OAI.GroupTheory.SimpleOvergroups.ArrayNames
import OAI.GroupTheory.SimpleOvergroups.CanonicalNames
import OAI.GroupTheory.SimpleOvergroups.TruncatedAlgebra

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical

variable {A k : Type*} [CommSemiring k]

abbrev Name (k A : Type*) := List (k × List A)

def value (p : Name k A) : MonoidAlgebra k (FreeMonoid A) :=
  (p.map fun a => MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1).sum

@[simp] theorem value_nil : value ([] : Name k A) = 0 := rfl
@[simp] theorem value_cons (a : k × List A) (p : Name k A) :
    value (a::p) = MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 + value p := rfl
@[simp] theorem value_append (p q : Name k A) : value (p++q) = value p + value q := by
  simp [value]

def oneName : Name k A := [(1,[])]
@[simp] theorem value_oneName : value (oneName : Name k A) = 1 := by
  simp [oneName,MonoidAlgebra.one_def]

def product (p q : Name k A) : Name k A :=
  p.flatMap fun a => q.map fun b => (a.1*b.1,a.2++b.2)

theorem value_mul_term (a : k × List A) (q : Name k A) :
    value (q.map fun b => (a.1*b.1,a.2++b.2)) =
      MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 * value q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons,value_cons,ih,mul_add,MonoidAlgebra.single_mul_single]
    rfl

@[simp] theorem value_product (p q : Name k A) : value (product p q) = value p * value q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    simp only [product,List.flatMap_cons] at ih ⊢
    rw [value_append,value_mul_term,ih,value_cons,add_mul]

theorem value_surjective : Function.Surjective (value (k:=k) (A:=A)) := by
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => exact ⟨[(1,w.toList)],by simp⟩
  | add p q hp hq =>
    obtain ⟨p,rfl⟩ := hp
    obtain ⟨q,rfl⟩ := hq
    exact ⟨p++q,value_append _ _⟩
  | smul a p hp =>
    obtain ⟨p,rfl⟩ := hp
    refine ⟨p.map (fun b => (a*b.1,b.2)),?_⟩
    induction p with
    | nil => simp
    | cons b p ih => simp [ih,smul_add,MonoidAlgebra.smul_single]

def cost (grade : List A → ℕ) (p : Name k A) : ℕ :=
  (p.map (fun a => grade a.2)).foldr max 0

omit [CommSemiring k] in
theorem cost_le_iff (grade : List A → ℕ) (p : Name k A) (b : ℕ) :
    cost grade p ≤ b ↔ ∀ a ∈ p, grade a.2 ≤ b := by
  induction p with
  | nil => simp [cost]
  | cons a p ih =>
    simp only [cost,List.map_cons,List.foldr_cons,max_le_iff] at ih ⊢
    simp only [List.mem_cons,forall_eq_or_imp]
    exact and_congr_right (fun _ => ih)

omit [CommSemiring k] in
 theorem term_cost_le (grade : List A → ℕ) {a : k × List A} {p : Name k A} (ha : a ∈ p) :
    grade a.2 ≤ cost grade p := (cost_le_iff grade p _).mp le_rfl a ha

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

theorem mem_ball (p : Name k A) :
    value p ∈ C.ball k (cost (fun w => C.grade (FreeMonoid.ofList w)) p) := by
  induction p with
  | nil => exact (C.ball k _).zero_mem
  | cons a p ih =>
    rw [value_cons]
    apply (C.ball k _).add_mem
    · exact C.single_mem_ball k (term_cost_le _ List.mem_cons_self) a.1
    · exact C.ball_mono k (by simp [cost]) ih

def collectName (omega : List A) (normal : List A → List A) (p : Name k A) : Name k A :=
  p.flatMap fun a => if normal a.2 = omega then [] else [(a.1,normal a.2)]

theorem value_collectName (p : Name k A) :
    value (collectName C.omega.toList (fun w => (C.normal (FreeMonoid.ofList w)).toList) p) =
      C.collect k (value p) := by
  induction p with
  | nil => simp [collectName]
  | cons a p ih =>
    change value ((if (C.normal (FreeMonoid.ofList a.2)).toList = C.omega.toList then []
      else [(a.1,(C.normal (FreeMonoid.ofList a.2)).toList)]) ++
      collectName C.omega.toList (fun w => (C.normal (FreeMonoid.ofList w)).toList) p) = _
    rw [value_append,ih,value_cons,map_add,C.collect_single]
    by_cases h : C.normal (FreeMonoid.ofList a.2) = C.omega
    · simp [h]
    · have h' : (C.normal (FreeMonoid.ofList a.2)).toList ≠ C.omega.toList := by
        intro he; exact h (by simpa using congrArg FreeMonoid.ofList he)
      simp [h,h']

variable [Primcodable A] [Primcodable k] [Finite k]

 theorem primrec_product : Primrec₂ (product (k:=k) (A:=A)) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact (((Primrec.dom_finite (fun p : k × k => p.1*p.2)).comp
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂

omit [CommSemiring k] [Finite k] in
 theorem primrec_cost {grade : List A → ℕ} (hg : Primrec grade) : Primrec (cost (k:=k) grade) := by
  unfold cost
  exact Primrec.list_foldr
    (Primrec.list_map Primrec.id (hg.comp (Primrec.snd.comp Primrec.snd)).to₂)
    (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

def partialCollect (omega : List A) (f : List A → Part (List A)) (p : Name k A) : Part (Name k A) :=
  (FiniteAlgebraicEnvelopes.Effect.traverse (fun a : k × List A =>
    (f a.2).map fun w => if w = omega then [] else [(a.1,w)]) p).map List.flatten

omit [CommSemiring k] [Primcodable A] [Primcodable k] [Finite k] in
theorem partialCollect_full (omega : List A) (f : List A → Part (List A))
    (normal : List A → List A) (p : Name k A) (h : ∀ a ∈ p, normal a.2 ∈ f a.2) :
    collectName omega normal p ∈ partialCollect omega f p := by
  have ht := FiniteAlgebraicEnvelopes.Bootstrap.Search.traverse_map
    (f := fun a : k × List A => (f a.2).map fun w => if w = omega then [] else [(a.1,w)])
    (g := fun a => if normal a.2 = omega then [] else [(a.1,normal a.2)])
    p (by intro a ha; exact Part.mem_map _ (h a ha))
  simpa only [partialCollect,collectName,List.flatMap] using Part.mem_map List.flatten ht

omit [Primcodable A] [Primcodable k] [Finite k] in
theorem value_eq_iff_arrays (p q : Name k A) :
    value p = value q ↔ Array.value (id : k → k) (id : List A → List A) p =
      Array.value id id q := by
  have h (p : Name k A) : (value p).coeff =
      Finsupp.mapDomain FreeMonoid.ofList (Array.value (id : k → k) id p) := by
    induction p with
    | nil => simp
    | cons a p ih => simp [ih, Finsupp.mapDomain_add]
  rw [← MonoidAlgebra.coeff_inj, h p, h q]
  exact (Finsupp.mapDomain_injective (f := FreeMonoid.ofList)
    (by intro x y h; exact congrArg FreeMonoid.toList h)).eq_iff

 theorem computable_value_eq : ComputablePred
    (fun p : Name k A × Name k A => value p.1 = value p.2) := by
  have he := Array.computable_value_eq (id : k → k) (id : List A → List A) 0 (·+·)
    (Primrec.dom_finite (fun p : k × k => p.1+p.2))
    Primrec.eq.computablePred Primrec.eq.computablePred rfl (by intros; rfl)
  exact he.of_eq (fun p => (value_eq_iff_arrays p.1 p.2).symm)

def valueKey : MonoidAlgebra k (FreeMonoid A) → ℕ := semanticKey value value_surjective

omit [Finite k] in
 theorem valueKey_injective : Function.Injective (valueKey (k:=k) (A:=A)) :=
  semanticKey_injective value value_surjective

omit [Finite k] in
@[simp] theorem valueKey_value (p : Name k A) : valueKey (value p) = key value p :=
  semanticKey_value value value_surjective p

def partialKey (omega : List A) (f : List A → Part (List A)) (p : Name k A) : Part ℕ :=
  (partialCollect omega f p).map (key value)

omit [Finite k] in
theorem partialKey_full (f : List A → Part (List A)) (p : Name k A)
    (h : ∀ a ∈ p, (C.normal (FreeMonoid.ofList a.2)).toList ∈ f a.2) :
    valueKey (C.collect k (value p)) ∈ partialKey C.omega.toList f p := by
  rw [← value_collectName C p,valueKey_value]
  exact Part.mem_map _ (partialCollect_full _ f _ p h)

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
omit [CommSemiring k] [Finite k] in
 theorem partrec_partialCollect (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialCollect (k:=k) omega (f p)) := by
  have hc : Partrec₂ (fun (p : P) (a : k × List A) =>
      (f p a.2).map fun w => if w = omega then [] else [(a.1,w)]) := by
    have hmap : Computable₂ (fun (p : P × (k × List A)) (w : List A) =>
        if w = omega then [] else [(p.2.1,w)]) := by
      refine (Computable.cond (Primrec.eq.decide.to_comp.comp
        Computable.snd (Computable.const omega)) (Computable.const [])
        (Primrec.list_cons.to_comp.comp
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
          (Computable.const []))).of_eq ?_
      intro p
      simp only [Bool.cond_decide]
    exact ((hf.comp Computable.fst (Computable.snd.comp Computable.snd)).map hmap).to₂
  exact (FiniteAlgebraicEnvelopes.Effect.partrec_traverse_parameter hc).map
    (Primrec.list_flatten.to_comp.comp Computable.snd).to₂
 theorem partrec_partialKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialKey (k:=k) omega (f p)) :=
  (partrec_partialCollect omega hf).map
    ((computable_key value computable_value_eq).comp Computable.snd).to₂
end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
