import OAI.Algebra.Finitistic.Selection.GroupAlgebraPresentation
import Mathlib.Data.Set.Finite.List
import Lean.Elab.Tactic.Omega

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

def word (w : List α) : FreeAlgebra R α := (w.map (FreeAlgebra.ι R)).prod

@[simp] theorem word_nil : word R α [] = 1 := rfl
@[simp] theorem word_append (u v : List α) :
    word R α (u ++ v) = word R α u * word R α v := by
  simp [word]
@[simp] theorem word_singleton (a : α) : word R α [a] = FreeAlgebra.ι R a := by
  simp [word]

def coefficients (p : FreeAlgebra R α) : FreeMonoid α →₀ R :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff

theorem expansion (p : FreeAlgebra R α) :
    (coefficients R α p).sum (fun w c => c • word R α w.toList) = p := by
  have h := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm_apply_apply p
  change MonoidAlgebra.lift R (FreeAlgebra R α) (FreeMonoid α)
    (FreeMonoid.lift (FreeAlgebra.ι R))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) = p at h
  simpa only [MonoidAlgebra.lift_apply, FreeMonoid.lift_apply, coefficients, word] using h

/-- Degree at most n means an R-linear combination of words of length at most n.
This definition includes zero, constants, and linear terms. -/
def degreeLE (n : ℕ) : Submodule R (FreeAlgebra R α) :=
  Submodule.span R {p | ∃ w : List α, w.length ≤ n ∧ p = word R α w}

variable {R α}
theorem word_mem_degreeLE (w : List α) (n : ℕ) (h : w.length ≤ n) :
    word R α w ∈ degreeLE R α n :=
  Submodule.subset_span ⟨w,h,rfl⟩

theorem one_mem_degreeLE (n : ℕ) : (1 : FreeAlgebra R α) ∈ degreeLE R α n := by
  simpa using word_mem_degreeLE (R := R) ([] : List α) n (Nat.zero_le n)

theorem generator_mem_degreeLE (a : α) : FreeAlgebra.ι R a ∈ degreeLE R α 2 := by
  simpa using word_mem_degreeLE (R := R) [a] 2 (by simp)

theorem product_mem_degreeLE (a b : α) :
    FreeAlgebra.ι R a * FreeAlgebra.ι R b ∈ degreeLE R α 2 := by
  simpa [word] using word_mem_degreeLE (R := R) [a,b] 2 (by simp)

variable (R α)
/-- A single common bound for every monomial in finitely many relations. -/
theorem exists_word_bound {κ : Type*} [Finite κ] (p : κ → FreeAlgebra R α) :
    ∃ N : ℕ, ∀ i w, w ∈ (coefficients R α (p i)).support → w.toList.length ≤ N := by
  let := Fintype.ofFinite κ
  classical
  refine ⟨Finset.univ.sup (fun i => (coefficients R α (p i)).support.sup
    (fun w => w.toList.length)), ?_⟩
  intro i w hw
  exact (Finset.le_sup (f := fun w : FreeMonoid α => w.toList.length) hw).trans
    (Finset.le_sup (f := fun i => (coefficients R α (p i)).support.sup
      (fun w => w.toList.length)) (Finset.mem_univ i))



abbrev Word (N : ℕ) := {w : List α // w.length ≤ N}
abbrev Letter (N : ℕ) := α ⊕ Word α N
abbrev Step (N : ℕ) := {s : List α × α // (s.1 ++ [s.2]).length ≤ N}

instance word_finite [Finite α] (N : ℕ) : Finite (Word α N) :=
  List.finite_length_le α N

instance step_finite [Finite α] (N : ℕ) : Finite (Step α N) := by
  apply Finite.of_injective (fun s : Step α N =>
    ((⟨s.val.1, by have := s.property; simp only [List.length_append,
      List.length_singleton] at this; omega⟩ : Word α N), s.val.2))
  intro a b h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x => x.1.val) h) (congrArg (fun x : Word α N × α => x.2) h)

def wordPrefix {N : ℕ} (s : Step α N) : Word α N :=
  ⟨s.val.1, by have := s.property; simp only [List.length_append,
    List.length_singleton] at this; omega⟩
def extended {N : ℕ} (s : Step α N) : Word α N := ⟨s.val.1 ++ [s.val.2], s.property⟩

def inclusion (N : ℕ) : FreeAlgebra R α →ₐ[R] FreeAlgebra R (Letter α N) :=
  FreeAlgebra.lift R (fun a => FreeAlgebra.ι R (.inl a))

def eliminate (N : ℕ) : FreeAlgebra R (Letter α N) →ₐ[R] FreeAlgebra R α :=
  FreeAlgebra.lift R (Sum.elim (FreeAlgebra.ι R) (fun w => word R α w.val))

def encodeWord (N : ℕ) (w : FreeMonoid α) : FreeAlgebra R (Letter α N) :=
  if h : w.toList.length ≤ N then FreeAlgebra.ι R (.inr ⟨w.toList,h⟩) else 0

def linearize (N : ℕ) (p : FreeAlgebra R α) : FreeAlgebra R (Letter α N) :=
  (coefficients R α p).sum (fun w c => c • encodeWord R α N w)

theorem eliminate_linearize (N : ℕ) (p : FreeAlgebra R α)
    (h : ∀ w ∈ (coefficients R α p).support, w.toList.length ≤ N) :
    eliminate R α N (linearize R α N p) = p := by
  apply Eq.trans (b := (coefficients R α p).sum (fun w c => c • word R α w.toList)) _ (expansion R α p)
  simp only [linearize, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  simp [encodeWord, h w hw, eliminate]

theorem linearize_degree (N : ℕ) (p : FreeAlgebra R α) :
    linearize R α N p ∈ degreeLE R (Letter α N) 2 := by
  classical
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  unfold encodeWord
  split
  · apply generator_mem_degreeLE
  · apply Submodule.zero_mem

variable {κ : Type*} (p : κ → FreeAlgebra R α) (N : ℕ)
abbrev EquationIndex := κ ⊕ (Unit ⊕ Step α N)

def relation : EquationIndex α N (κ := κ) → FreeAlgebra R (Letter α N)
  | .inl i => linearize R α N (p i)
  | .inr (.inl _) => FreeAlgebra.ι R (.inr ⟨[], Nat.zero_le N⟩) - 1
  | .inr (.inr s) => FreeAlgebra.ι R (.inr (extended α s)) -
      FreeAlgebra.ι R (.inr (wordPrefix α s)) * FreeAlgebra.ι R (.inl s.val.2)

theorem relation_degree (i : EquationIndex α N (κ := κ)) :
    relation R α p N i ∈ degreeLE R (Letter α N) 2 := by
  rcases i with i | (u | s)
  · exact linearize_degree R α N (p i)
  · exact Submodule.sub_mem _ (generator_mem_degreeLE _) (one_mem_degreeLE _)
  · exact Submodule.sub_mem _ (generator_mem_degreeLE _) (product_mem_degreeLE _ _)

def original : RingCon (FreeAlgebra R α) :=
  ringConGen (fun x y => ∃ i, x = p i ∧ y = 0)

def quadratic : RingCon (FreeAlgebra R (Letter α N)) :=
  ringConGen (fun x y => ∃ i, x = relation R α p N i ∧ y = 0)

abbrev Original := (original R α p).Quotient
abbrev Quadratic := (quadratic R α p N).Quotient

def originalMap : FreeAlgebra R α →ₐ[R] Original R α p := (original R α p).mkₐ R

def quadraticMap : FreeAlgebra R (Letter α N) →ₐ[R] Quadratic R α p N :=
  (quadratic R α p N).mkₐ R

theorem original_relation (i : κ) : originalMap R α p (p i) = 0 :=
  (original R α p).eq.mpr (RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩)

theorem quadratic_relation (i : EquationIndex α N (κ := κ)) :
    quadraticMap R α p N (relation R α p N i) = 0 :=
  (quadratic R α p N).eq.mpr (RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩)



def oldInNew : FreeAlgebra R α →ₐ[R] Quadratic R α p N :=
  (quadraticMap R α p N).comp (inclusion R α N)

/-- Every auxiliary prefix generator equals its original word in the quotient. -/
theorem auxiliary_eq_word (w : List α) (h : w.length ≤ N) :
    quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w,h⟩)) =
      oldInNew R α p N (word R α w) := by
  induction w using List.reverseRecOn with
  | nil =>
    have hh := quadratic_relation R α p N (.inr (.inl ()))
    simpa only [relation, map_sub, map_one, sub_eq_zero, word_nil] using hh
  | append_singleton w a ih =>
    have hw : w.length ≤ N := by simp only [List.length_append, List.length_singleton] at h; omega
    have hh := quadratic_relation R α p N (.inr (.inr ⟨(w,a),h⟩))
    simp only [relation, map_sub, map_mul, sub_eq_zero] at hh
    change quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w ++ [a],h⟩)) =
      quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w,hw⟩)) *
      quadraticMap R α p N (FreeAlgebra.ι R (.inl a)) at hh
    rw [ih hw] at hh
    simpa [word_append, word_singleton, map_mul, oldInNew, inclusion] using hh

theorem linearize_in_quotient (f : FreeAlgebra R α)
    (h : ∀ w ∈ (coefficients R α f).support, w.toList.length ≤ N) :
    quadraticMap R α p N (linearize R α N f) = oldInNew R α p N f := by
  conv_rhs => rw [← expansion R α f]
  simp only [linearize, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [encodeWord, dite_eq_left (h w hw)]
  rw [auxiliary_eq_word]

variable (bound : ∀ i w, w ∈ (coefficients R α (p i)).support → w.toList.length ≤ N)

include bound in
theorem eliminate_relation (i : EquationIndex α N (κ := κ)) :
    originalMap R α p (eliminate R α N (relation R α p N i)) = 0 := by
  rcases i with i | (u | s)
  · rw [relation, eliminate_linearize R α N (p i) (bound i)]
    exact original_relation R α p i
  · simp [relation, eliminate]
  · simp [relation, eliminate, extended, wordPrefix]

def toOriginal : Quadratic R α p N →ₐ[R] Original R α p :=
  (quadratic R α p N).liftₐ ((originalMap R α p).comp (eliminate R α N))
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      exact (eliminate_relation R α p N bound i).trans (map_zero _).symm))

def toQuadratic : Original R α p →ₐ[R] Quadratic R α p N :=
  (original R α p).liftₐ (oldInNew R α p N)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change oldInNew R α p N (p i) = oldInNew R α p N 0
      rw [map_zero, ← linearize_in_quotient R α p N (p i) (bound i)]
      exact quadratic_relation R α p N (.inl i)))

@[simp] theorem toOriginal_quotient (f : FreeAlgebra R (Letter α N)) :
    toOriginal R α p N bound (quadraticMap R α p N f) =
      originalMap R α p (eliminate R α N f) := rfl

@[simp] theorem toQuadratic_quotient (f : FreeAlgebra R α) :
    toQuadratic R α p N bound (originalMap R α p f) = oldInNew R α p N f := rfl

/-- Eliminating auxiliaries after including the old generators fixes the old algebra. -/
theorem original_roundtrip :
    (toOriginal R α p N bound).comp (toQuadratic R α p N bound) =
      AlgHom.id R (Original R α p) := by
  have h : ((toOriginal R α p N bound).comp (toQuadratic R α p N bound)).comp
      (originalMap R α p) = originalMap R α p := by
    apply FreeAlgebra.hom_ext
    funext a
    simp [oldInNew, inclusion, eliminate, AlgHom.comp_apply,
      toQuadratic_quotient, toOriginal_quotient]
  apply AlgHom.ext
  intro x
  obtain ⟨f,rfl⟩ := (original R α p).mkₐ_surjective (α := R) x
  exact DFunLike.congr_fun h f

/-- Prefix equations prove that the other composite fixes every new generator too. -/
theorem quadratic_roundtrip :
    (toQuadratic R α p N bound).comp (toOriginal R α p N bound) =
      AlgHom.id R (Quadratic R α p N) := by
  have h : ((toQuadratic R α p N bound).comp (toOriginal R α p N bound)).comp
      (quadraticMap R α p N) = quadraticMap R α p N := by
    apply FreeAlgebra.hom_ext
    funext a
    rcases a with a | ⟨w,hw⟩
    · simp [oldInNew, inclusion, eliminate, AlgHom.comp_apply,
        toQuadratic_quotient, toOriginal_quotient]
    · change toQuadratic R α p N bound
        (toOriginal R α p N bound (quadraticMap R α p N
          (FreeAlgebra.ι R (.inr ⟨w,hw⟩)))) = _
      rw [toOriginal_quotient]
      simp only [eliminate, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      rw [toQuadratic_quotient]
      exact (auxiliary_eq_word R α p N w hw).symm
  apply AlgHom.ext
  intro x
  obtain ⟨f,rfl⟩ := (quadratic R α p N).mkₐ_surjective (α := R) x
  exact DFunLike.congr_fun h f

/-- An algebra equivalence with mutually inverse composites. -/
def quadraticEquiv : Quadratic R α p N ≃ₐ[R] Original R α p :=
  AlgEquiv.ofAlgHom (toOriginal R α p N bound) (toQuadratic R α p N bound)
    (original_roundtrip R α p N bound) (quadratic_roundtrip R α p N bound)



/-- Converting arbitrary equations to zero relations changes no quotient. -/
theorem equations_eq_zero (lhs rhs : κ → FreeAlgebra R α) :
    ringConGen (fun x y => ∃ i, x = lhs i ∧ y = rhs i) =
      original R α (fun i => lhs i - rhs i) := by
  apply le_antisymm
  · apply RingCon.ringConGen_le.mpr
    rintro x y ⟨i,rfl,rfl⟩
    have h : original R α (fun i => lhs i - rhs i) (lhs i - rhs i) 0 :=
      RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩
    have hh := (original R α (fun i => lhs i - rhs i)).add h
      ((original R α (fun i => lhs i - rhs i)).refl (rhs i))
    simpa only [sub_add_cancel, zero_add] using hh
  · apply RingCon.ringConGen_le.mpr
    rintro x y ⟨i,rfl,rfl⟩
    let c := ringConGen (fun x y => ∃ i, x = lhs i ∧ y = rhs i)
    have h : c (lhs i) (rhs i) := RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩
    have hh := c.add h (c.refl (-rhs i))
    simpa only [← sub_eq_add_neg, sub_self] using hh

/-- A finite noncommutative presentation whose zero relations have degree ≤ 2. -/
def HasFiniteQuadraticPresentation (A : Type*) [Ring A] [Algebra R A] : Prop :=
  ∃ (ι κ : Type) (_ : Finite ι) (_ : Finite κ) (p : κ → FreeAlgebra R ι),
    (∀ i, p i ∈ degreeLE R ι 2) ∧ Nonempty (Original R ι p ≃ₐ[R] A)

/-- Finite prefix conversion of any finite family of polynomial zero relations. -/
theorem finite_zero_presentation_to_quadratic (ι κ : Type) [Finite ι] [Finite κ]
    (p : κ → FreeAlgebra R ι) :
    HasFiniteQuadraticPresentation R (Original R ι p) := by
  obtain ⟨N,hN⟩ := exists_word_bound R ι p
  exact ⟨Letter ι N, EquationIndex ι N (κ := κ), inferInstance, inferInstance,
    relation R ι p N, relation_degree R ι p N, ⟨quadraticEquiv R ι p N hN⟩⟩

variable {R} in
/-- Transport preserves every generator, relation, and degree bound. -/
theorem HasFiniteQuadraticPresentation.of_equiv {A B : Type*} [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (h : HasFiniteQuadraticPresentation R A)
    (e : A ≃ₐ[R] B) : HasFiniteQuadraticPresentation R B := by
  obtain ⟨ι,κ,hι,hκ,p,hd,⟨q⟩⟩ := h
  exact ⟨ι,κ,hι,hκ,p,hd,⟨q.trans e⟩⟩

/-- Equality of generated congruences gives an algebra equivalence of quotients. -/
def quotientCongr {B : Type*} [Ring B] [Algebra R B]
    (c d : RingCon B) (h : c = d) : c.Quotient ≃ₐ[R] d.Quotient := by
  subst d
  exact AlgEquiv.refl

/-- Section 3, lines 22–31: every finitely presented associative unital algebra
has a finite quadratic presentation, allowing linear and constant terms.
Only the coefficient ring is commutative. The algebra itself need not be. -/
theorem finite_presentation_to_quadratic {A : Type*} [Ring A] [Algebra R A]
    (h : GroupAlgebraPresentation.HasFinitePresentation R A) :
    HasFiniteQuadraticPresentation R A := by
  obtain ⟨ι,κ,hι,hκ,lhs,rhs,⟨e⟩⟩ := h
  let : Finite ι := hι
  let : Finite κ := hκ
  have e' : Original R ι (fun i => lhs i - rhs i) ≃ₐ[R] A :=
    (quotientCongr R _ _ (equations_eq_zero R ι lhs rhs).symm).trans e
  exact (finite_zero_presentation_to_quadratic R ι κ (fun i => lhs i - rhs i)).of_equiv e'

/-- The conversion also characterizes finite presentation: forgetting a degree
bound yields the original finite noncommutative notion. -/
theorem finite_presentation_iff_quadratic {A : Type*} [Ring A] [Algebra R A] :
    GroupAlgebraPresentation.HasFinitePresentation R A ↔
      HasFiniteQuadraticPresentation R A := by
  refine ⟨finite_presentation_to_quadratic R, ?_⟩
  rintro ⟨ι,κ,hι,hκ,p,_,⟨e⟩⟩
  exact ⟨ι,κ,hι,hκ,p,fun _ => 0,⟨e⟩⟩

end LittleFinitistic.QuadraticPresentation

end

end OAI
