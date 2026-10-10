import Mathlib
import OAI.GroupTheory.FiniteType.ClassifyingSpacesFiniteExtensionGeometricFromProducts

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace Steinberg
variable (n R : Type*) [Ring R]

structure Root where
  i : n
  j : n
  different : i≠j
  coefficient : R

private def letter (i j : n) (h : i≠j) (a : R) : FreeGroup (Root n R) :=
  FreeGroup.of ⟨i,j,h,a⟩

inductive Relation : FreeGroup (Root n R) → Prop
  | add (i j : n) (h : i≠j) (a b : R) :
      Relation (letter n R i j h a*letter n R i j h b*(letter n R i j h (a+b))⁻¹)
  | chain (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
      Relation (⁅letter n R i j hij a,letter n R j k hjk b⁆*(letter n R i k hik (a*b))⁻¹)
  | away (i j k l : n) (hij : i≠j) (hkl : k≠l) (hil : i≠l) (hjk : j≠k) (a b : R) :
      Relation ⁅letter n R i j hij a,letter n R k l hkl b⁆

def relations : Set (FreeGroup (Root n R)) := Relation n R

abbrev Group := PresentedGroup (relations n R)

variable {n R}
def root (i j : n) (h : i≠j) (a : R) : Group n R := PresentedGroup.of ⟨i,j,h,a⟩

lemma root_add (i j : n) (h : i≠j) (a b : R) :
    root i j h a*root i j h b=root i j h (a+b) := by
  apply eq_of_mul_inv_eq_one
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.add i j h a b)
  simpa only [map_mul,map_inv,letter,PresentedGroup.of,root] using he

lemma root_commutator (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : R) : ⁅root i j hij a,root j k hjk b⁆=root i k hik (a*b) := by
  apply eq_of_mul_inv_eq_one
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.chain i j k hij hjk hik a b)
  simpa only [map_mul,map_inv,map_commutatorElement,letter,PresentedGroup.of,root] using he

lemma root_commute (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.away i j k l hij hkl hil hjk a b)
  simpa only [map_commutatorElement,letter,PresentedGroup.of,root] using he

@[simp] lemma root_zero (i j : n) (h : i≠j) : root i j h (0:R)=1 := by
  have h0 := root_add i j h (0:R) 0
  simpa using h0

@[simp] lemma root_neg (i j : n) (h : i≠j) (a : R) :
    root i j h (-a)=(root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [root_add,neg_add_cancel,root_zero]

def lift {H : Type*} [_root_.Group H] (f : ∀ i j : n, i≠j → R → H)
    (ha : ∀ i j h a b, f i j h a*f i j h b=f i j h (a+b))
    (hc : ∀ i j k hij hjk hik a b, ⁅f i j hij a,f j k hjk b⁆=f i k hik (a*b))
    (hd : ∀ i j k l hij hkl, i≠l → j≠k → ∀ a b, Commute (f i j hij a) (f k l hkl b)) :
    Group n R →* H :=
  PresentedGroup.toGroup (rels:=relations n R) (f:=fun x : Root n R => f x.i x.j x.different x.coefficient) (by
    intro r hr
    cases (show Relation n R r from hr) with
    | add i j h a b => simp [letter,ha]
    | chain i j k hij hjk hik a b =>
      simp only [map_mul,map_inv,map_commutatorElement,letter,FreeGroup.lift_apply_of]
      rw [hc i j k hij hjk hik a b,mul_inv_cancel]
    | away i j k l hij hkl hil hjk a b =>
      simpa [letter] using (hd i j k l hij hkl hil hjk a b).commutator_eq)

@[simp] lemma lift_root {H : Type*} [_root_.Group H] (f : ∀ i j : n, i≠j → R → H)
    (ha hc hd) (i j : n) (h : i≠j) (a : R) :
    lift f ha hc hd (root i j h a)=f i j h a := PresentedGroup.toGroup.of _

@[ext] theorem hom_ext {H : Type*} [_root_.Group H] {f g : Group n R →* H}
    (h : ∀ i j hij a, f (root i j hij a)=g (root i j hij a)) : f=g := by
  apply PresentedGroup.ext
  intro x
  exact h x.i x.j x.different x.coefficient

def map {S : Type*} [Ring S] (φ : R →ₙ+* S) : Group n R →* Group n S :=
  lift (fun i j h a => root i j h (φ a))
    (by intros; rw [root_add,map_add])
    (by intros; rw [root_commutator,map_mul])
    (by intros; apply root_commute <;> assumption)

@[simp] lemma map_root {S : Type*} [Ring S] (φ : R →ₙ+* S) (i j : n) (h : i≠j) (a : R) :
    map φ (root i j h a)=root i j h (φ a) := by simpa only [map,root,lift] using (PresentedGroup.toGroup.of (rels:=relations n R) (x:=⟨i,j,h,a⟩) _)

def matrix [Fintype n] [DecidableEq n] : Group n R →* (Matrix n n R)ˣ :=
  lift NoncommElementary.root
    (fun i j h a b => (NoncommElementary.root_add i j h a b).symm)
    NoncommElementary.root_commutator NoncommElementary.root_commute

@[simp] lemma matrix_root [Fintype n] [DecidableEq n] (i j : n) (h : i≠j) (a : R) :
    matrix (root i j h a)=NoncommElementary.root i j h a := by simpa only [matrix,root,lift] using (PresentedGroup.toGroup.of (rels:=relations n R) (x:=⟨i,j,h,a⟩) _)

lemma matrix_mem [Fintype n] [DecidableEq n] (g : Group n R) :
    matrix g∈NoncommElementary.elementary := by
  apply PresentedGroup.generated_by (relations n R)
    (NoncommElementary.elementary.comap matrix) _ g
  intro x
  change matrix (root x.i x.j x.different x.coefficient)∈NoncommElementary.elementary (R:=R) (n:=n)
  rw [matrix_root]
  exact NoncommElementary.root_mem x.i x.j x.different x.coefficient

def pi [Fintype n] [DecidableEq n] : Group n R →* NoncommElementary.elementary (R:=R) (n:=n) :=
  matrix.codRestrict _ matrix_mem

@[simp] lemma pi_coe [Fintype n] [DecidableEq n] (g : Group n R) :
    (pi g : (Matrix n n R)ˣ)=matrix g := rfl

lemma pi_surjective [Fintype n] [DecidableEq n] : Function.Surjective (pi (n:=n) (R:=R)) := by
  intro ⟨g,hg⟩
  have him : NoncommElementary.elementary (R:=R) (n:=n)≤ matrix.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,j,h,a,rfl⟩
    exact ⟨root i j h a,matrix_root i j h a⟩
  obtain ⟨s,hs⟩ := him hg
  exact ⟨s,Subtype.ext hs⟩

end Steinberg

namespace CompressedSplittings
variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

structure BinaryData where
  s : Fin 2 → R
  d : Fin 2 → R
  s_left : ∀ i, φ 1*s i=s i
  s_right : ∀ i, s i*φ 1=s i
  d_left : ∀ i, φ 1*d i=d i
  d_right : ∀ i, d i*φ 1=d i
  s_commute : ∀ i x, Commute (s i) (φ x)
  d_commute : ∀ i x, Commute (d i) (φ x)
  ds : ∀ i j, d i*s j=if i=j then φ 1 else 0
  partition : s 0*d 0+s 1*d 1=φ 1
end CompressedSplittings

namespace Steinberg
variable {n R S : Type*} [Ring R] [Ring S]

def KernelAnnihilationObligation : Prop :=
  ∀ (φ : R →ₙ+* R), CompressedSplittings.BinaryData φ →
    ∀ z : Group (Fin 6) R, pi z = 1 → map φ z = 1

@[simp] lemma map_id (z : Group n R) : map (NonUnitalRingHom.id R) z = z := by
  have h : map (NonUnitalRingHom.id R) = MonoidHom.id (Group n R) := by
    apply hom_ext
    intros
    rfl
  exact DFunLike.congr_fun h z

@[simp] lemma map_comp {T : Type*} [Ring T] (φ : R →ₙ+* S) (ψ : S →ₙ+* T)
    (z : Group n R) : map (ψ.comp φ) z = map ψ (map φ z) := by
  have h : map (n:=n) (ψ.comp φ) = (map ψ).comp (map φ) := by
    apply hom_ext
    intros
    simp
  exact DFunLike.congr_fun h z

def reindex {m : Type*} (f : n ↪ m) : Group n R →* Group m R :=
  lift (fun i j h a => root (f i) (f j) (f.injective.ne h) a)
    (by intros; exact root_add _ _ _ _ _)
    (by
      intro i j k hij hjk hik a b
      exact root_commutator _ _ _ _ _ (f.injective.ne hik) a b)
    (by
      intro i j k l hij hkl hil hjk a b
      exact root_commute _ _ _ _ _ _ (f.injective.ne hil) (f.injective.ne hjk) a b)

@[simp] lemma reindex_root {m : Type*} (f : n ↪ m) (i j : n) (h : i ≠ j) (a : R) :
    reindex f (root i j h a) = root (f i) (f j) (f.injective.ne h) a := by
  simp [reindex]

lemma root_commutator_reverse (i j k : n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    ⁅root j k hjk b, root i j hij a⁆ = root i k hik (-(a*b)) := by
  rw [root_neg, ← root_commutator i j k hij hjk hik a b,
    commutatorElement_inv]

lemma opposite_commute_of_support (i j k : n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b e : R) (hbe : b*e = b) (hab : a*b = 0)
    (hea : e*a = 0) :
    Commute (root i j hij a) (root j i hij.symm b) := by
  have h₁ : Commute (root i j hij a) (root j k hjk b) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [root_commutator i j k hij hjk hik, hab, root_zero]
  have h₂ : Commute (root i j hij a) (root k i hik.symm e) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [root_commutator_reverse k i j hik.symm hij hjk.symm, hea, neg_zero, root_zero]
  have h := h₁.mul_right h₂
  have h' := (h.mul_right h₁.inv_right).mul_right h₂.inv_right
  rw [← commutatorElement_def, root_commutator j k i hjk hik.symm hij.symm,
    hbe] at h'
  exact h'

lemma roots_commute_orthogonal
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0)
    (i j k l : n) (hij : i ≠ j) (hkl : k ≠ l) (a b : R) :
    Commute (root i j hij (φ a)) (root k l hkl (ψ b)) := by
  by_cases hjk : j = k
  · subst k
    by_cases hil : i = l
    · subst l
      obtain ⟨t, hit, hjt⟩ := hthree i j hij
      apply opposite_commute_of_support i j t hij hit hjt (φ a) (ψ b) (ψ 1)
      · rw [← map_mul, mul_one]
      · exact hφψ a b
      · exact hψφ 1 a
    · apply commutatorElement_eq_one_iff_commute.mp
      rw [root_commutator i j l hij hkl hil, hφψ, root_zero]
  · by_cases hil : i = l
    · subst l
      apply commutatorElement_eq_one_iff_commute.mp
      rw [root_commutator_reverse k i j hkl hij (Ne.symm hjk), hψφ, neg_zero, root_zero]
    · exact root_commute i j k l hij hkl hil hjk (φ a) (ψ b)

lemma commute_of_roots {H : Type*} [_root_.Group H] (f : Group n R →* H)
    (b : H) (hf : ∀ i j hij a, Commute (f (root i j hij a)) b)
    (z : Group n R) : Commute (f z) b := by
  have hz : z ∈ (Subgroup.centralizer ({b} : Set H)).comap f := by
    apply PresentedGroup.generated_by (relations n R)
    intro x
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hf x.i x.j x.different x.coefficient).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp hz

lemma maps_commute_orthogonal
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) (z w : Group n R) :
    Commute (map φ z) (map ψ w) := by
  apply commute_of_roots (map φ) (map ψ w) _ z
  intro i j hij a
  apply Commute.symm
  apply commute_of_roots (map ψ) (map φ (root i j hij a)) _ w
  intro k l hkl b
  simp only [map_root]
  exact (roots_commute_orthogonal hthree φ ψ hφψ hψφ i j k l hij hkl a b).symm

def orthogonalSum (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) : R →ₙ+* S where
  toFun a := φ a + ψ a
  map_zero' := by simp
  map_add' a b := by simp [add_comm, add_left_comm]
  map_mul' a b := by simp [map_mul, mul_add, add_mul, hφψ, hψφ]

@[simp] lemma orthogonalSum_apply (φ ψ : R →ₙ+* S) (hφψ hψφ) (a : R) :
    orthogonalSum φ ψ hφψ hψφ a = φ a + ψ a := rfl

lemma map_orthogonalSum
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) (z : Group n R) :
    map (orthogonalSum φ ψ hφψ hψφ) z = map φ z * map ψ z := by
  let f : Group n R →* Group n S := {
    toFun z := map φ z * map ψ z
    map_one' := by simp
    map_mul' a b := by
      simp only [map_mul]
      exact (maps_commute_orthogonal hthree φ ψ hφψ hψφ b a).mul_mul_mul_comm _ _ }
  have hf : map (orthogonalSum φ ψ hφψ hψφ) = f := by
    apply hom_ext
    intro i j hij a
    simp [f, root_add]
  exact DFunLike.congr_fun hf z

end Steinberg

end

end OAI
