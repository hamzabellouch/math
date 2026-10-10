import OAI.Analysis.MetricEntropy.SymmetricIndex
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI

universe uK

/-!
# Literal coefficients and actual symmetric multilinear forms

A coefficient is assigned freely to every multiset of basis indices, including
repetitions. Summing over ordered tuples gives an actual multilinear map. Basis
evaluation recovers every coefficient, and every permutation-invariant
multilinear map arises this way. The degree-zero case is included.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

/-- Free literal coefficients on multisets of basis indices. -/
abbrev SymmetricForm (K : Type uK) (r j : ℕ) := Sym (Fin r) j → K

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

/-- Evaluation sums over ordered basis tuples; repeated indices are retained. -/
def eval (F : SymmetricForm K r j) (v : Fin j → (Fin r → K)) : K :=
  ∑ a : Fin j → Fin r, F (tupleSym a) * ∏ i, v i (a i)

@[simp] theorem eval_zero (v : Fin j → (Fin r → K)) :
    eval (0 : SymmetricForm K r j) v = 0 := by
  simp [eval]

@[simp] theorem eval_add (F G : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (F + G) v = eval F v + eval G v := by
  simp [eval, add_mul, Finset.sum_add_distrib]

@[simp] theorem eval_smul (c : K) (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) : eval (c • F) v = c * eval F v := by
  simp only [eval, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private def coordinateProduct (a : Fin j → Fin r) :
    MultilinearMap K (fun _ : Fin j => Fin r → K) K :=
  (MultilinearMap.mkPiAlgebra K (Fin j) K).compLinearMap
    (fun i => LinearMap.proj (a i))

private theorem coordinateProduct_apply (a : Fin j → Fin r)
    (v : Fin j → (Fin r → K)) : coordinateProduct a v = ∏ i, v i (a i) := rfl

/-- The coefficient formula is an actual multilinear map, not an assumed law. -/
def toMultilinearMap (F : SymmetricForm K r j) :
    MultilinearMap K (fun _ : Fin j => Fin r → K) K :=
  ∑ a : Fin j → Fin r, F (tupleSym a) • coordinateProduct a

@[simp] theorem toMultilinearMap_apply (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) : toMultilinearMap F v = eval F v := by
  simp only [toMultilinearMap, _root_.sum_apply, _root_.smul_apply,
    coordinateProduct_apply, smul_eq_mul, eval]

/-- Evaluation at the specified basis tuple recovers its literal coefficient. -/
theorem eval_basis (F : SymmetricForm K r j) (a : Fin j → Fin r) :
    eval F (fun i => Pi.single (a i) (1 : K)) = F (tupleSym a) := by
  classical
  unfold eval
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ a i :=
      not_forall.mp (fun h => hba (funext h))
    have hzero : (∏ i : Fin j, (Pi.single (a i) (1 : K) : Fin r → K) (b i)) =
        (0 : K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hzero, mul_zero]
  · intro h
    exact (h (Finset.mem_univ a)).elim

theorem toMultilinearMap_injective :
    Function.Injective (toMultilinearMap (K := K) (r := r) (j := j)) := by
  intro F G h
  funext s
  obtain ⟨a, rfl⟩ := tupleSym_surjective r j s
  have ha := congrArg
    (fun f : MultilinearMap K (fun _ : Fin j => Fin r → K) K =>
      f (fun i => Pi.single (a i) (1 : K))) h
  simpa only [toMultilinearMap_apply, eval_basis] using ha

/-- Permuting the argument slots does not change the actual multilinear map. -/
theorem toMultilinearMap_domDomCongr (F : SymmetricForm K r j)
    (σ : Equiv.Perm (Fin j)) :
    (toMultilinearMap F).domDomCongr σ = toMultilinearMap F := by
  apply Module.Basis.ext_multilinear (fun _ : Fin j => Pi.basisFun K (Fin r))
  intro a
  simp only [MultilinearMap.domDomCongr_apply, Pi.basisFun_apply,
    toMultilinearMap_apply]
  change eval F (fun i => Pi.single ((a ∘ σ) i) (1 : K)) =
    eval F (fun i => Pi.single (a i) (1 : K))
  rw [eval_basis, eval_basis, tupleSym_comp_perm]

/-- The evaluation is invariant under every permutation, including repeated
vectors and the zero-degree tuple. -/
theorem eval_comp_perm (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) (σ : Equiv.Perm (Fin j)) :
    eval F (v ∘ σ) = eval F v := by
  have h := congrArg
    (fun f : MultilinearMap K (fun _ : Fin j => Fin r → K) K => f v)
    (toMultilinearMap_domDomCongr F σ)
  simpa only [MultilinearMap.domDomCongr_apply, toMultilinearMap_apply,
    Function.comp_def] using h

/-- Symmetry as an actual property of a multilinear map. -/
def IsSymmetric (f : MultilinearMap K (fun _ : Fin j => Fin r → K) K) : Prop :=
  ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → (Fin r → K)), f (v ∘ σ) = f v

theorem toMultilinearMap_isSymmetric (F : SymmetricForm K r j) :
    IsSymmetric (toMultilinearMap F) := by
  intro σ v
  simpa only [toMultilinearMap_apply] using eval_comp_perm F v σ

private def representative (s : Sym (Fin r) j) : Fin j → Fin r :=
  Classical.choose (tupleSym_surjective r j s)

private theorem tupleSym_representative (s : Sym (Fin r) j) :
    tupleSym (representative s) = s :=
  Classical.choose_spec (tupleSym_surjective r j s)

/-- Read coefficients from actual basis evaluations. Symmetry will show that
this does not depend on the representative selected for the multiset. -/
def ofMultilinearMap (f : MultilinearMap K (fun _ : Fin j => Fin r → K) K) :
    SymmetricForm K r j :=
  fun s => f (fun i => Pi.single (representative s i) (1 : K))

theorem ofMultilinearMap_tupleSym
    (f : MultilinearMap K (fun _ : Fin j => Fin r → K) K)
    (hf : IsSymmetric f) (a : Fin j → Fin r) :
    ofMultilinearMap f (tupleSym a) = f (fun i => Pi.single (a i) (1 : K)) := by
  let b := representative (tupleSym a)
  obtain ⟨σ, hσ⟩ := (tupleSym_eq_iff b a).mp (tupleSym_representative (tupleSym a))
  calc
    ofMultilinearMap f (tupleSym a) = f (fun i => Pi.single (b i) (1 : K)) := rfl
    _ = f ((fun i => Pi.single (b i) (1 : K)) ∘ σ) := (hf σ _).symm
    _ = f (fun i => Pi.single (a i) (1 : K)) := by
      apply congrArg f
      funext i
      exact congrArg (fun x : Fin r => Pi.single x (1 : K)) (congrFun hσ i)

/-- Surjectivity onto the actual symmetric multilinear maps follows by basis
extensionality; no characteristic restriction is required for this bridge. -/
theorem toMultilinearMap_ofMultilinearMap
    (f : MultilinearMap K (fun _ : Fin j => Fin r → K) K) (hf : IsSymmetric f) :
    toMultilinearMap (ofMultilinearMap f) = f := by
  apply Module.Basis.ext_multilinear (fun _ : Fin j => Pi.basisFun K (Fin r))
  intro a
  simpa only [Pi.basisFun_apply, toMultilinearMap_apply, eval_basis] using
    ofMultilinearMap_tupleSym f hf a

theorem exists_toMultilinearMap
    (f : MultilinearMap K (fun _ : Fin j => Fin r → K) K) (hf : IsSymmetric f) :
    ∃ F : SymmetricForm K r j, toMultilinearMap F = f :=
  ⟨ofMultilinearMap f, toMultilinearMap_ofMultilinearMap f hf⟩

@[simp] theorem toMultilinearMap_add (F G : SymmetricForm K r j) :
    toMultilinearMap (F + G) = toMultilinearMap F + toMultilinearMap G := by
  ext v
  simp only [toMultilinearMap_apply, _root_.add_apply, eval_add]

@[simp] theorem toMultilinearMap_smul (c : K) (F : SymmetricForm K r j) :
    toMultilinearMap (c • F) = c • toMultilinearMap F := by
  ext v
  simp only [toMultilinearMap_apply, _root_.smul_apply, eval_smul, smul_eq_mul]

/-- The symmetry condition is a linear subspace condition on actual maps. -/
def invariantMultilinearSubmodule (K : Type uK) [CommSemiring K] (r j : ℕ) :
    Submodule K (MultilinearMap K (fun _ : Fin j => Fin r → K) K) where
  carrier := {f | IsSymmetric f}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro f g hf hg σ v
    simp only [_root_.add_apply, hf σ v, hg σ v]
  smul_mem' := by
    intro c f hf σ v
    simp only [_root_.smul_apply, hf σ v]

/-- The concrete coefficient parametrization is linear into actual invariant
multilinear maps. -/
def toInvariantMultilinear : SymmetricForm K r j →ₗ[K]
    invariantMultilinearSubmodule K r j where
  toFun F := ⟨toMultilinearMap F, toMultilinearMap_isSymmetric F⟩
  map_add' F G := Subtype.ext (toMultilinearMap_add F G)
  map_smul' c F := Subtype.ext (toMultilinearMap_smul c F)

/-- Free multiset coefficients and genuine symmetric multilinear maps describe
exactly the same vector space. -/
def equivInvariantMultilinear : SymmetricForm K r j ≃ₗ[K]
    invariantMultilinearSubmodule K r j :=
  LinearEquiv.ofBijective toInvariantMultilinear ⟨
    fun _ _ equality => toMultilinearMap_injective (congrArg Subtype.val equality),
    fun f => ⟨ofMultilinearMap f.val,
      Subtype.ext (toMultilinearMap_ofMultilinearMap f.val f.property)⟩⟩

section Ring

variable {K : Type uK} [CommRing K] {r j : ℕ}

@[simp] theorem eval_neg (F : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (-F) v = -eval F v := by
  simp [eval, Finset.sum_neg_distrib]

@[simp] theorem eval_sub (F G : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (F - G) v = eval F v - eval G v := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

end Ring

end SymmetricForm

end MetricEntropyDuality

end

end OAI
