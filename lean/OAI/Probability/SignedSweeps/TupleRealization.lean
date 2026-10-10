import OAI.Probability.SignedSweeps.InvariantObstruction

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev InjectiveTuple (I : Type*) (n : ℕ) := I ↪ Fin n

def tupleEquiv {I : Type*} {n : ℕ} (g : SymmetricGroup n) :
    InjectiveTuple I n ≃ InjectiveTuple I n where
  toFun x := x.trans g.toEmbedding
  invFun x := x.trans g⁻¹.toEmbedding
  left_inv x := by apply Function.Embedding.ext; intro i; exact g.symm_apply_apply (x i)
  right_inv x := by apply Function.Embedding.ext; intro i; exact g.apply_symm_apply (x i)

@[simp] lemma tupleEquiv_apply {I : Type*} {n : ℕ} (g : SymmetricGroup n)
    (x : InjectiveTuple I n) (i : I) : tupleEquiv g x i = g (x i) := rfl

@[simp] lemma tupleEquiv_one {I : Type*} {n : ℕ} (x : InjectiveTuple I n) :
    tupleEquiv 1 x = x := by ext i; rfl

@[simp] lemma tupleEquiv_mul {I : Type*} {n : ℕ} (g h : SymmetricGroup n)
    (x : InjectiveTuple I n) : tupleEquiv (g * h) x = tupleEquiv g (tupleEquiv h x) := rfl

abbrev TupleSpace (I : Type*) [Fintype I] (n : ℕ) :=
  EuclideanSpace ℂ (InjectiveTuple I n)

def tupleIsometry {I : Type*} [Fintype I] {n : ℕ} (g : SymmetricGroup n) :
    TupleSpace I n ≃ₗᵢ[ℂ] TupleSpace I n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (tupleEquiv g)

def tupleRepresentation (I : Type*) [Fintype I] (n : ℕ) :
    Representation ℂ (SymmetricGroup n) (TupleSpace I n) where
  toFun g := (tupleIsometry (I := I) g).toLinearEquiv.toLinearMap
  map_one' := by
    ext f x
    change f (tupleEquiv (1 : SymmetricGroup n) x) = f x
    rw [tupleEquiv_one]
  map_mul' := by
    intro g h
    ext f x
    change f (tupleEquiv (g * h)⁻¹ x) = f (tupleEquiv h⁻¹ (tupleEquiv g⁻¹ x))
    simp

@[simp] lemma tupleRepresentation_apply {I : Type*} [Fintype I] {n : ℕ}
    (g : SymmetricGroup n) (f : TupleSpace I n) (x : InjectiveTuple I n) :
    tupleRepresentation I n g f x = f (tupleEquiv g⁻¹ x) := rfl

def extendOffFirstRow {n : ℕ} (lam : Partition n)
    (x : InjectiveTuple (OffFirstRow lam) n) : SymmetricGroup n :=
  Classical.choose (Equiv.Perm.exists_extending_pair Subtype.val x Subtype.val_injective x.injective)

lemma extendOffFirstRow_apply {n : ℕ} (lam : Partition n)
    (x : InjectiveTuple (OffFirstRow lam) n) (i : OffFirstRow lam) :
    extendOffFirstRow lam x i.1 = x i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    Subtype.val x Subtype.val_injective x.injective) i

def tupleRealization {n : ℕ} (lam : Partition n) :
    Specht lam →ₗ[ℂ] TupleSpace (OffFirstRow lam) n where
  toFun v := WithLp.toLp 2 (fun x => spechtInclusion lam v (extendOffFirstRow lam x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma tupleRealization_apply_perm {n : ℕ} (lam : Partition n) (v : Specht lam)
    (x : InjectiveTuple (OffFirstRow lam) n) (g : SymmetricGroup n)
    (hg : ∀ i : OffFirstRow lam, g i.1 = x i) :
    tupleRealization lam v x = spechtInclusion lam v g := by
  let a : rowSubgroup lam := ⟨(extendOffFirstRow lam x)⁻¹ * g,
    restrict_offFirstRow_eq lam _ _ (fun i => (extendOffFirstRow_apply lam x i).trans (hg i).symm)⟩
  change spechtInclusion lam v (extendOffFirstRow lam x) = spechtInclusion lam v g
  symm
  simpa [a] using specht_right_row lam v a (extendOffFirstRow lam x)

lemma tupleRealization_injective {n : ℕ} (lam : Partition n) :
    Function.Injective (tupleRealization lam) := by
  intro x y h
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  apply PiLp.ext
  intro g
  let t : InjectiveTuple (OffFirstRow lam) n :=
    (Function.Embedding.subtype _).trans g.toEmbedding
  rw [← tupleRealization_apply_perm lam x t g (fun _ => rfl),
    ← tupleRealization_apply_perm lam y t g (fun _ => rfl)]
  exact congrArg (fun f : TupleSpace (OffFirstRow lam) n => f t) h

lemma tupleRealization_intertwines {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (v : Specht lam) :
    tupleRealization lam (spechtRepresentation lam g v) =
      tupleRepresentation (OffFirstRow lam) n g (tupleRealization lam v) := by
  apply PiLp.ext
  intro x
  change spechtInclusion lam v (g⁻¹ * extendOffFirstRow lam x) =
    tupleRealization lam v (tupleEquiv g⁻¹ x)
  symm
  apply tupleRealization_apply_perm
  intro i
  change g⁻¹ (extendOffFirstRow lam x i.1) = g⁻¹ (x i)
  rw [extendOffFirstRow_apply]

lemma tuple_intertwiner_eq_zero_of_fewer_labels {n : ℕ} (lam : Partition n)
    (I : Type*) [Fintype I] (hI : lam.1.rowLen 0 + Fintype.card I < n)
    (T : Specht lam →ₗ[ℂ] TupleSpace I n)
    (hT : ∀ g v, T (spechtRepresentation lam g v) = tupleRepresentation I n g (T v)) :
    T = 0 := by
  classical
  ext v x
  let S : Finset (Fin n) := Finset.univ \ Finset.univ.map x
  have hS : lam.1.rowLen 0 < S.card := by
    simp only [S, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_map]
    omega
  have hfix (g : supportedSubgroup S) : tupleEquiv g.1 x = x := by
    apply Function.Embedding.ext
    intro i
    change g.1 (x i) = x i
    apply g.property
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and, not_not]
    exact ⟨i, rfl⟩
  have hz := congrArg (fun A : Specht lam →ₗ[ℂ] Specht lam => T (A v) x)
    (supportedAverage_eq_zero lam S hS)
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    MonoidHom.comp_apply, Subgroup.subtype_apply, hT, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply, tupleRepresentation_apply, LinearMap.zero_apply, map_zero,
    PiLp.zero_apply] at hz
  have hi (g : supportedSubgroup S) : tupleEquiv g.1⁻¹ x = x := hfix g⁻¹
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul] at hz
  have hu : (Fintype.card (supportedSubgroup S) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa only [← mul_assoc, inv_mul_cancel₀ hu, one_mul, LinearMap.zero_apply, PiLp.zero_apply] using hz

def tupleMarginal {I J : Type*} [Fintype I] [Fintype J] {n : ℕ} (e : J ↪ I) :
    TupleSpace I n →ₗ[ℂ] TupleSpace J n where
  toFun f := WithLp.toLp 2 (fun x => ∑ y : InjectiveTuple I n,
    if e.trans y = x then f y else 0)
  map_add' f g := by
    ext x
    change (∑ y, if e.trans y = x then f y + g y else 0) = _
    simp only [ite_add_zero, Finset.sum_add_distrib]
    rfl
  map_smul' c f := by
    ext x
    change (∑ y, if e.trans y = x then c • f y else 0) =
      c • ∑ y, if e.trans y = x then f y else 0
    simp only [Finset.smul_sum, smul_ite, smul_zero]

lemma tupleMarginal_intertwines {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (e : J ↪ I) (g : SymmetricGroup n) (f : TupleSpace I n) :
    tupleMarginal e (tupleRepresentation I n g f) =
      tupleRepresentation J n g (tupleMarginal e f) := by
  classical
  apply PiLp.ext
  intro x
  change (∑ y, if e.trans y = x then f (tupleEquiv g⁻¹ y) else 0) =
    ∑ y, if e.trans y = tupleEquiv g⁻¹ x then f y else 0
  apply Fintype.sum_equiv (tupleEquiv g⁻¹)
  intro y
  have h : (e.trans y = x) ↔ (e.trans (tupleEquiv g⁻¹ y) = tupleEquiv g⁻¹ x) :=
    (tupleEquiv g⁻¹).injective.eq_iff.symm
  simp only [h]

lemma tupleRealization_marginal_eq_zero {n : ℕ} (lam : Partition n)
    {J : Type*} [Fintype J] (e : J ↪ OffFirstRow lam)
    (he : Fintype.card J < n - lam.1.rowLen 0) (v : Specht lam) :
    tupleMarginal e (tupleRealization lam v) = 0 := by
  have hz := tuple_intertwiner_eq_zero_of_fewer_labels lam J (by omega)
    ((tupleMarginal e).comp (tupleRealization lam)) (by
      intro g x
      simp only [LinearMap.comp_apply, tupleRealization_intertwines, tupleMarginal_intertwines])
  exact LinearMap.congr_fun hz v

end SignedSweeps
end

end OAI
