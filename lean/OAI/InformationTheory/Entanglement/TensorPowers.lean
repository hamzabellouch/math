import OAI.InformationTheory.Entanglement.ChoiTransfer
import OAI.InformationTheory.Entanglement.SecretDefinitions
import OAI.InformationTheory.Entanglement.MultiTensor

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion FiniteConstruction
variable {S n m p q : Type} [Fintype S] [Fintype n] [Fintype m] [Fintype p] [Fintype q]
  [DecidableEq S] [DecidableEq n] [DecidableEq m] [DecidableEq p] [DecidableEq q]
lemma multiTensor_psd {M : S → Mat n} (hM : ∀ s, (M s).PosSemidef) :
    (multiTensor M).PosSemidef := by
  have he : multiTensor M=multiTensor (fun s => CFC.sqrt (M s))*
      (multiTensor (fun s => CFC.sqrt (M s)))ᴴ := by
    rw [multiTensor_adjoint,multiTensor_mul]
    congr 1
    funext s
    exact (TensorCriterion.sqrt_mul_conjTranspose (M s) (hM s)).symm
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

def powerMap (F : Map n m) : Map (S → n) (S → m) where
  toFun A := Matrix.of fun a b => ∑ i, ∑ j, A i j * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s)
  map_add' A B := by
    ext a b
    change (∑ i, ∑ j, (A i j+B i j) * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s)) =
      (∑ i, ∑ j, A i j * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s)) +
      (∑ i, ∑ j, B i j * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s))
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' c A := by
    ext a b
    change (∑ i, ∑ j, (c*A i j) * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s)) =
      c*(∑ i, ∑ j, A i j * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s))
    simp only [mul_assoc,Finset.mul_sum]
omit [Fintype m] [DecidableEq m] in
lemma powerMap_single (F : Map n m) (i j : S → n) :
    powerMap F (Matrix.single i j 1)=fun a b => ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s) := by
  ext a b
  simp [powerMap,Matrix.single_apply,ite_and]
lemma powerMap_cp {F : Map n m} (hF : CP F) : CP (powerMap (S := S) F) := by
  apply cp_of_choi
  have he : choi (powerMap (S := S) F)=
      (multiTensor (fun _ : S => choi F)).submatrix
        (fun a s => (a.1 s,a.2 s)) (fun a s => (a.1 s,a.2 s)) := by
    ext a b
    exact congrFun (congrFun (powerMap_single F a.1 b.1) a.2) b.2
  rw [he]
  exact (multiTensor_psd (fun _ => cp_choi hF)).submatrix _
omit [Fintype m] [DecidableEq m] in
lemma powerMap_input_transpose (F : Map n m) :
    (powerMap (S := S) F).comp transposeMap=powerMap (F.comp transposeMap) := by
  ext A a b
  change (∑ i, ∑ j, A j i * ∏ s, F (Matrix.single (i s) (j s) 1) (a s) (b s))=_
  rw [Finset.sum_comm]
  change (∑ i, ∑ j, A i j * ∏ s, F (Matrix.single (j s) (i s) 1) (a s) (b s))=_
  simp only [powerMap,LinearMap.comp_apply,transposeMap_apply,Matrix.transpose_single]
  rfl
lemma powerMap_input_cp {F : Map n m} (hF : CP (F.comp transposeMap)) :
    CP ((powerMap (S := S) F).comp transposeMap) := by
  rw [powerMap_input_transpose]
  exact powerMap_cp hF

def pull (e : p → n) : Map n p where
  toFun A := A.submatrix e e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p] in
lemma pull_cp (e : p → n) : CP (pull e) := by
  intro k _ A hA
  exact hA.submatrix (fun a : k×p => (a.1,e a.2))
omit [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p] in
lemma pull_transpose (e : p → n) : (pull e).comp transposeMap=transposeMap.comp (pull e) := rfl
omit [DecidableEq n] [DecidableEq m] [DecidableEq p] [DecidableEq q] in
lemma tensorMap_pull (e : p → n) (f : q → m) :
    tensorMap (pull e) (pull f)=pull (fun a => (e a.1,f a.2)) := rfl

omit [DecidableEq n] [DecidableEq m] [DecidableEq p] [DecidableEq q] in
lemma represented_of_witness {R : Mat (n×m)} (hR : R.PosSemidef) (h1 : Matrix.trace R=1)
    [Nonempty p] [Nonempty q] (L : Map p n) (M : Map q m) (χ : p×q → ℂ)
    (hL : CP L) (hLT : CP (L.comp transposeMap))
    (hM : CP M) (hMT : CP (M.comp transposeMap))
    (he : R=tensorMap L M (projector χ)) : Represented R := by
  let e := Fintype.equivFin p
  let f := Fintype.equivFin q
  let L' := L.comp (pull e)
  let M' := M.comp (pull f)
  let χ' : Fin (Fintype.card p) × Fin (Fintype.card q) → ℂ :=
    fun a => χ (e.symm a.1,f.symm a.2)
  refine ⟨hR,h1,Fintype.card p,Fintype.card q,Fintype.card_pos,Fintype.card_pos,L',M',χ',
    cp_comp hL (pull_cp e),?_,cp_comp hM (pull_cp f),?_,?_⟩
  · change CP ((L.comp (pull e)).comp transposeMap)
    rw [LinearMap.comp_assoc,pull_transpose,← LinearMap.comp_assoc]
    exact cp_comp hLT (pull_cp e)
  · change CP ((M.comp (pull f)).comp transposeMap)
    rw [LinearMap.comp_assoc,pull_transpose,← LinearMap.comp_assoc]
    exact cp_comp hMT (pull_cp f)
  · change R=tensorMap (L.comp (pull e)) (M.comp (pull f)) (projector χ')
    rw [← tensorMap_comp,tensorMap_pull]
    change R=tensorMap L M ((projector χ').submatrix (fun a => (e a.1,f a.2)) (fun a => (e a.1,f a.2)))
    have hc : (projector χ').submatrix (fun a => (e a.1,f a.2)) (fun a => (e a.1,f a.2))=projector χ := by
      ext a b
      simp [χ',projector,Matrix.vecMulVec_apply]
    rw [hc]
    exact he

omit [DecidableEq n] [DecidableEq m] in
lemma tensorMap_entry_sum (L : Map p n) (M : Map q m) (A : Mat (p×q))
    (a b : n×m) : tensorMap L M A a b=
      ∑ i, ∑ j, A i j*(L (Matrix.single i.1 j.1 1) a.1 b.1*
        M (Matrix.single i.2 j.2 1) a.2 b.2) := by
  rw [linearMap_entries (tensorMap L M)]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← single_product,tensorMap_kronecker]
  rfl

def tensorPower (R : Mat (n×m)) : Mat ((S → n)×(S → m)) :=
  fun a b => ∏ s, R (a.1 s,a.2 s) (b.1 s,b.2 s)
def vectorPower (χ : p×q → ℂ) : (S → p)×(S → q) → ℂ :=
  fun a => ∏ s, χ (a.1 s,a.2 s)
lemma tensorPower_psd {R : Mat (n×m)} (hR : R.PosSemidef) :
    (tensorPower (S := S) R).PosSemidef :=
  (multiTensor_psd (fun _ : S => hR)).submatrix (fun a : (S → n)×(S → m) => fun s => (a.1 s,a.2 s))
omit [DecidableEq n] [DecidableEq m] in
lemma tensorPower_trace (R : Mat (n×m)) :
    Matrix.trace (tensorPower (S := S) R)=(Matrix.trace R)^(Fintype.card S) := by
  let e := Equiv.arrowProdEquivProdArrow S (fun _ => n) (fun _ => m)
  have he := e.symm.sum_comp (fun a : S → n×m => ∏ s, R (a s) (a s))
  change (∑ a : (S → n)×(S → m), ∏ s, R (a.1 s,a.2 s) (a.1 s,a.2 s))=_
  calc
    _ = ∑ i : S → n×m, ∏ s, R (i s) (i s) := he
    _ = ∏ _ : S, ∑ a : n×m, R a a := (Fintype.prod_sum (fun _ : S => fun a : n×m => R a a)).symm
    _ = _ := by simp only [Matrix.trace,Matrix.diag,Finset.prod_const,Finset.card_univ]
omit [DecidableEq n] [DecidableEq m] in
lemma powerMap_representation (L : Map p n) (M : Map q m) (χ : p×q → ℂ) :
    tensorPower (S := S) (tensorMap L M (projector χ))=
      tensorMap (powerMap L) (powerMap M) (projector (vectorPower χ)) := by
  ext a b
  change (∏ s, tensorMap L M (projector χ) (a.1 s,a.2 s) (b.1 s,b.2 s))=_
  simp_rw [tensorMap_entry_sum]
  simp only [Fintype.sum_prod_type]
  simp_rw [Fintype.prod_sum]
  simp only [powerMap_single,projector,Matrix.vecMulVec_apply,Pi.star_apply,vectorPower]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.prod_mul_distrib,star_prod]

theorem represented_tensorPower {R : Mat (n×m)} (hR : Represented R) :
    Represented (tensorPower (S := S) R) := by
  obtain ⟨hRp,hRt,r,s,hr,hs,L,M,χ,hL,hLT,hM,hMT,hEq⟩ := hR
  have : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  apply represented_of_witness (tensorPower_psd hRp) (by rw [tensorPower_trace,hRt,one_pow])
    (powerMap L) (powerMap M) (vectorPower χ) (powerMap_cp hL) (powerMap_input_cp hLT)
    (powerMap_cp hM) (powerMap_input_cp hMT)
  rw [hEq]
  exact powerMap_representation L M χ

end SecretKey

end

end OAI
