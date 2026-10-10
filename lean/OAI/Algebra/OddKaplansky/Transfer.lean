import OAI.Algebra.OddKaplansky.ScalarAlgebra

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10 portUniverse11 portUniverse12

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)
def matrixEquiv : Matrix (Z M q) (Z M q) K ≃ₗ[K] Sector M q hζ :=
  (LinearEquiv.ofInjective (encode M q hζ) (encode_injective M q hζ hc hz)).trans
    (LinearEquiv.ofEq _ _ (encode_range M q hζ hc hz))
lemma matrixEquiv_mul (T S : Matrix (Z M q) (Z M q) K) :
    (matrixEquiv M q hζ hc hz (T*S)).val=(matrixEquiv M q hζ hc hz T).val*(matrixEquiv M q hζ hc hz S).val := encode_mul M q hζ hc hz T S

def scalar {L : Type portUniverse2} [Group L] (T : Matrix (Z M q) (Z M q) (MonoidAlgebra K L)) : MonoidAlgebra K (L×GroupData M q) :=
  MatrixBlock.output (ProductAlgebras.leftMap (K := K) (G := L) (H := GroupData M q)).toRingHom
    (fun u v => ProductAlgebras.rightMap (G := L) (Ω M q hζ u v)) T
include hc hz in
lemma scalar_products {L : Type portUniverse3} [Group L] (A B : Matrix (Z M q) (Z M q) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : scalar M q hζ A*scalar M q hζ B=1 ∧ scalar M q hζ B*scalar M q hζ A≠1 := by
  apply MatrixBlock.prescribed_scalar_products
  · intro u v s t
    rw [← map_mul,Ω_mul M q hζ hc hz]
    split_ifs <;> simp
  · intro x u v
    exact ProductAlgebras.left_right_commute x (Ω M q hζ u v)
  · intro x u v he
    by_contra hx
    exact ProductAlgebras.product_ne_zero hx (Ω_ne_zero M q hζ hc hz u v) he
  · convert hAB using 1 ; congr ; exact Subsingleton.elim _ _
  · convert hBA using 1 ; congr ; exact Subsingleton.elim _ _
include hc hz in
lemma scalar_formula {L : Type portUniverse4} [Group L] (T : Matrix (Z M q) (Z M q) (MonoidAlgebra K L)) :
    scalar M q hζ T=ProductAlgebras.rightMap (G := L) (1-f M q hζ)+
      ∑ u,∑ v,ProductAlgebras.leftMap (T u v)*ProductAlgebras.rightMap (Ω M q hζ u v) := by
  rw [scalar,MatrixBlock.output_formula,← map_sum,Ω_sum M q hζ hc hz,map_sub,map_one]
  rfl
end
end OddKaplansky.Heisenberg

namespace OddKaplansky.Padding
noncomputable section
open scoped Classical BigOperators Matrix
variable {R : Type portUniverse5} {I : Type portUniverse6} {J : Type portUniverse7} [Ring R] [sectionInstance76 : Fintype I] [sectionInstance77 : Fintype J]
def pad (T : Matrix I I R) : Matrix (I⊕J) (I⊕J) R := Matrix.fromBlocks T 0 0 1
lemma pad_mul (A B : Matrix I I R) : pad (J := J) (A*B)=pad A*pad B := by simp [pad,Matrix.fromBlocks_multiply]
lemma pad_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] : pad (R := R) (I := I) (J := J) 1=1 := Matrix.fromBlocks_one
lemma pad_ne_one
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {J : Type contextUniverse3}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} J] {T : Matrix I I R} (h : T≠1) : pad (J := J) T≠1 := by
  intro he
  apply h
  funext i j
  have hh := congrFun (congrFun he (Sum.inl i)) (Sum.inl j)
  simpa [pad,Matrix.one_apply] using hh
lemma products (A B : Matrix I I R) (hAB : A*B=1) (hBA : B*A≠1) :
    pad (J := J) A*pad B=1 ∧ pad (J := J) B*pad A≠1 := by
  rw [← pad_mul,← pad_mul,hAB,pad_one]
  exact ⟨rfl,pad_ne_one hBA⟩
end
end OddKaplansky.Padding

namespace OddKaplansky.FixedField
noncomputable section
open scoped Classical BigOperators Matrix
variable (M : ℕ) (hM : 2≤M) (r : ℕ)
include hM in
lemma power_search : ∃ q, r≤M^q := by
  refine ⟨r,?_⟩
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := r))).trans (Nat.pow_le_pow_left hM r)
def leastQ : ℕ := Nat.find (power_search M hM r)
lemma leastQ_spec : r≤M^(leastQ M hM r) := Nat.find_spec (power_search M hM r)
lemma leastQ_min {q : ℕ} (hq : r≤M^q) : leastQ M hM r≤q := Nat.find_min' (power_search M hM r) hq
variable [NeZero M] {K : Type portUniverse8} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (M : K)≠0)
@[instance_reducible]
def coordinateOrder : LinearOrder (Heisenberg.Z M (leastQ M hM r)) :=
  @FiniteChoice.functionOrder (Fin (leastQ M hM r)) (Fourier.C M) inferInstance inferInstance (SourceOrders.cyclic M)
def indices : (Fin r⊕Fin (M^(leastQ M hM r)-r)) ≃ Heisenberg.Z M (leastQ M hM r) :=
  finSumFinEquiv.trans ((finCongr (by
    have hh := leastQ_spec M hM r
    simp only [Heisenberg.Z,Fintype.card_fun,Fintype.card_fin,Fourier.C,Fintype.card_multiplicative,ZMod.card]
    omega)).trans (@FiniteChoice.orderedIndex _ (coordinateOrder M hM r) inferInstance).symm)
def pad {L : Type portUniverse9} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    Matrix (Heisenberg.Z M (leastQ M hM r)) (Heisenberg.Z M (leastQ M hM r)) (MonoidAlgebra K L) :=
  Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r) (Padding.pad A)
def output {L : Type portUniverse10} [Group L] (A : Matrix (Fin r) (Fin r) (MonoidAlgebra K L)) :
    MonoidAlgebra K (L×Heisenberg.GroupData M (leastQ M hM r)) := Heisenberg.scalar M (leastQ M hM r) hζ (pad M hM r A)
include hc in
lemma output_products {L : Type portUniverse11} [Group L] (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A*B=1) (hBA : B*A≠1) : output M hM r hζ A*output M hM r hζ B=1 ∧ output M hM r hζ B*output M hM r hζ A≠1 := by
  have hcc : (Fintype.card (Fourier.C M) : K)≠0 := by simpa [Fourier.C] using hc
  have hzz : (Fintype.card (Heisenberg.Z M (leastQ M hM r)) : K)≠0 := by
    simpa [Heisenberg.Z,Fourier.C] using pow_ne_zero (leastQ M hM r) hc
  have hpad := Padding.products (J := Fin (M^(leastQ M hM r)-r)) A B
    (by convert hAB using 1 ; congr ; exact Subsingleton.elim _ _)
    (by convert hBA using 1 ; congr ; exact Subsingleton.elim _ _)
  let E := Matrix.reindexAlgEquiv K (MonoidAlgebra K L) (indices M hM r)
  have hone : E 1=1 := map_one E
  have hmul : ∀ X Y, E (X*Y)=E X*E Y := fun X Y => map_mul E X Y
  apply Heisenberg.scalar_products M (leastQ M hM r) hζ hcc hzz
  · change E (Padding.pad A)*E (Padding.pad B)=1
    rw [← hmul]
    have hh : E (Padding.pad A*Padding.pad B)=E 1 := by apply congrArg E; convert hpad.1 using 1 ; congr ; exact Subsingleton.elim _ _
    exact hh.trans hone
  · intro he
    apply hpad.2
    have hh : E (Padding.pad B*Padding.pad A)=E 1 := by
      rw [hmul,hone]
      exact he
    convert E.injective hh using 1 ; congr ; exact Subsingleton.elim _ _

lemma finite_field_data (K : Type portUniverse12) [Field K] [Fintype K] (hK : 3≤Fintype.card K) :
    ∃ ζ : K, IsPrimitiveRoot ζ (Fintype.card K-1) ∧ ((Fintype.card K-1 : ℕ) : K)≠0 := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨u,?_,?_⟩
  · rw [← Fintype.card_units K,← Nat.card_eq_fintype_card,← hu]
    simpa only [orderOf_units] using IsPrimitiveRoot.orderOf (u : K)
  · have hq : (Fintype.card K : K)=0 := by exact FiniteField.cast_card_eq_zero K
    have hsub : ((Fintype.card K-1 : ℕ) : K)=(Fintype.card K : K)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub (R := K) (show 1≤Fintype.card K by omega))
    rw [hsub,hq,zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
end
end OddKaplansky.FixedField

end

end OAI
