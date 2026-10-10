import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.InductiveLimit

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra


open scoped CStarAlgebra ComplexOrder
namespace KirchbergRordam.UnitaryPaths

variable {A : Type*} [CStarAlgebra A]


@[fun_prop] lemma phase_continuous : Continuous phase := by unfold phase; fun_prop
@[simp] lemma phase_zero : phase 0 = 1 := by simp [phase]
@[simp] lemma phase_one : phase 1 = -1 := by simp [phase, Complex.exp_pi_mul_I]
lemma phase_unitary (t : unitInterval) : star (phase t) * phase t = 1 := by
  have hn : ‖phase t‖ = 1 := by
    simpa [phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I ((t:ℝ) * Real.pi)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
  norm_num


lemma involutionValue_continuous (U : A) : Continuous (involutionValue U) := by
  unfold involutionValue
  fun_prop

lemma involutionValue_unitary (U : A) (hs : star U = U) (hm : U * U = 1)
    (t : unitInterval) : involutionValue U t ∈ unitary A := by
  have hz := phase_unitary t
  have h1 : (star ((1:ℂ)+phase t)/2)*((1+phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1-phase t)/2)=1 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1+star (phase t)*phase t)/2 := by ring
      _ = 1 := by rw [hz]; norm_num
  have h2 : (star ((1:ℂ)+phase t)/2)*((1-phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1+phase t)/2)=0 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1-star (phase t)*phase t)/2 := by ring
      _ = 0 := by rw [hz]; norm_num
  have h : star (involutionValue U t) * involutionValue U t = 1 := by
    simp only [involutionValue, star_add, star_smul, star_one, hs, star_div₀,
      star_ofNat, star_sub, smul_add, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, one_mul, mul_one, hm]
    calc
      _ = (((1+star (phase t))/2)*((1+phase t)/2)+
            ((1-star (phase t))/2)*((1-phase t)/2)) • (1:A) +
          (((1+star (phase t))/2)*((1-phase t)/2)+
            ((1-star (phase t))/2)*((1+phase t)/2)) • U := by
              rw [add_smul, add_smul]; module
      _ = 1 := by
        simp only [star_add, star_sub, star_one] at h1 h2
        rw [h1, h2, one_smul, zero_smul, add_zero]
  refine ⟨h, ?_⟩
  have hc : Commute (involutionValue U t) (star (involutionValue U t)) := by
    unfold involutionValue
    simp only [star_add, star_smul, star_one, hs]
    exact ((Commute.one_left _).smul_left _).add_left
      ((((Commute.one_right U).smul_right _).add_right
        ((Commute.refl U).smul_right _)).smul_left _)
  exact hc.eq.trans h


end KirchbergRordam.UnitaryPaths

namespace KirchbergRordam.MatrixPermutationPath
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma perm_one : perm (1 : Equiv.Perm ι) = 1 := by
  apply Subtype.ext
  change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
  simp
lemma perm_mul (σ τ : Equiv.Perm ι) : perm (σ*τ) = perm σ * perm τ := by
  apply Subtype.ext
  change ((σ*τ)⁻¹).permMatrix ℂ = σ⁻¹.permMatrix ℂ * τ⁻¹.permMatrix ℂ
  simp

lemma perm_swap_selfadjoint (i j : ι) : star (perm (Equiv.swap i j) : Mat ι) =
    (perm (Equiv.swap i j) : Mat ι) := by
  change ((Equiv.swap i j)⁻¹.permMatrix ℂ)ᴴ = (Equiv.swap i j)⁻¹.permMatrix ℂ
  simp


theorem joined_one_perm (σ : Equiv.Perm ι) : Joined (1 : unitary (Mat ι)) (perm σ) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa using Joined.refl (1 : unitary (Mat ι))
  | swap_mul σ i j hij ih =>
    rw [perm_mul]
    have hi : Joined (1 : unitary (Mat ι)) (perm (Equiv.swap i j)) :=
      ⟨UnitaryPaths.involutionPath _ (perm_swap_selfadjoint i j)⟩
    simpa only [one_mul] using hi.mul ih

lemma perm_conjugation (σ : Equiv.Perm ι) (a : Mat ι) :
    Unitary.conjStarAlgAut ℂ _ (perm σ) a = CStarMatrix.reindexₐ ℂ ℂ σ a := by
  change σ⁻¹.permMatrix ℂ * CStarMatrix.ofMatrix.symm a * (σ⁻¹.permMatrix ℂ)ᴴ =
    Matrix.reindex σ σ (CStarMatrix.ofMatrix.symm a)
  rw [Matrix.conjTranspose_permMatrix]
  change σ.symm.toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl


end KirchbergRordam.MatrixPermutationPath

namespace KirchbergRordam.MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]


@[simp] lemma block_apply (a : ι → Mat κ) (i j : κ) (k l : ι) :
    block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl
lemma block_injective : Function.Injective (block (ι:=ι) (κ:=κ)) := by
  intro a b h
  funext k
  ext i j
  have := congrArg (fun m : Mat (κ×ι) => m (i,k) (j,k)) h
  simpa [block_apply] using this


lemma evaluationBlock_continuous (ξ : ι → C(unitInterval, unitInterval))
    (f : C(unitInterval, Mat κ)) : Continuous (fun t => evaluationBlock ξ t f) :=
  (map_continuous block).comp (continuous_pi (fun i => f.continuous.comp (ξ i).continuous))


lemma diagonal_injective (ξ : ι → C(unitInterval, unitInterval))
    (hcover : ∀ s : unitInterval, ∃ i t, ξ i t = s) :
    Function.Injective (diagonal (κ:=κ) ξ) := by
  intro f g h
  ext s a b
  obtain ⟨i,t,rfl⟩ := hcover s
  have ht : block (fun i => f (ξ i t)) = block (fun i => g (ξ i t)) :=
    DFunLike.congr_fun h t
  exact congrFun (congrFun (congrFun (block_injective ht) i) a) b


omit instDecidableEqκ in
lemma interpolate_zero.{contextLevel1, contextLevel2}
    {κ : Type contextLevel1}
    {ν : Type contextLevel2}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ν]
    [DecidableEq ν]
    (e₀ e₁ : κ ≃ ν) (a : Mat κ) :
    interpolate e₀ e₁ 0 a = CStarMatrix.reindexₐ ℂ ℂ e₀ a := by
  simp only [interpolate, StarAlgEquiv.trans_apply, Path.source,
    MatrixPermutationPath.perm_one]
  simp

omit instDecidableEqκ in
lemma interpolate_one.{contextLevel1, contextLevel2}
    {κ : Type contextLevel1}
    {ν : Type contextLevel2}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ν]
    [DecidableEq ν]
    (e₀ e₁ : κ ≃ ν) (a : Mat κ) :
    interpolate e₀ e₁ 1 a = CStarMatrix.reindexₐ ℂ ℂ e₁ a := by
  simp only [interpolate, StarAlgEquiv.trans_apply, Path.target,
    MatrixPermutationPath.perm_conjugation]
  ext i j
  change a (e₀.symm ((e₀.symm.trans e₁).symm i))
    (e₀.symm ((e₀.symm.trans e₁).symm j)) = a (e₁.symm i) (e₁.symm j)
  simp


omit instDecidableEqκ in
lemma interpolate_continuous.{contextLevel1, contextLevel2}
    {κ : Type contextLevel1}
    {ν : Type contextLevel2}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ν]
    [DecidableEq ν]
    (e₀ e₁ : κ ≃ ν) (f : unitInterval → Mat κ)
    (hf : Continuous f) : Continuous (fun t => interpolate e₀ e₁ t (f t)) := by
  change Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : Mat ν) *
    (CStarMatrix.reindexₐ ℂ ℂ e₀) (f t) *
    star ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : Mat ν))
  have hu : Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : Mat ν)) :=
    continuous_subtype_val.comp (Path.continuous _)
  exact (hu.mul ((map_continuous (CStarMatrix.reindexₐ ℂ ℂ e₀)).comp hf)).mul hu.star

end KirchbergRordam.MatrixDiagonalPath


namespace KirchbergRordam.MatrixBlockReindex
open MatrixTensor (leftMatrix rightMatrix)
open MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix Kronecker
variable {P Q L R S T : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T]


@[simp] lemma sumBlock_ll (a : Mat P) (b : Mat Q) (i j : P) :
    sumBlock (a,b) (Sum.inl i) (Sum.inl j) = a i j := rfl
@[simp] lemma sumBlock_lr (a : Mat P) (b : Mat Q) (i : P) (j : Q) :
    sumBlock (a,b) (Sum.inl i) (Sum.inr j) = 0 := rfl
@[simp] lemma sumBlock_rl (a : Mat P) (b : Mat Q) (i : Q) (j : P) :
    sumBlock (a,b) (Sum.inr i) (Sum.inl j) = 0 := rfl
@[simp] lemma sumBlock_rr (a : Mat P) (b : Mat Q) (i j : Q) :
    sumBlock (a,b) (Sum.inr i) (Sum.inr j) = b i j := rfl

@[simp] lemma left_apply (a : Mat P) (i j : P) (k l : Q) :
    leftMatrix a (i,k) (j,l) = a i j * if k=l then 1 else 0 := by
  change (Matrix.kronecker (CStarMatrix.ofMatrix.symm a) (1 : Matrix Q Q ℂ)) (i,k) (j,l)=_
  simp [Matrix.one_apply]
@[simp] lemma right_apply (a : Mat Q) (i j : P) (k l : Q) :
    rightMatrix a (i,k) (j,l) = (if i=j then 1 else 0) * a k l := by
  change (Matrix.kronecker (1 : Matrix P P ℂ) (CStarMatrix.ofMatrix.symm a)) (i,k) (j,l)=_
  simp [Matrix.one_apply]


def repackLeft (hL : Q × L ≃ T) (hR : R ≃ S × T) :
    (P × Q) × (L ⊕ R) ≃ (P ⊕ ((P × Q) × S)) × T :=
  (Equiv.prodSumDistrib (P × Q) L R).trans
    ((Equiv.sumCongr
      ((Equiv.prodAssoc P Q L).trans (Equiv.prodCongr (Equiv.refl P) hL))
      ((Equiv.prodCongr (Equiv.refl (P × Q)) hR).trans
        (Equiv.prodAssoc (P × Q) S T).symm)).trans
      (Equiv.sumProdDistrib P ((P × Q) × S) T).symm)

omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT in
@[simp] lemma repackLeft_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    (hL : Q × L ≃ T) (hR : R ≃ S × T)
    (i : P) (j : Q) (l : L) :
    repackLeft (P:=P) hL hR ((i,j),Sum.inl l) = (Sum.inl i, hL (j,l)) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT in
@[simp] lemma repackLeft_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    (hL : Q × L ≃ T) (hR : R ≃ S × T)
    (i : P) (j : Q) (r : R) :
    repackLeft (P:=P) hL hR ((i,j),Sum.inr r) =
      (Sum.inr ((i,j),(hR r).1), (hR r).2) := rfl

lemma repackLeft_entry (hL : Q × L ≃ T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => leftMatrix (κ:=Q) a) (fun _ : R => m)) x y =
      leftMatrix (sumBlock (a,block (fun _ : S => m)))
        (repackLeft hL hR x) (repackLeft hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases hj : j=j' <;> by_cases hl : l=l' <;>
      simp [block_apply, hj, hl, hL.injective.eq_iff, Prod.ext_iff]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1 ≠ (hR r').1 ∨ (hR r).2 ≠ (hR r').2 := by
        by_contra h
        push Not at h
        exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with hs|ht
      · simp [block_apply, hr, hs]
      · simp [block_apply, hr, ht]

lemma repackLeft_matrix (hL : Q × L ≃ T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackLeft hL hR)
      (block (Sum.elim (fun _ : L => leftMatrix (κ:=Q) a) (fun _ : R => m))) =
        leftMatrix (sumBlock (a,block (fun _ : S => m))) := by
  ext x y
  exact repackLeft_entry hL hR a m ((repackLeft hL hR).symm x)
    ((repackLeft hL hR).symm y) |>.trans (by simp)


def repackRight (hL : P × L ≃ T) (hR : R ≃ T × S) :
    (P × Q) × (L ⊕ R) ≃ T × (Q ⊕ ((P × Q) × S)) where
  toFun x := match x.2 with
    | .inl l => (hL (x.1.1,l), .inl x.1.2)
    | .inr r => ((hR r).1, .inr (x.1,(hR r).2))
  invFun x := match x.2 with
    | .inl j => (((hL.symm x.1).1,j), .inl (hL.symm x.1).2)
    | .inr y => (y.1, .inr (hR.symm (x.1,y.2)))
  left_inv x := by rcases x with ⟨⟨i,j⟩,l|r⟩ <;> simp
  right_inv x := by rcases x with ⟨t,j|⟨ij,s⟩⟩ <;> simp

omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT in
@[simp] lemma repackRight_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    (hL : P × L ≃ T) (hR : R ≃ T × S)
    (i : P) (j : Q) (l : L) :
    repackRight (Q:=Q) hL hR ((i,j),Sum.inl l) = (hL (i,l),Sum.inl j) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT in
@[simp] lemma repackRight_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    (hL : P × L ≃ T) (hR : R ≃ T × S)
    (i : P) (j : Q) (r : R) :
    repackRight (Q:=Q) hL hR ((i,j),Sum.inr r) =
      ((hR r).1,Sum.inr ((i,j),(hR r).2)) := rfl

lemma repackRight_entry (hL : P × L ≃ T) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => rightMatrix (ι:=P) a) (fun _ : R => m)) x y =
      rightMatrix (sumBlock (a,block (fun _ : S => m)))
        (repackRight hL hR x) (repackRight hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases hi : i=i' <;> by_cases hl : l=l' <;>
      simp [block_apply, hi, hl, hL.injective.eq_iff, Prod.ext_iff]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1 ≠ (hR r').1 ∨ (hR r).2 ≠ (hR r').2 := by
        by_contra h
        push Not at h
        exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with ht|hs
      · simp [block_apply, hr, ht]
      · simp [block_apply, hr, hs]

lemma repackRight_matrix (hL : P × L ≃ T) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackRight hL hR)
      (block (Sum.elim (fun _ : L => rightMatrix (ι:=P) a) (fun _ : R => m))) =
        rightMatrix (sumBlock (a,block (fun _ : S => m))) := by
  ext x y
  exact repackRight_entry hL hR a m ((repackRight hL hR).symm x)
    ((repackRight hL hR).symm y) |>.trans (by simp)

end KirchbergRordam.MatrixBlockReindex
end

end OAI
