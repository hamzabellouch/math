import OAI.Probability.CubeShuffle.ModifiedKernel
import OAI.Probability.CubeShuffle.Generation
import OAI.RepresentationTheory.FiniteUnitary.CommutingBlocks
import OAI.RepresentationTheory.FiniteUnitary.Fourier

namespace OAI

namespace CubeShuffle.ParallelBlocks
open scoped BigOperators Classical
variable {B X : Type*}

def lift : (B → Equiv.Perm X) →* Equiv.Perm (B × X) where
  toFun p :=
    { toFun := fun x => (x.1,p x.1 x.2)
      invFun := fun x => (x.1,(p x.1).symm x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma lift_apply (p : B → Equiv.Perm X) (x : B × X) : lift p x=(x.1,p x.1 x.2) := rfl

noncomputable def injection (b : B) : Equiv.Perm X →* Equiv.Perm (B × X) :=
  lift.comp
    { toFun := fun p c => if c=b then p else 1
      map_one' := by funext c; simp
      map_mul' := by intro p q; funext c; by_cases h : c=b <;> simp [h] }

@[simp] lemma injection_apply (b : B) (p : Equiv.Perm X) (x : B × X) :
    injection b p x=(x.1,if x.1=b then p x.2 else x.2) := by
  simp only [injection,MonoidHom.comp_apply,lift_apply]
  by_cases h : x.1=b <;> simp [h]

lemma injection_commute {b c : B} (h : b≠c) (p q : Equiv.Perm X) :
    Commute (injection b p) (injection c q) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,injection_apply]
  by_cases hb : x.1=b <;> by_cases hc : x.1=c <;> simp_all

variable [Fintype B]

lemma lift_product (p : B → Equiv.Perm X) :
    lift p=Finset.univ.noncommProd (fun b => injection b (p b))
      (fun _ _ _ _ h => injection_commute h _ _) := by
  have he (s : Finset B) (x : B × X) :
      s.noncommProd (fun b => injection b (p b))
        (fun _ _ _ _ h => injection_commute h _ _) x=
          (x.1,if x.1∈s then p x.1 x.2 else x.2) := by
    induction s using Finset.induction_on with
    | empty =>
      have hz : Finset.noncommProd (∅ : Finset B) (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=1 := Finset.noncommProd_empty _ _
      rw [hz]; simp
    | @insert a s ha ih =>
      have hz : (insert a s).noncommProd (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=injection a (p a)*
          s.noncommProd (fun b => injection b (p b))
            (fun _ _ _ _ h => injection_commute h _ _) :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [hz,Equiv.Perm.mul_apply,ih,injection_apply]
      by_cases h : x.1=a
      · subst a; simp [ha]
      · simp [h]
  apply Equiv.ext
  intro x
  rw [he]
  simp

end CubeShuffle.ParallelBlocks
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

variable {G H : Type*} [Group G] [Group H]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_uniform_absorb [Fintype G] [Nonempty Ω]
    (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P*uniformOperator ρ=uniformOperator ρ := by
  rw [sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end CubeShuffle.UnitaryFinite
namespace CubeShuffle.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X Ω : Type*} [Fintype B] [DecidableEq B] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype B] [DecidableEq B] in
lemma local_average_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b))
      (sampleOperator (ρ.comp (injection c)) (P c)) := by
  by_cases h : b=c
  · subst c; exact Commute.refl _
  · rw [sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

lemma sampleOperator_parallel (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) :
    sampleOperator ρ (fun ω : B → Ω => lift (fun b => P b (ω b)))=
      CommutingBlocks.blocks (fun b => sampleOperator (ρ.comp (injection b)) (P b))
        (local_average_commute ρ P) := by
  let A (b : B) (w : Ω) := continuousRepresentation ρ (injection b (P b w))
  have hc : ∀ ω : B → Ω, Pairwise fun b c => Commute (A b (ω b)) (A c (ω c)) := by
    intro ω b c h
    exact (injection_commute h _ _).map (continuousRepresentation ρ)
  have havg : Pairwise fun b c => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A b w)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A c w) := by
    intro b c _
    exact local_average_commute ρ P b c
  have he (ω : B → Ω) : continuousRepresentation ρ (lift (fun b => P b (ω b)))=
      Finset.univ.noncommProd (fun b => A b (ω b)) (fun _ _ _ _ h => hc ω h) := by
    rw [lift_product]
    exact Finset.map_noncommProd _ _ _ (continuousRepresentation ρ)
  unfold sampleOperator
  simp_rw [he]
  exact (FiniteAverage.ordered_average A hc havg).symm

end CubeShuffle.ParallelBlocks
namespace CubeShuffle
open scoped BigOperators Classical

noncomputable def splitPerm (r L : ℕ) : Equiv.Perm (Card (L+r)) ≃* Equiv.Perm (Card r × Card L) :=
  (cardSplit r L).permCongrHom

noncomputable def outerPerm (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) :
    Equiv.Perm (Card r × Card L) :=
  (Equiv.prodComm (Card L) (Card r)).permCongrHom
    (ParallelBlocks.lift (fun x => butterflyPerm r (decodeButterfly r (fun i => hi (x,i)))))

lemma outerPerm_apply (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) (x : Card r × Card L) :
    outerPerm r L hi x=(butterflyPerm r (decodeButterfly r (fun i => hi (x.2,i))) x.1,x.2) := rfl

lemma splitPerm_butterfly (r L : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi)))=
      outerPerm r L hi*ParallelBlocks.lift
        (fun b => butterflyPerm L (decodeButterfly L (fun i => lo (b,i)))) := by
  apply Equiv.ext
  intro x
  change cardSplit r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi))
    ((cardSplit r L).symm x))=_
  rw [butterfly_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryTree_node_raw (L r : ℕ) (U : Card (r+1) → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r+1) → Bool) :
    boundaryTree L (r+1) U X=InputTree.node (fun y => X (Sum.inl y))
      (fun b => boundaryTree L r (fun u => U (Fin.cons b u)) (fun i => X (Sum.inr (b,i)))) := by
  conv_lhs => unfold boundaryTree
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryOutput_node_raw (L r : ℕ) (Y : SwitchIndex (L+r+1) → Bool) (b : Card (r+1)) :
    boundaryOutput L (r+1) Y b=
      boundaryOutput L r (fun i => Y (Sum.inr (b 0,i))) (Fin.tail b) := by
  conv_lhs => unfold boundaryOutput
  cases b 0 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryTree_split (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) (x : Card (L+r)) :
    cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm x)=
      let y := cardSplit r L x
      let z := U y.1 y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex L → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card L × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    let U' : Card r → Equiv.Perm (Card L) := fun b => U (Fin.cons (x 0) b)
    have hh := ih U' lo' hi' (Fin.tail x)
    let u := (boundaryTree L r U' (assembleBits r L lo' hi')).perm (Fin.tail x)
    let y := cardSplit r L (Fin.tail x)
    let z := U' y.1 y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r L u=(w,z) at hh
    rw [boundaryTree_node_raw]
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r L u).2,Sum.inl (cardSplit r L u).1)))
      ((cardSplit r L u).1) : Card (r+1)),(cardSplit r L u).2)=
        ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

lemma splitPerm_boundaryTree (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (boundaryTree L r U (assembleBits r L lo hi)).perm=
      outerPerm r L hi*ParallelBlocks.lift U := by
  apply Equiv.ext
  intro x
  change cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm
    ((cardSplit r L).symm x))=_
  rw [boundaryTree_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryOutput_split (L r : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) (b : Card r) :
    boundaryOutput L r (assembleBits r L lo hi) b=
      butterflyPerm L (decodeButterfly L (fun i => lo (b,i))) := by
  induction r with
  | zero =>
    rw [Subsingleton.elim b (fun j => Fin.elim0 j)]
    rfl
  | succ r ih =>
    rw [boundaryOutput_node_raw]
    change boundaryOutput L r (assembleBits r L (fun j => lo (Fin.cons (b 0) j.1,j.2))
      (fun j => hi (j.1,Sum.inr (b 0,j.2)))) (Fin.tail b)=_
    rw [ih]
    simp only [Fin.cons_self_tail]

end CubeShuffle
namespace CubeShuffle
open scoped BigOperators Classical

abbrev OuterCoins (r L : ℕ) := Card L × SwitchIndex r → Bool
abbrev LocalCoins (L : ℕ) := SwitchIndex L → Bool

def parallelSplitCoinEquiv (r L : ℕ) :
    ((Card r → LocalCoins L) × OuterCoins r L) ≃ LocalCoins (L+r) :=
  (Equiv.prodCongr (Equiv.curry (Card r) (SwitchIndex L) Bool).symm (Equiv.refl _)).trans
    (splitCoinEquiv r L)

lemma parallelSplitCoinEquiv_apply (r L : ℕ) (c : Card r → LocalCoins L) (h : OuterCoins r L) :
    parallelSplitCoinEquiv r L (c,h)=assembleBits r L (fun x => c x.1 x.2) h := by
  exact splitCoinEquiv_apply _ _ _ _

def pairAssembleEquiv (B C H : Type*) :
    ((H × (B → C × C)) × H) ≃ (((B → C) × H) × ((B → C) × H)) where
  toFun w := (((fun b => (w.1.2 b).1),w.1.1),((fun b => (w.1.2 b).2),w.2))
  invFun w := ((w.1.2,fun b => (w.1.1 b,w.2.1 b)),w.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def palindromeStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) ≃ BenesCoins (L+r) :=
  (pairAssembleEquiv _ _ _).trans
    (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L))

lemma palindromeStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    palindromeStageEquiv r L w=
      (assembleBits r L (fun x => (w.1.2 x.1).1 x.2) w.1.1,
       assembleBits r L (fun x => (w.1.2 x.1).2 x.2) w.2) := by
  simp only [palindromeStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,pairAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,parallelSplitCoinEquiv_apply]

def modifiedAssembleEquiv (B C H U : Type*) :
    ((H × (B → U × (C × C))) × H) ≃ (B → U) × (((B → C) × H) × ((B → C) × H)) where
  toFun w := ((fun b => (w.1.2 b).1),
    (((fun b => (w.1.2 b).2.1),w.1.1),((fun b => (w.1.2 b).2.2),w.2)))
  invFun w := ((w.2.1.2,fun b => (w.1 b,(w.2.1.1 b,w.2.2.1 b))),w.2.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def modifiedStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) ≃
      ModifiedCoins L r :=
  (modifiedAssembleEquiv _ _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L)))

lemma modifiedStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    modifiedStageEquiv r L w=
      ((fun b => (w.1.2 b).1),
       (assembleBits r L (fun x => (w.1.2 x.1).2.1 x.2) w.1.1,
        assembleBits r L (fun x => (w.1.2 x.1).2.2 x.2) w.2)) := by
  simp only [modifiedStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,modifiedAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,Equiv.refl_apply,parallelSplitCoinEquiv_apply]

lemma palindrome_stage (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (palindromePerm (L+r) (palindromeStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [palindromeStageEquiv_apply]
  change splitPerm r L (_*_⁻¹)=_
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_butterfly,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  rfl

noncomputable def localModifiedPerm (L : ℕ) (e : Bool)
    (w : Equiv.Perm (Card L) × BenesCoins L) : Equiv.Perm (Card L) :=
  if e then 1 else butterflyPerm L (decodeButterfly L w.2.1)*w.1⁻¹

lemma modified_stage (r L : ℕ) (E : Finset (Card r))
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (modifiedPerm L r E (modifiedStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [modifiedStageEquiv_apply]
  unfold modifiedPerm modifiedInputTree
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_boundaryTree,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  congr 2
  apply congrArg ParallelBlocks.lift
  funext b
  simp only [Pi.mul_apply,Pi.inv_apply,modifiedBoundary,boundaryOutput_split,localModifiedPerm]
  by_cases h : b∈E <;> simp [h]

end CubeShuffle
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_sandwich (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun w : (Ω × Ξ) × Ω => P w.1.1*Q w.1.2*(P w.2)⁻¹)=
      sampleOperator ρ P*sampleOperator ρ Q*(sampleOperator ρ P).adjoint := by
  rw [sampleOperator_prod ρ (fun w : Ω × Ξ => P w.1*Q w.2) (fun w : Ω => (P w)⁻¹),
    sampleOperator_prod ρ P Q,sampleOperator_inv ρ hρ]

lemma localModified_average (L : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card L)) V) (e : Bool) :
    sampleOperator ρ (localModifiedPerm L e)=if e then 1 else uniformOperator ρ := by
  cases e
  · simp only [Bool.false_eq_true,ite_false]
    rw [←sampleOperator_equiv ρ _ (Equiv.prodComm _ _)]
    exact sampleOperator_uniform_mul ρ (fun w : BenesCoins L => butterflyPerm L (decodeButterfly L w.1))
  · simp only [ite_true]
    exact sampleOperator_one ρ

end CubeShuffle.UnitaryFinite

namespace CubeShuffle
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleOperator_palindrome_stage (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := funext (palindrome_stage r L)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) (palindromeStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b))))

lemma sampleOperator_modified_stage (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift
        (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*(outerPerm r L w.2)⁻¹ :=
    funext (modified_stage r L E)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) (modifiedStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b))))

end CubeShuffle
namespace CubeShuffle.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def retain (P : ι → V →L[ℂ] V) (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1 else P i

omit [CompleteSpace V] [Fintype ι] in
lemma retain_commute (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j))
    (E : Finset ι) (i j : ι) : Commute (retain P E i) (retain P E j) := by
  unfold retain
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.one_right _ | exact hP _ _

omit [CompleteSpace V] in
lemma blocks_retain (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j)) (E : Finset ι) :
    blocks (retain P E) (retain_commute P hP E)=coarse P hP E := by
  have hs : E∪Eᶜ=(Finset.univ : Finset ι) := Finset.union_compl E
  have hh := Finset.noncommProd_union_of_disjoint (s := E) (t := Eᶜ) disjoint_compl_right
    (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)
  simp only [hs] at hh
  change blocks (retain P E) (retain_commute P hP E)=_ at hh
  rw [hh]
  have he : E.noncommProd (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)=1 := by
    exact (Finset.noncommProd_eq_pow_card E (retain P E)
      (fun i _ j _ _ => retain_commute P hP E i j) 1 (by intro i hi; exact ite_eq_left hi)).trans (one_pow _)
  rw [he,one_mul]
  apply Finset.noncommProd_congr rfl
  intro i hi
  exact ite_eq_right (Finset.mem_compl.mp hi)

end CubeShuffle.CommutingBlocks

namespace CubeShuffle.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def centralProjection (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b : B) : V →L[ℂ] V :=
  uniformOperator (ρ.comp (injection b))

omit [Fintype B] in
lemma centralProjection_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b c : B) :
    Commute (centralProjection ρ b) (centralProjection ρ c) := by
  simpa only [centralProjection,sampleOperator_uniform] using
    local_average_commute ρ (fun _ => id : B → Equiv.Perm X → Equiv.Perm X) b c

omit [Fintype B] in
lemma local_central_commute {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b)) (centralProjection ρ c) := by
  by_cases h : b=c
  · subst c
    change _*uniformOperator _=uniformOperator _*_
    rw [sampleOperator_uniform_absorb,sampleOperator_weighted,weighted_uniform_right,sampleLaw_sum,one_smul]
  · unfold centralProjection
    rw [←sampleOperator_uniform,sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

end CubeShuffle.ParallelBlocks
namespace CubeShuffle
open scoped BigOperators Classical
open UnitaryFinite ParallelBlocks CommutingBlocks
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma modified_central_average (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) :
    sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
      lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))=
      coarse (centralProjection ρ) (centralProjection_commute ρ) E := by
  rw [sampleOperator_parallel ρ (fun b => localModifiedPerm L (decide (b∈E))),←blocks_retain]
  apply Finset.noncommProd_congr rfl
  · intro b _
    rw [localModified_average]
    simp only [retain,centralProjection,decide_eq_true_eq]
  · intro b _ c _ _
    exact local_average_commute ρ (fun b => localModifiedPerm L (decide (b∈E))) b c

lemma central_local_gap (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (b : Card r) :
    ‖sampleOperator (ρ.comp (injection b)) (palindromePerm L)*(1-centralProjection ρ b)‖≤blockGap L := by
  change ‖sampleOperator _ _*(1-uniformOperator _)‖≤_
  rw [mul_sub,mul_one,sampleOperator_uniform_absorb,sampleOperator_weighted]
  exact palindrome_off_invariants_gap L _ (unitary_comp ρ hρ _)

lemma central_blocks_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ)
    (B : V →L[ℂ] V) (hB0 : ‖B‖≤1) (n : ℕ) :
    ‖B*blocks (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
      (local_average_commute ρ (fun _ => palindromePerm L))*B.adjoint‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖B*coarse (centralProjection ρ) (centralProjection_commute ρ) E*B.adjoint‖ else 0 := by
  have hB : ‖B.adjoint‖≤1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hB0
  have h := blocks_exception_bound (centralProjection ρ) (centralProjection_commute ρ)
    (fun b => uniformOperator_projection (ρ.comp (injection b)) (unitary_comp ρ hρ _))
    (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
    (local_average_commute ρ (fun _ => palindromePerm L))
    (local_central_commute ρ (fun _ => palindromePerm L))
    (fun b => sampleOperator_norm_le (ρ.comp (injection b)) (unitary_comp ρ hρ _) (palindromePerm L))
    (blockGap L) (blockGap_pos L).le (blockGap_lt_one L).le (central_local_gap r L ρ hρ)
    B.adjoint hB n
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

/-- The network comparison at a fixed central size is proved for the actual
fair-coin operators. No spectral/PSD comparison hypothesis is inserted. -/
theorem palindrome_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)‖ else 0 := by
  rw [sampleOperator_palindrome_stage r L ρ hρ]
  rw [sampleOperator_parallel ρ (fun _ => palindromePerm L)]
  apply (central_blocks_exception_bound r L ρ hρ (sampleOperator ρ (outerPerm r L))
    (sampleOperator_norm_le ρ hρ _) n).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro E _
  split_ifs
  · rw [sampleOperator_modified_stage r L E ρ hρ,modified_central_average]
  · rfl

end CubeShuffle

end OAI
