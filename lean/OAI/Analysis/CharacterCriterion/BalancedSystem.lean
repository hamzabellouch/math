import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.MatrixPaths

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


namespace KirchbergRordam.BalancedDropMultiplicity

def upper (p : ℕ) : ℕ := p*p
def lower (p : ℕ) : ℕ := p*p-p+1
def middle (p : ℕ) : ℕ := upper p * lower p - upper p - lower p

def next (p : ℕ) : ℕ := p*p*p

lemma lower_eq {p : ℕ} (hp : 2 ≤ p) : lower p + p = p*p + 1 := by
  have : p ≤ p*p := by nlinarith
  unfold lower; omega
lemma upper_pos {p : ℕ} (hp : 2 ≤ p) : 0 < upper p := by unfold upper; positivity
lemma lower_pos {p : ℕ} (hp : 2 ≤ p) : 0 < lower p := by
  have lowerIdentity := lower_eq hp
  nlinarith
lemma lower_two {p : ℕ} (hp : 2 ≤ p) : 2 ≤ lower p := by
  have h := lower_eq hp
  nlinarith
lemma sum_le_product {p : ℕ} (hp : 2 ≤ p) : upper p + lower p ≤ upper p * lower p := by
  have ha : 2 ≤ upper p := by unfold upper; nlinarith
  have hb := lower_two hp
  nlinarith
lemma total {p : ℕ} (hp : 2 ≤ p) : lower p + upper p + middle p = upper p * lower p := by
  have := sum_le_product hp
  unfold middle; omega
lemma next_two {p : ℕ} (hp : 2 ≤ p) : 2 ≤ next p := by unfold next; nlinarith
lemma mul_upper (p : ℕ) : p * upper p = next p := by unfold upper next; ring
lemma mul_lower {p : ℕ} (hp : 2 ≤ p) : (p+1) * lower p = next p+1 := by
  have := lower_eq hp
  unfold next; nlinarith
lemma at_zero {p : ℕ} (hp : 2 ≤ p) : upper p + middle p = (p-1)*(next p+1) := by
  have ht := total hp
  have hl := mul_lower hp
  have he : upper p * lower p = lower p + (p-1)*(next p+1) := by
    rw [← hl]
    have hp' : p-1+1=p := by omega
    unfold upper; nlinarith
  omega
lemma at_one {p : ℕ} (hp : 2 ≤ p) : lower p + middle p = next p*(p-1) := by
  have ht := total hp
  have hl := lower_eq hp
  have he : upper p * lower p = upper p + next p*(p-1) := by
    have hp' : p-1+1=p := by omega
    have hl' : lower p = p*(p-1)+1 := by nlinarith
    rw [hl']
    unfold upper next
    ring
  omega
lemma zero_space {p : ℕ} (hp : 2 ≤ p) : p + p*(p+1)*(p-1) = next p := by
  have hp' : p-1+1=p := by omega
  unfold next; nlinarith
lemma one_space {p : ℕ} (hp : 2 ≤ p) : (p+1) + p*(p+1)*(p-1) = next p+1 := by
  have := zero_space hp
  omega

def stage : ℕ → ℕ
  | 0 => 2
  | n+1 => next (stage n)
@[simp] lemma stage_zero : stage 0 = 2 := rfl
@[simp] lemma stage_succ (n : ℕ) : stage (n+1) = next (stage n) :=
  rfl
lemma stage_two (n : ℕ) : 2 ≤ stage n := by
  induction n with
  | zero => simp
  | succ n ih => rw [stage_succ]; exact next_two ih
lemma stage_coprime (n : ℕ) : (stage n).Coprime (stage n+1) := by simp

end KirchbergRordam.BalancedDropMultiplicity

namespace KirchbergRordam.MatrixBlockReindex
open MatrixDiagonalPath
open MatrixTensor (leftMatrix rightMatrix)
open scoped ComplexOrder CStarAlgebra Matrix
variable {P Q R S : Type*} [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [DecidableEq R] [DecidableEq S]
omit instDecidableEqP instDecidableEqQ in
lemma reindex_trans.{contextLevel1, contextLevel2}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    [Fintype P]
    [Fintype Q]
    [DecidableEq P]
    [DecidableEq Q]
    {T : Type*} [Fintype T] [DecidableEq T]
    (e : P ≃ Q) (f : Q ≃ T) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
      CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl
lemma reindex_block (e : P ≃ Q) (a : P → Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl R) e) (block a) =
      block (fun i => a (e.symm i)) := by
  ext i j
  rcases i with ⟨r,p⟩; rcases j with ⟨s,q⟩
  change (if e.symm p=e.symm q then a (e.symm p) r s else 0) =
    (if p=q then a (e.symm p) r s else 0)
  simp only [e.symm.injective.eq_iff]
lemma reindex_left (e : P ≃ Q) (f : R ≃ S) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (leftMatrix (κ:=R) a) =
      leftMatrix (κ:=S) (CStarMatrix.reindexₐ ℂ ℂ e a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change leftMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [left_apply, f.symm.injective.eq_iff]
  rfl
lemma reindex_right (e : P ≃ Q) (f : R ≃ S) (a : Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (rightMatrix (ι:=P) a) =
      rightMatrix (ι:=Q) (CStarMatrix.reindexₐ ℂ ℂ f a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change rightMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [right_apply, e.symm.injective.eq_iff]
  rfl
end KirchbergRordam.MatrixBlockReindex

namespace KirchbergRordam.BalancedDropSystem
open MatrixDiagonalPath
open MatrixTensor (leftMatrix rightMatrix)
open MatrixBlockReindex
open BalancedDropMultiplicity
open scoped ComplexOrder CStarAlgebra Matrix

abbrev P (p : ℕ) := Fin p
abbrev Q (p : ℕ) := Fin (p+1)
abbrev Low (p : ℕ) := Fin (lower p)
abbrev High (p : ℕ) := Fin (upper p)
abbrev Mid (p : ℕ) := Fin (middle p)
abbrev Slot (p : ℕ) := Low p ⊕ (High p ⊕ Mid p)
abbrev Index (p : ℕ) := (P p × Q p) × Slot p
abbrev ZeroSpace (p : ℕ) := P p ⊕ ((P p × Q p) × Fin (p-1))
abbrev OneSpace (p : ℕ) := Q p ⊕ ((P p × Q p) × Fin (p-1))


def zeroLow (p : ℕ) (hp : 2 ≤ p) : Q p × Low p ≃ Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_prod, Fintype.card_fin] using mul_lower hp)
def zeroMid (p : ℕ) (hp : 2 ≤ p) : High p ⊕ Mid p ≃ Fin (p-1) × Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using at_zero hp)
def zeroOuter (p : ℕ) (hp : 2 ≤ p) : ZeroSpace p ≃ P (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using zero_space hp)
def oneLow (p : ℕ) : P p × High p ≃ P (next p) :=
  cardEquiv (by simpa only [Fintype.card_prod, Fintype.card_fin] using mul_upper p)
def oneMid (p : ℕ) (hp : 2 ≤ p) : Low p ⊕ Mid p ≃ P (next p) × Fin (p-1) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using at_one hp)
def oneOuter (p : ℕ) (hp : 2 ≤ p) : OneSpace p ≃ Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using one_space hp)


def slotSwap (p : ℕ) : Slot p ≃ High p ⊕ (Low p ⊕ Mid p) where
  toFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  invFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  left_inv x := by rcases x with x|x|x <;> rfl
  right_inv x := by rcases x with x|x|x <;> rfl

def zeroReindex (p : ℕ) (hp : 2 ≤ p) : Index p ≃ P (next p) × Q (next p) :=
  (repackLeft (zeroLow p hp) (zeroMid p hp)).trans
    (Equiv.prodCongr (zeroOuter p hp) (Equiv.refl _))
def oneReindex (p : ℕ) (hp : 2 ≤ p) : Index p ≃ P (next p) × Q (next p) :=
  (Equiv.prodCongr (Equiv.refl _) (slotSwap p)).trans
    ((repackRight (oneLow p) (oneMid p hp)).trans
      (Equiv.prodCongr (Equiv.refl _) (oneOuter p hp)))

lemma half_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

def eigenpath (p : ℕ) : Slot p → C(unitInterval, unitInterval) :=
  Sum.elim (fun _ => lowerPath) (Sum.elim (fun _ => upperPath) (fun _ => ContinuousMap.const _ half))

@[simp] lemma lower_zero : lowerPath 0 = 0 := by
  apply Subtype.ext
  change (0 : ℝ) / 2 = 0
  norm_num
@[simp] lemma lower_one : lowerPath 1 = half := by
  apply Subtype.ext
  change (1 : ℝ) / 2 = (1 : ℝ) / 2
  rfl
@[simp] lemma upper_zero : upperPath 0 = half := by
  apply Subtype.ext
  change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
  rw [zero_add]
@[simp] lemma upper_one : upperPath 1 = 1 := by
  apply Subtype.ext
  change ((1 : ℝ) + 1) / 2 = 1
  norm_num

lemma eigen_cover (p : ℕ) (hp : 2 ≤ p) (s : unitInterval) :
    ∃ i t, eigenpath p i t = s := by
  by_cases hs : (s:ℝ) ≤ 1/2
  · refine ⟨.inl ⟨0,lower_pos hp⟩, ⟨2*s,by constructor <;> linarith [s.property.1]⟩, ?_⟩
    apply Subtype.ext
    change 2*(s:ℝ)/2=(s:ℝ)
    ring
  · refine ⟨.inr (.inl ⟨0,upper_pos hp⟩), ⟨2*s-1,by constructor <;> linarith [s.property.2]⟩, ?_⟩
    apply Subtype.ext
    change ((2*(s:ℝ)-1)+1)/2=(s:ℝ)
    ring


def fiberMap (p : ℕ) (hp : 2 ≤ p) (t : unitInterval) :
    C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)) →⋆ₐ[ℂ]
      PrimeDimensionDrop.Fiber (next p) (next p+1) :=
  (interpolate (zeroReindex p hp) (oneReindex p hp) t).toStarAlgHom.comp
    (evaluationBlock (eigenpath p) t)


def rawStep (p : ℕ) (hp : 2 ≤ p) :
    C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)) →⋆ₐ[ℂ]
      C(unitInterval, PrimeDimensionDrop.Fiber (next p) (next p+1)) where
  toFun f := ⟨fun t => fiberMap p hp t f,
    interpolate_continuous _ _ _ (evaluationBlock_continuous _ _)⟩
  map_zero' := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_zero
  map_one' := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_one
  map_add' f g := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_add f g
  map_mul' f g := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_mul f g
  commutes' z := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).commutes z
  map_star' f := by apply ContinuousMap.ext; intro t; exact map_star (fiberMap p hp t) f

@[simp] lemma rawStep_apply (p : ℕ) (hp : 2 ≤ p) (f) (t : unitInterval) :
    rawStep p hp f t = interpolate (zeroReindex p hp) (oneReindex p hp) t
      (evaluationBlock (eigenpath p) t f) := rfl

lemma zero_eval (p : ℕ) (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (a : Mat (P p)) (ha : leftMatrix a = f 0) :
    evaluationBlock (eigenpath p) 0 f =
      block (Sum.elim (fun _ : Low p => leftMatrix (κ:=Q p) a)
        (fun _ : High p ⊕ Mid p => f half)) := by
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [eigenpath,ha]

lemma one_eval (p : ℕ) (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (b : Mat (Q p)) (hb : rightMatrix b = f 1) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (P p × Q p)) (slotSwap p))
      (evaluationBlock (eigenpath p) 1 f) =
      block (Sum.elim (fun _ : High p => rightMatrix (ι:=P p) b)
        (fun _ : Low p ⊕ Mid p => f half)) := by
  change CStarMatrix.reindexₐ ℂ ℂ _ (block _) = _
  rw [reindex_block]
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [slotSwap,eigenpath,hb]

lemma rawStep_zero (p : ℕ) (hp : 2 ≤ p)
    (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (a : Mat (P p)) (ha : leftMatrix a = f 0) :
    rawStep p hp f 0 = leftMatrix (κ := Q (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter p hp)
        (sumBlock (a,block (fun _ : Fin (p-1) => f half)))) := by
  rw [rawStep_apply,interpolate_zero,zero_eval p f a ha]
  unfold zeroReindex
  rw [reindex_trans,repackLeft_matrix,reindex_left]

lemma rawStep_one (p : ℕ) (hp : 2 ≤ p)
    (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (b : Mat (Q p)) (hb : rightMatrix b = f 1) :
    rawStep p hp f 1 = rightMatrix (ι := P (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (oneOuter p hp)
        (sumBlock (b,block (fun _ : Fin (p-1) => f half)))) := by
  rw [rawStep_apply,interpolate_one]
  unfold oneReindex
  rw [reindex_trans,one_eval p f b hb,reindex_trans,repackRight_matrix,reindex_right]


def step (p : ℕ) (hp : 2 ≤ p) : PrimeDimensionDrop.Algebra p (p+1) →⋆ₐ[ℂ]
    PrimeDimensionDrop.Algebra (next p) (next p+1) where
  toFun f := ⟨rawStep p hp f.val, by
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := f.property
    exact ⟨⟨_, (rawStep_zero p hp f.val a ha).symm⟩,
      ⟨_, (rawStep_one p hp f.val b hb).symm⟩⟩⟩
  map_zero' := by apply Subtype.ext; exact (rawStep p hp).map_zero
  map_one' := by apply Subtype.ext; exact (rawStep p hp).map_one
  map_add' f g := by apply Subtype.ext; exact (rawStep p hp).map_add f.val g.val
  map_mul' f g := by apply Subtype.ext; exact (rawStep p hp).map_mul f.val g.val
  commutes' z := by apply Subtype.ext; exact (rawStep p hp).commutes z
  map_star' f := by apply Subtype.ext; exact map_star (rawStep p hp) f.val

lemma rawStep_injective (p : ℕ) (hp : 2 ≤ p) : Function.Injective (rawStep p hp) := by
  intro f g h
  apply diagonal_injective (eigenpath p) (eigen_cover p hp)
  apply ContinuousMap.ext
  intro t
  exact (interpolate (zeroReindex p hp) (oneReindex p hp) t).injective
    (DFunLike.congr_fun h t)

lemma step_injective (p : ℕ) (hp : 2 ≤ p) : Function.Injective (step p hp) := by
  intro f g h
  apply Subtype.ext
  exact rawStep_injective p hp (congrArg Subtype.val h)

lemma step_norm (p : ℕ) (hp : 2 ≤ p) (f : PrimeDimensionDrop.Algebra p (p+1)) :
    ‖step p hp f‖ = ‖f‖ := NonUnitalStarAlgHom.norm_map _ (step_injective p hp) f

end KirchbergRordam.BalancedDropSystem


end

end OAI
