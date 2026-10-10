import Mathlib
import OAI.Algebra.GroupRing.LinkComponents
import OAI.Algebra.GroupRing.TypeWeights

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
/-- Generic table application avoids reducing the concrete projective-plane
alphabet while composing the elementary cardinality bounds. -/
theorem allowed_turn_table {PV PD TV T : Type*} [Fintype PD] [Fintype TV]
    (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (v : PV) (a b : PD)
    (ha : Γ.origin a = v) (hb : Γ.origin b = v)
    (hab : plabel a ≠ plabel b) (f : T → T → ℝ)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤ f t u) :
    ((allowed Γ plabel outgoing pin v).card : ℝ) ≤ f (plabel a) (plabel b) :=
  (Nat.cast_le.mpr (allowed_turn_le Γ plabel outgoing pin v a b ha hb)).trans
    (htable _ _ hab)
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open ChainSubdivision TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

/-- A choice of orientation for each actual edge; only this choice, not an
independent matching event for its reverse, is counted. -/
def edgePair (e : Edge len) : Sym2 (Dart len) := s((e,false),(e,true))

omit [Fintype C] [Fintype V] in
theorem edgePair_injective : Function.Injective (edgePair len) := by
  intro e f h
  rw [edgePair,edgePair,Sym2.eq_iff] at h
  rcases h with h | h
  · exact congrArg Prod.fst h.1
  · have hh := congrArg Prod.snd h.1
    cases hh

omit [Fintype V] in
theorem edges_eq : PatternEmbeddings.edges (graph len first last) =
    Finset.univ.image (edgePair len) := by
  ext x
  simp only [PatternEmbeddings.edges,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,b⟩,rfl⟩
    refine ⟨e,?_⟩
    cases b
    · rfl
    · exact Sym2.eq_swap
  · rintro ⟨e,rfl⟩
    exact ⟨(e,false),rfl⟩

omit [Fintype V] in
theorem edges_card : (PatternEmbeddings.edges (graph len first last)).card = ∑ c, len c := by
  rw [edges_eq,Finset.card_image_of_injective _ (edgePair_injective len),Finset.card_univ,card_edges]

def label (w : C → ℤ → WordEstimate.Letter) (d : Dart len) : Types.Letter :=
  if d.2 then Types.inverse (signedLetter (w d.1.1 d.1.2.val))
  else signedLetter (w d.1.1 d.1.2.val)

omit [Fintype C] [Fintype V] in
@[simp] theorem label_reverse (w : C → ℤ → WordEstimate.Letter) (d : Dart len) :
    label len w ((graph len first last).reverse d) = Types.inverse (label len w d) := by
  rcases d with ⟨e,b⟩
  cases b <;> simp [label,Types.inverse_inverse]

omit [Fintype C] [Fintype V] in
@[simp] theorem label_back (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (back len v) = Types.inverse (signedLetter (w v.1 v.2.val)) := rfl
omit [Fintype C] [Fintype V] in
@[simp] theorem label_front (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (front len v) = signedLetter (w v.1 ((v.2.val : ℤ)+1)) := by
  simp [label,front,Nat.cast_add]

omit [Fintype C] [Fintype V] in
/-- Literal internal turn weight, not an independent-letter approximation. -/
theorem internal_weight (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (v : Interior len) :
    TypeWeights.jointWeight (label len w (back len v)) (label len w (front len v)) =
      WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1)) := by
  have hn : label len w (back len v) ≠ label len w (front len v) := by
    intro he
    exact back_ne_front len v (himm (Prod.ext (by simp) he))
  rw [label_back,label_front] at hn ⊢
  rw [TypeWeights.jointWeight_signed]
  unfold WordEstimate.weight
  split_ifs with he
  · exfalso
    apply hn
    rw [he]
    rcases w v.1 v.2.val with ⟨g,b⟩
    exact Types.inverse_signed g b
  · rfl

def turnProduct (w : C → ℤ → WordEstimate.Letter) : ℝ :=
  ∏ v : Interior len, WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1))

omit [Fintype V] in
/-- Exact product of the type-table factors at all unmarked vertices. -/
theorem internal_product (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d))) :
    (∏ v : Interior len,
      TypeWeights.jointWeight (label len w (back len v)) (label len w (front len v))) =
      turnProduct len w := by
  apply Finset.prod_congr rfl
  intro v _
  exact internal_weight len first last w himm v

/-- Marked vertices carry the optional prescribed root. Internal vertices
never gain spurious pins. -/
def pin {TV : Type*} (p : V → Option TV) : Vertex len (V := V) → Option TV
  | .inl v => p v
  | .inr _ => none

omit [Fintype C] [Fintype V] in
@[simp] theorem pin_internal {TV : Type*} (p : V → Option TV) (v : Interior len) :
    pin len p (.inr v) = none := rfl

/-- Source vertex-assignment cost, separating the finitely many marked vertices. -/
def cost {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → WordEstimate.Letter) : Vertex len (V := V) → ℝ
  | .inl v => if pp v = none then n else 1
  | .inr v => n*p*WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1))

theorem cost_product {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → WordEstimate.Letter) :
    (∏ v, cost len pp n p w v) =
      n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1)) * turnProduct len w := by
  rw [Fintype.prod_sum_type]
  simp only [cost,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    card_interiors,Finset.prod_ite,Finset.prod_const,one_pow,mul_one,pow_add,
    turnProduct]
  ring

omit [Fintype V] in
theorem allowed_cost {TV : Type*} [Fintype TV]
    (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (n p : ℝ) (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u) :
    ∀ v, ((StageRealization.allowed (graph len first last) (label len w)
      outgoing (pin len pp) v).card : ℝ) ≤ cost len pp n p w v := by
  intro v
  cases v with
  | inl v =>
    dsimp [cost]
    split_ifs with hp
    · exact (Nat.cast_le.mpr (StageRealization.allowed_card_le _ _ _ _ _)).trans hn
    · obtain ⟨x,hx⟩ := Option.ne_none_iff_exists'.mp hp
      exact_mod_cast StageRealization.pinned_card_le (graph len first last)
        (label len w) outgoing (pin len pp) (.inl v) x hx
  | inr v =>

    have hn' : label len w (back len v) ≠ label len w (front len v) := by
      intro he
      exact back_ne_front len v (himm (Prod.ext (by simp) he))
    have h := StageRealization.allowed_turn_table (graph len first last) (label len w)
      outgoing (pin len pp) (.inr v) (back len v) (front len v)
      (back_origin len first last v) (front_origin len first last v) hn'
      (fun t u => n*p*TypeWeights.jointWeight t u) (by
        intro t u htu
        simpa only [← Nat.card_eq_fintype_card] using htable t u htu)
    rwa [internal_weight len first last w himm] at h

/-- Exact finite first moment for an actually subdivided chain pattern. The
fixed root costs one instead of n; all unmarked vertices use the type table. -/
theorem fixed_label_bound {TV : Type*} [Fintype TV]
    (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (n p : ℝ) (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u)
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : PatternEmbeddings.Dart outgoing //
      PatternEmbeddings.origin outgoing e = v} ≤ d)
    (hsize : ∀ x : PatternEmbeddings.Dart outgoing,
      R + (∑ c, len c) + 4*d^(2*N+1) ≤
        Nat.card {e : PatternEmbeddings.Dart outgoing //
          PatternEmbeddings.label outgoing e = PatternEmbeddings.label outgoing x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅,
        StageRealization.realizations (graph len first last) (label len w) outgoing
          (pin len pp) Types.inverse r : ℕ) : ℝ) /
        (ConditionedMatchings.Matching.conditioned
          (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
          (PatternEmbeddings.origin outgoing) N ∅).card ≤
      (n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1)) * turnProduct len w) / (R : ℝ)^(∑ c, len c) := by
  have h := StageRealization.fixed_label_bound (graph len first last) (label len w)
    outgoing (pin len pp) Types.inverse Types.inverse_ne himm N d R h2 hR hd
    (by intro x; rw [edges_card]; exact hsize x) hΩ (cost len pp n p w)
    (allowed_cost len first last outgoing pp n p w himm hn htable)
  rwa [cost_product,edges_card] at h

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

abbrev BlockTurn := (i : Underlying s len) × Fin (height s len i-1)

def firstCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val,by omega⟩
def nextCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val+1,by omega⟩

omit [Fintype C] in
@[simp] theorem firstCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (firstCoordinate s len i k).val = (k.val : ℤ)+lower s len i := by
  have h := wordCoordinate_val s len i (firstCoordinate s len i k)
  simp only [firstCoordinate,Equiv.apply_symm_apply] at h
  dsimp only [firstCoordinate]
  omega
omit [Fintype C] in
@[simp] theorem nextCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (nextCoordinate s len i k).val = (k.val : ℤ)+lower s len i+1 := by
  have h := wordCoordinate_val s len i (nextCoordinate s len i k)
  simp only [nextCoordinate,Equiv.apply_symm_apply,Nat.cast_add,Nat.cast_one] at h
  dsimp only [nextCoordinate]
  omega

def turnPoint (x : BlockTurn s len) : Position len :=
  includeBlock s hs len x.1 (firstCoordinate s len x.1 x.2)

def turns : Finset (Position len) := Finset.univ.filter (fun x => x.2.val+1 ∈ positions 0 (len x.1))

theorem turnPoint_mem (x : BlockTurn s len) : turnPoint s hs len x ∈ turns len := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have ht := full_subset s hs (len x.1.1) x.1.2 (nextCoordinate s len x.1 x.2).property
  change (firstCoordinate s len x.1 x.2).val+1 ∈ positions 0 (len x.1.1)
  simpa only [firstCoordinate_val,nextCoordinate_val] using ht

omit [Fintype C] in
theorem turnPoint_block (x : BlockTurn s len) :
    turnPoint s hs len x ∈ blockPositions s hs len x.1 := by
  exact Finset.mem_map.mpr ⟨firstCoordinate s len x.1 x.2,Finset.mem_attach _ _,rfl⟩

omit [Fintype C] in
/-- Different block turns are different turns of the actual chain subdivision. -/
theorem turnPoint_injective : Function.Injective (turnPoint s hs len) := by
  intro x y he
  have hc : x.1 = y.1 := by
    by_contra hn
    exact Finset.disjoint_left.mp (blockPositions_disjoint s hs len hn)
      (turnPoint_block s hs len x) (he ▸ turnPoint_block s hs len y)
  rcases x with ⟨i,k⟩
  rcases y with ⟨i',l⟩
  dsimp at hc
  subst i'
  have hv := congrArg (fun x : Position len => x.2.val) he
  change (firstCoordinate s len i k).val = (firstCoordinate s len i l).val at hv
  rw [firstCoordinate_val,firstCoordinate_val] at hv
  have hk : k = l := Fin.ext (by omega)
  cases hk
  rfl

def atTurn (w : C → ℤ → Letter) (x : Position len) : ℝ :=
  weight (w x.1 x.2.val) (w x.1 (x.2.val+1))
def chainProduct (w : C → ℤ → Letter) : ℝ := ∏ x ∈ turns len, atTurn len w x

omit [Fintype C] in
theorem wordWeight_pred (h : ℕ) (W : Fin h → Letter) :
    wordWeight h W = ∏ k : Fin (h-1), weight (W ⟨k.val,by omega⟩) (W ⟨k.val+1,by omega⟩) := by
  cases h with
  | zero => simp [wordWeight]
  | succ h => exact wordWeight_eq_product h W

theorem turn_product (w : C → ℤ → Letter) :
    (∏ x : BlockTurn s len, atTurn len w (turnPoint s hs len x)) =
      ∏ i : Underlying s len, wordWeight (height s len i) (word s len w i) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [wordWeight_pred]
  apply Finset.prod_congr rfl
  intro k _
  change weight (w i.1 (firstCoordinate s len i k).val)
    (w i.1 ((firstCoordinate s len i k).val+1)) =
    weight (w i.1 ((k.val : ℤ)+lower s len i))
      (w i.1 (((k.val+1 : ℕ) : ℤ)+lower s len i))
  rw [firstCoordinate_val]
  simp only [Nat.cast_add,Nat.cast_one]
  congr 2; ring

include hs in
/-- Discarding only nonnegative factors at most one can increase a chain's
turn product. This accounts for cross-block turns and all end fragments. -/
theorem chain_le_blocks (w : C → ℤ → Letter) :
    chainProduct len w ≤ ∏ i : Underlying s len, wordWeight (height s len i) (word s len w i) := by
  let S := Finset.univ.image (turnPoint s hs len)
  have hS : S ⊆ turns len := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact turnPoint_mem s hs len y
  calc
    chainProduct len w ≤ ∏ x ∈ S, atTurn len w x :=
      Finset.prod_le_prod_of_subset_of_le_one₀ hS (fun x _ => weight_nonneg _ _)
        (fun x _ _ => weight_le_one _ _)
    _ = ∏ x : BlockTurn s len, atTurn len w (turnPoint s hs len x) := by
      exact Finset.prod_image (fun _ _ _ _ he => turnPoint_injective s hs len he)
    _ = _ := turn_product s hs len w

/-- A literal bin contributes its upper endpoint to the fixed-label exponent. -/
theorem bin_weight_upper {h : ℕ} {d : ℤ} {W : Fin h → Letter}
    (hW : W ∈ binWords h d) : wordWeight h W ≤ Real.exp (-(d : ℝ)) := by
  obtain ⟨hp,he⟩ := (Finset.mem_filter.mp hW).2
  have hf := Int.floor_le (-Real.log (wordWeight h W))
  rw [he] at hf
  calc
    wordWeight h W = Real.exp (Real.log (wordWeight h W)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

include hs in
/-- Fixed-label loss from all active full blocks. The stage instance is
obtained by taking C to be the active-chain subtype itself. -/
theorem chain_bin_bound (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i)) :
    chainProduct len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  refine (chain_le_blocks s hs len w).trans ?_
  calc
    (∏ i, wordWeight (height s len i) (word s len w i)) ≤ ∏ i, Real.exp (-(d i : ℝ)) :=
      Finset.prod_le_prod₀ (fun i _ => wordWeight_nonneg _ _) (fun i _ => bin_weight_upper (hbin i))
    _ = _ := by rw [← Real.exp_sum,Finset.sum_neg_distrib]

omit [Fintype C] in
theorem mem_positions_nat (n : ℕ) (q : ℤ) :
    q ∈ positions 0 n ↔ 0 ≤ q ∧ q < n := by
  have hlo : ⌈(0 : ℝ)-1/2⌉ = (0 : ℤ) := by norm_num
  have hhi : ⌈(n : ℝ)-1/2⌉ = (n : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    push_cast
    constructor <;> linarith
  simp only [positions,hlo,hhi,Finset.mem_Ico]

/-- Literal indexing equivalence from internal subdivision vertices to the
half-integer-grid turn positions. -/
def turnEquiv : ((c : C) × Fin (len c-1)) ≃ (turns len) where
  toFun v := ⟨⟨v.1,⟨(v.2.val : ℤ),(mem_positions_nat (len v.1) v.2.val).mpr
      ⟨by omega,by omega⟩⟩⟩,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (mem_positions_nat (len v.1) (v.2.val+1)).mpr
      ⟨by omega,by omega⟩⟩⟩
  invFun x := ⟨x.val.1,⟨x.val.2.val.toNat,by
    have h0 := (mem_positions_nat (len x.val.1) x.val.2.val).mp x.val.2.property
    have h1 := (mem_positions_nat (len x.val.1) (x.val.2.val+1)).mp
      (Finset.mem_filter.mp x.property).2
    omega⟩⟩
  left_inv v := by
    rcases v with ⟨c,k⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Fin.ext
    exact Int.toNat_natCast k.val
  right_inv x := by
    rcases x with ⟨⟨c,q,hq⟩,hx⟩
    apply Subtype.ext
    dsimp only
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    exact Int.toNat_of_nonneg ((mem_positions_nat _ _).mp hq).1

/-- The full-chain product is exactly the product over the actual internal
vertices used in the matching first moment. -/
theorem chainProduct_eq (w : C → ℤ → Letter) :
    chainProduct len w = ∏ v : ((c : C) × Fin (len c-1)),
      weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1)) := by
  rw [chainProduct,← Finset.prod_coe_sort]
  symm
  exact Fintype.prod_equiv (turnEquiv len) _ _ (fun _ => rfl)

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI
