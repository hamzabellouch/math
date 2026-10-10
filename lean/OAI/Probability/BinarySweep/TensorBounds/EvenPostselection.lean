import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungHilbert
import OAI.Probability.BinarySweep.TensorBounds.TensorReduction
import OAI.Probability.BinarySweep.MatrixBounds.MatrixSqrtBlocks

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {K A B : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]

lemma reduced_postselection (n : ℕ) (hn : 0 < n) (e : K → A × B)
    (v : (Fin n → K) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    ((rankOne v).trace • (∑ c : WordType K n, ∑ t : K → ZMod (n+1),
      matrixTensorPower n (reducedPhaseDensity n e c t)) -
      reshape (wordPair n e) v * (reshape (wordPair n e) v).conjTranspose).PosSemidef := by
  have h := densityChannel_psd (wordPair n e) (symmetric_vector_postselection n hn v hv)
  rw [densityChannel_sub, densityChannel_smul, densityChannel_sum] at h
  simp only [phaseAverage, densityChannel_smul, densityChannel_sum,
    densityChannel_tensorRankOne, ← Finset.smul_sum, smul_smul] at h
  have hd : (((n+1 : ℕ) : ℂ)^Fintype.card K) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
  rw [mul_assoc, mul_inv_cancel₀ hd, mul_one, densityChannel_rankOne] at h
  exact h

variable {P : Type*} [DecidableEq P]

def MatchedPair (p : A → P) := {x : A × A // p x.1 = p x.2}
instance (p : A → P) : Fintype (MatchedPair p) :=
  inferInstanceAs (Fintype {pair : A × A // p pair.1 = p pair.2})
instance (p : A → P) : DecidableEq (MatchedPair p) :=
  inferInstanceAs (DecidableEq {pair : A × A // p pair.1 = p pair.2})

def matchedEmbedding (p : A → P) : MatchedPair p → A × A := Subtype.val

omit [Fintype A] [DecidableEq A] [DecidableEq P] in
lemma matchedEmbedding_injective (p : A → P) : Function.Injective (matchedEmbedding p) :=
  Subtype.val_injective

def pairVector (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (Fin n → MatchedPair p) → ℂ :=
  fun w => Q (fun i => (w i).val.1) (fun i => (w i).val.2)

lemma reshape_pairVector (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hQ : ∀ x y, (fun i => p (x i)) ≠ (fun i => p (y i)) → Q x y = 0) :
    reshape (wordPair n (matchedEmbedding p)) (pairVector n p Q) = Q := by
  ext x y
  by_cases h : (fun i => p (x i)) = (fun i => p (y i))
  · let w : Fin n → MatchedPair p := fun i => ⟨(x i,y i), congrFun h i⟩
    have hw : wordPair n (matchedEmbedding p) w = (x,y) := rfl
    have ht := reshape_injective_apply (wordPair n (matchedEmbedding p))
      (wordPair_injective n _ (matchedEmbedding_injective p)) (pairVector n p Q) w
    rw [hw] at ht
    exact ht
  · have hn : (x,y) ∉ Set.range (wordPair n (matchedEmbedding p)) := by
      rintro ⟨w,hw⟩
      apply h
      funext i
      have hi := (wordPair_eq_iff n _ w x y).mp hw i
      have hh := (w i).property
      change p (matchedEmbedding p (w i)).1 = p (matchedEmbedding p (w i)).2 at hh
      rw [hi] at hh
      exact hh
    rw [reshape_outside _ _ x y hn, hQ x y h]

def wordPerm (n : ℕ) (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → A) where
  toFun x := x ∘ g
  invFun x := x ∘ g.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [Fintype A] [DecidableEq P] in
lemma pairVector_symmetric (n : ℕ) (p : A → P) (Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hQ : ∀ (g : Equiv.Perm (Fin n)) x y, Q (x ∘ g) (y ∘ g) = Q x y) :
    ∀ w u, wordCounts w = wordCounts u → pairVector n p Q w = pairVector n p Q u := by
  intro w u h
  obtain ⟨g,hg⟩ := exists_perm_eq_of_wordCounts h
  have hw : w = u ∘ g := (funext hg).symm
  rw [hw]
  simpa only [pairVector, Function.comp_def] using
    hQ g (fun i => (u i).val.1) (fun i => (u i).val.2)

theorem even_block_postselection (n : ℕ) (hn : 0 < n) (p : A → P)
    (Q : Matrix (Fin n → A) (Fin n → A) ℂ) (hQ : Q.PosSemidef)
    (hblock : ∀ x y, (p ∘ x) ≠ (p ∘ y) → Q x y = 0)
    (hperm : ∀ (g : Equiv.Perm (Fin n)) x y, Q (x ∘ g) (y ∘ g) = Q x y) :
    (Q.trace • (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
      matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) - Q).PosSemidef := by
  let S := CFC.sqrt Q
  have hSblock : ∀ x y, (p ∘ x) ≠ (p ∘ y) → S x y = 0 :=
    sqrt_block_diagonal (fun x => p ∘ x) Q hblock
  have hSperm (g : Equiv.Perm (Fin n)) (x y) : S (x ∘ g) (y ∘ g) = S x y := by
    have hh := sqrt_submatrix_invariant Q hQ (wordPerm n g) (by
      ext u v; exact hperm g u v)
    exact congrFun (congrFun hh x) y
  let v := pairVector n p S
  have hr : reshape (wordPair n (matchedEmbedding p)) v = S :=
    reshape_pairVector n p S hSblock
  have ht : (rankOne v).trace = Q.trace := by
    rw [← reshape_trace (wordPair n (matchedEmbedding p))
      (wordPair_injective n _ (matchedEmbedding_injective p)) v, hr, sqrt_gram Q hQ]
  have hh := reduced_postselection n hn (matchedEmbedding p) v (pairVector_symmetric n p S hSperm)
  rw [ht, hr, sqrt_gram Q hQ] at hh
  exact hh

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} {n : ℕ}

def signC (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) : ℂ :=
  ((koszulSign β g : ℤ) : ℂ)

@[simp] lemma signC_one (β : Fin n → Bool) : signC β 1 = 1 := by simp [signC]
lemma signC_mul (β : Fin n → Bool) (f g : Equiv.Perm (Fin n)) :
    signC β (f*g) = signC (β ∘ g.symm) f * signC β g := by
  simp only [signC, koszulSign_mul, Units.val_mul, Int.cast_mul]
lemma signC_sq (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    signC β g * signC β g = 1 := by
  unfold signC
  rw [← Int.cast_mul, ← Units.val_mul, koszulSign_sq]
  norm_num
@[simp] lemma signC_star (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    star (signC β g) = signC β g := by simp [signC]
lemma signC_swap (β : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (hβ : β a = β b) :
    signC β (Equiv.swap a b) = if β a = true then -1 else 1 := by
  simp only [signC, koszulSign_swap β a b hab hβ]
  split_ifs <;> norm_num

def act (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    ((Fin n → A) → ℂ) →ₗ[ℂ] ((Fin n → A) → ℂ) where
  toFun v x := signC (p ∘ x) g⁻¹ * v (x ∘ g)
  map_add' u v := by ext x; simp only [Pi.add_apply, mul_add]
  map_smul' c v := by ext x; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm,
    RingHom.id_apply]

@[simp] lemma act_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) (x) :
    act p g v x = signC (p ∘ x) g⁻¹ * v (x ∘ g) := rfl

lemma act_one (p : A → Bool) : act (n := n) p 1 = 1 := by
  ext v x
  simp [act]

lemma act_mul (p : A → Bool) (g h : Equiv.Perm (Fin n)) :
    act p (g*h) = act p g * act p h := by
  apply LinearMap.ext
  intro v
  funext x
  change signC (p ∘ x) (g*h)⁻¹ * v (x ∘ ⇑(g*h)) =
    signC (p ∘ x) g⁻¹ * (signC (p ∘ (x ∘ g)) h⁻¹ * v ((x ∘ g) ∘ h))
  simp only [_root_.mul_inv_rev, signC_mul]
  have he : (p ∘ x) ∘ (Equiv.symm g⁻¹) = p ∘ (x ∘ g) := rfl
  rw [he]
  have hw : x ∘ ⇑(g*h) = (x ∘ g) ∘ h := rfl
  rw [hw]
  ring

def tensorRep (p : A → Bool) (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) ((Fin n → A) → ℂ) where
  toFun := act p
  map_one' := act_one p
  map_mul' := act_mul p

def Invariant (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ) : Prop :=
  ∀ (g : Equiv.Perm (Fin n)) x y,
    M (x ∘ g) (y ∘ g) = signC (p ∘ x) g⁻¹ * signC (p ∘ y) g⁻¹ * M x y

lemma invariant_same_parity (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (x y : Fin n → A)
    (h : p ∘ x = p ∘ y) : M (x ∘ g) (y ∘ g) = M x y := by
  rw [hM g x y, h, signC_sq, one_mul]

lemma comp_swap_eq {T : Type*} (x : Fin n → T) (i j : Fin n) (h : x i = x j) :
    x ∘ Equiv.swap i j = x := by
  funext k
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma invariant_repeated_mismatch_zero (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : Invariant p M)
    (x y : Fin n → A) (i j : Fin n) (hij : i ≠ j)
    (hx : x i = x j) (hy : y i = y j) (hp : p (x i) ≠ p (y i)) : M x y = 0 := by
  have h := hM (Equiv.swap i j) x y
  rw [comp_swap_eq x i j hx, comp_swap_eq y i j hy, Equiv.swap_inv,
    signC_swap _ i j hij (by change p (x i)=p (x j); rw [hx]),
    signC_swap _ i j hij (by change p (y i)=p (y j); rw [hy])] at h
  simp only [Function.comp_apply] at h
  cases hx' : p (x i) <;> cases hy' : p (y i)
  · exact False.elim (hp (hx'.trans hy'.symm))
  · simp only [hx', hy', Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at h
    linear_combination (1/2 : ℂ) * h
  · simp only [hx', hy', Bool.false_eq_true, ↓reduceIte, mul_one, neg_one_mul] at h
    linear_combination (1/2 : ℂ) * h
  · exact False.elim (hp (hx'.trans hy'.symm))

variable [Fintype A]

lemma invariant_mismatch_card (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : Invariant p M)
    (x y : Fin n → A) (hxy : M x y ≠ 0) :
    (Finset.univ.filter (fun i => p (x i) ≠ p (y i))).card ≤ (Fintype.card A)^2 := by
  let T := {i : Fin n // p (x i) ≠ p (y i)}
  let f : T → A × A := fun i => (x i.val,y i.val)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra h
    have hx := congrArg Prod.fst hij
    have hy := congrArg Prod.snd hij
    exact hxy (invariant_repeated_mismatch_zero p M hM x y i j h hx hy i.property)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [T, Fintype.card_subtype, Fintype.card_prod, pow_two] using hc

end BinaryCoordinateSweeps.Signed

end

end OAI
