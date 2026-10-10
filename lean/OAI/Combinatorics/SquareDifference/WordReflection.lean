import OAI.Combinatorics.SquareDifference.MarkedTuples

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma prod_word_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b α β) v (z v)) =
      halfProduct b α β a (fun v => z v.1) *
      halfProduct b α β a (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_half, foldWord_reflect_half b hne, halfProduct]

lemma prod_word_opposite_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b β α) v (z v)) =
      halfProduct b α β (a ∘ reflect b α β) (fun v => z v.1) *
      halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_opposite_half, foldWord_opposite_reflect_half,
    halfProduct]

lemma wordIntegral_folding {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hsym : ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a|^2 ≤
      multilinearIntegral L (a ∘ foldWord b α β) *
      multilinearIntegral L (a ∘ foldWord b β α) ∧
      0 ≤ multilinearIntegral L (a ∘ foldWord b α β) := by
  have hsplit : multilinearIntegral L a =
      L (fun z => halfProduct b α β a (fun v => z v.1) *
        halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1))) := by
    unfold multilinearIntegral
    apply congrArg L
    funext z
    exact prod_word_split b hne (fun v => a v (z v))
  simp only [multilinearIntegral, prod_word_fold b hne, prod_word_opposite_fold b hne]
  constructor
  · have hcs := cut_cauchy_schwarz L (fun z v => z v.1)
      (fun z v => z (reflect b α β v.1)) hsym hpos
      (halfProduct b α β a) (halfProduct b α β (a ∘ reflect b α β))
    rw [← hsplit] at hcs
    exact hcs
  · exact hpos _

lemma word_diagonal_nonneg {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (g : X → ℝ) : 0 ≤ diagonalIntegral L g := by
  have hf : (fun _ : WordVertex B h => g) ∘ foldWord b α β = fun _ => g := rfl
  unfold diagonalIntegral multilinearIntegral
  rw [← hf]
  simp_rw [prod_word_fold b hne]
  exact hpos _

lemma word_signed_holder {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b₀ : B) {α₀ β₀ : Fin h} (hne₀ : α₀ ≠ β₀)
    (hsym : ∀ b α β, ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ b α β, α ≠ β → ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card (WordVertex B h) : ℝ)) := by
  classical
  have hd := word_diagonal_nonneg L b₀ hne₀ (hpos b₀ α₀ β₀ hne₀)
  apply holder_of_finite_maximum L hd ?_ a
  intro a
  obtain ⟨i, hi⟩ := word_folding_maximum
    (fun r : WordVertex B h → WordVertex B h => multilinearIntegral L (a ∘ r))
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).1)
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).2)
  refine ⟨i, ?_⟩
  have hh := hi id
  change |multilinearIntegral L a| ≤ |diagonalIntegral L (a i)| at hh
  rwa [abs_of_nonneg (hd (a i))] at hh

lemma tupleLaw_diagonal_nonneg {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ)) (g : ZMod p → ℝ) :
    0 ≤ diagonalIntegral tupleLaw g := by
  exact word_diagonal_nonneg tupleLaw (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tupleLaw_reflection_positive hp (⟨0, by decide⟩ : Fin tupleBlocks) (by decide)) g

lemma tupleLaw_signed_holder {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ)) (a : TupleVertex → ZMod p → ℝ) :
    |multilinearIntegral tupleLaw a| ≤
      ∏ v, (diagonalIntegral tupleLaw (a v))^((1 : ℝ)/(Fintype.card TupleVertex : ℝ)) := by
  exact word_signed_holder tupleLaw (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide) tupleLaw_symmetric
    (fun b _α _β hne => tupleLaw_reflection_positive hp b hne) a

lemma multilinearIntegral_sum {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → I → X → ℝ) :
    multilinearIntegral L (fun v x => ∑ i, a v i x) =
      ∑ r : V → I, multilinearIntegral L (fun v => a v (r v)) := by
  classical
  unfold multilinearIntegral
  rw [← map_sum]
  apply congrArg L
  funext z
  simp only [Finset.sum_apply]
  exact Fintype.prod_sum fun v i => a v i (z v)

lemma diagonalIntegral_smul {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (f : X → ℝ) :
    diagonalIntegral L (c • f) = c^(Fintype.card V) * diagonalIntegral L f := by
  unfold diagonalIntegral multilinearIntegral
  simp only [Pi.smul_apply, smul_eq_mul, prod_mul_distrib, prod_const, card_univ]
  exact map_smul L (c^Fintype.card V) (fun z => ∏ _v, f (z _v))

noncomputable def diagonalRoot {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  (diagonalIntegral L g)^((1 : ℝ)/(Fintype.card V : ℝ))

lemma diagonalRoot_nonneg {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (g : X → ℝ) :
    0 ≤ diagonalRoot L g := Real.rpow_nonneg (hdiag g) _

lemma diagonalRoot_pow {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (g : X → ℝ) :
    (diagonalRoot L g)^(Fintype.card V) = diagonalIntegral L g := by
  unfold diagonalRoot
  rw [← Real.rpow_mul_natCast (hdiag g)]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one]

lemma diagonalRoot_smul {V X : Type*} [Fintype V] [Nonempty V]
    (heven : Even (Fintype.card V))
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (c : ℝ) (g : X → ℝ) :
    diagonalRoot L (c • g) = |c| * diagonalRoot L g := by
  unfold diagonalRoot
  rw [diagonalIntegral_smul]
  rw [← heven.pow_abs c, Real.mul_rpow (pow_nonneg (abs_nonneg c) _) (hdiag g)]
  congr 1
  rw [← Real.rpow_natCast_mul (abs_nonneg c)]
  rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one]

lemma diagonalIntegral_add_le {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f g : X → ℝ) :
    diagonalIntegral L (f+g) ≤ (diagonalRoot L f + diagonalRoot L g)^(Fintype.card V) := by
  classical
  let a (v : V) (i : Bool) : X → ℝ := if i then g else f
  have he (x : X) (v : V) : ∑ i, a v i x = (f+g) x := by simp [a, add_comm]
  have heq : diagonalIntegral L (f+g) =
      ∑ r : V → Bool, multilinearIntegral L (fun v => a v (r v)) := by
    simpa only [he, diagonalIntegral] using multilinearIntegral_sum L a
  rw [heq]
  calc
    _ ≤ ∑ r : V → Bool, ∏ v, diagonalRoot L (a v (r v)) := by
      apply sum_le_sum
      intro r _
      exact (le_abs_self _).trans (hholder _)
    _ = ∏ v : V, ∑ i : Bool, diagonalRoot L (a v i) := (Fintype.prod_sum (fun v i => diagonalRoot L (a v i))).symm
    _ = _ := by simp [a, add_comm]

lemma diagonalRoot_add_le {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f g : X → ℝ) : diagonalRoot L (f+g) ≤ diagonalRoot L f + diagonalRoot L g := by
  have h := Real.rpow_le_rpow (hdiag (f+g)) (diagonalIntegral_add_le L hholder f g)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg (Fintype.card V)))
  change diagonalRoot L (f+g) ≤ _ at h
  have hn := add_nonneg (diagonalRoot_nonneg L hdiag f) (diagonalRoot_nonneg L hdiag g)
  rw [← Real.rpow_natCast_mul hn] at h
  rwa [mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one] at h

noncomputable def functionalSeminorm {V X : Type*} [Fintype V] [Nonempty V]
    (heven : Even (Fintype.card V))
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v)) : Seminorm ℝ (X → ℝ) :=
  Seminorm.of (diagonalRoot L) (diagonalRoot_add_le L hdiag hholder)
    (fun c g => by simpa only [Real.norm_eq_abs] using diagonalRoot_smul heven L hdiag c g)

noncomputable def cutKernel {Ω I : Type*} [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) : Matrix I I ℝ :=
  fun x y => L (fun z => if left z = x ∧ right z = y then 1 else 0)

lemma cut_form_eq_sum {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, cutKernel L left right x y * F x * G y := by
  classical
  have he : (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, (F x * G y) • (fun z => if left z = x ∧ right z = y then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]
    simp
  rw [he, map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_sum]
  apply sum_congr rfl
  intro y _
  rw [map_smul, smul_eq_mul]
  change (F x * G y) * cutKernel L left right x y = _
  ring

lemma cutKernel_posSemidef {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z))) :
    (cutKernel L left right).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    have hs := hsym (fun z => if z=x then 1 else 0) (fun z => if z=y then 1 else 0)
    have he (x y : I) (z : Ω) :
        (if left z=x then (1 : ℝ) else 0) * (if right z=y then 1 else 0) =
          if left z=x ∧ right z=y then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [he] at hs
    exact hs.symm
  · intro F
    have hh := hpos F
    rw [cut_form_eq_sum] at hh
    simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
      mul_left_comm, mul_comm, mul_assoc] using hh

lemma matrix_prod_posSemidef {J I : Type*} [Fintype J] [Fintype I]
    (K : J → Matrix I I ℝ) (hK : ∀ j, (K j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j, K j x y) := by
  classical
  have hs (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, K j x y) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun x y => ∏ j ∈ (∅ : Finset J), K j x y) =
          Matrix.vecMulVec (fun _ : I => (1 : ℝ)) (star (fun _ : I => (1 : ℝ))) := by
        ext x y
        simp [Matrix.vecMulVec]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
    | @insert j s hj ih =>
      have he : (fun x y => ∏ k ∈ insert j s, K k x y) =
          (K j).hadamard (fun x y => ∏ k ∈ s, K k x y) := by
        ext x y
        change (∏ k ∈ insert j s, K k x y) = K j x y * ∏ k ∈ s, K k x y
        exact prod_insert hj
      rw [he]
      exact (hK j).hadamard ih
  exact hs univ

lemma cut_positive_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F : I → ℝ) :
    0 ≤ L (fun z => F (left z) * F (right z)) := by
  rw [cut_form_eq_sum]
  have hh := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK).2 F
  simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
    mul_left_comm, mul_comm, mul_assoc] using hh

lemma cut_symmetric_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)) := by
  rw [cut_form_eq_sum, cut_form_eq_sum, sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  have hs : cutKernel L left right x y = cutKernel L left right y x := by
    have h := congrFun (congrFun hK.isHermitian x) y
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  rw [hs]
  ring

noncomputable def lawDensity {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) : ℝ :=
  L (fun y => if y=x then 1 else 0)

noncomputable def tensorLaw {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) : ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j v)
  map_add' F G := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← mul_sum, RingHom.id_apply]

lemma tensorLaw_fubini {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ j, (V → X j) → ℝ) :
    tensorLaw L (fun z => ∏ j, F j (fun v => z v j)) = ∏ j, L j (F j) := by
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * ∏ j, F j (z j)) = _
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j z => lawDensity (L j) z * F j z)]
  apply prod_congr rfl
  intro j _
  exact (linearFunctional_density (L j) (F j)).symm

lemma tensorLaw_probability {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L j (fun _ => 1)=1) :
    tensorLaw L (fun _ => 1) = 1 := by
  have hh := tensorLaw_fubini L (fun _ _ => 1)
  simpa only [prod_const_one, hL] using hh

lemma tensorLaw_nonneg {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ j F, (∀ z, 0 ≤ F z) → 0 ≤ L j F)
    (F : (V → ∀ j, X j) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tensorLaw L F := by
  apply sum_nonneg
  intro z _
  apply mul_nonneg (prod_nonneg fun j _ => ?_) (hF _)
  exact hL j _ (fun _ => by split_ifs <;> norm_num)

lemma prod_indicator_forall {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Decidable (∀ j, P j)] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma tensorLaw_cutKernel {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (x y : W → ∀ j, X j) :
    cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) x y =
      ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
  classical
  unfold cutKernel
  have he (z : V → ∀ j, X j) :
      (if (fun w => z (l w))=x ∧ (fun w => z (r w))=y then (1 : ℝ) else 0) =
      ∏ j, if (fun w => z (l w) j)=(fun w => x w j) ∧
        (fun w => z (r w) j)=(fun w => y w j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · rintro ⟨hl, hr⟩ j
      exact ⟨funext fun w => congrFun (congrFun hl w) j,
        funext fun w => congrFun (congrFun hr w) j⟩
    · intro h
      exact ⟨funext fun w => funext fun j => congrFun (h j).1 w,
        funext fun w => funext fun j => congrFun (h j).2 w⟩
  simp_rw [he]
  exact tensorLaw_fubini L (fun j z => if (fun w => z (l w))=(fun w => x w j) ∧
    (fun w => z (r w))=(fun w => y w j) then 1 else 0)

lemma tensorLaw_cut_positive {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (hsym : ∀ j, ∀ F G : (W → X j) → ℝ,
      L j (fun z => F (fun w => z (l w)) * G (fun w => z (r w))) =
      L j (fun z => G (fun w => z (l w)) * F (fun w => z (r w))))
    (hpos : ∀ j, ∀ F : (W → X j) → ℝ,
      0 ≤ L j (fun z => F (fun w => z (l w)) * F (fun w => z (r w)))) :
    (cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w))).PosSemidef := by
  classical
  have he : cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) =
      fun x y => ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
    funext x y
    exact tensorLaw_cutKernel L l r x y
  rw [he]
  let K (j : J) : Matrix (W → ∀ j, X j) (W → ∀ j, X j) ℝ :=
    (cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))).submatrix
      (fun x w => x w j) (fun x w => x w j)
  have hK (j : J) : (K j).PosSemidef :=
    (cutKernel_posSemidef (L j) _ _ (hsym j) (hpos j)).submatrix _
  exact matrix_prod_posSemidef K hK

lemma tensorLaw_word_symmetric {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) (α β : Fin h) (F G : (CutHalf b α β → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      tensorLaw L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  by_cases hne : α = β
  · subst β
    have he (z : WordVertex B h → ∀ j, X j) : (fun v : CutHalf b α α =>
        z (reflect b α α v.1)) = fun v => z v.1 := by
      funext v
      exact False.elim (lt_irrefl _ v.2)
    simp_rw [he, mul_comm (F _) (G _)]
  · exact cut_symmetric_of_kernel (tensorLaw L) _ _
      (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
        (fun v => reflect b α β v.1) (fun j => hsym j b α β)
        (fun j => hpos j b α β hne)) F G

lemma tensorLaw_word_positive {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (F : (CutHalf b α β → ∀ j, X j) → ℝ) :
    0 ≤ tensorLaw L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  exact cut_positive_of_kernel (tensorLaw L) _ _
    (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
      (fun v => reflect b α β v.1) (fun j => hsym j b α β)
      (fun j => hpos j b α β hne)) F

noncomputable def productTupleLaw {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] :
    ((TupleVertex → ∀ j, ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw (fun j => tupleLaw (p := p j))

lemma productTupleLaw_diagonal_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ)) (g : (∀ j, ZMod (p j)) → ℝ) :
    0 ≤ diagonalIntegral (productTupleLaw p) g := by
  exact word_diagonal_nonneg (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)
      (⟨0, by decide⟩ : Fin tupleBlocks) (by decide)) g

lemma productTupleLaw_signed_holder {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ))
    (a : TupleVertex → (∀ j, ZMod (p j)) → ℝ) :
    |multilinearIntegral (productTupleLaw p) a| ≤
      ∏ v, diagonalRoot (productTupleLaw p) (a v) := by
  exact word_signed_holder (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_symmetric (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne))
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)) a

lemma squareIndicator_mul_sq {F : Type*} [Field F] (q : F) (hq : q ≠ 0) (x : F) :
    squareIndicator (q^2*x) = squareIndicator x := by
  classical
  have hs : IsSquare (q^2*x) ↔ IsSquare x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y/q, ?_⟩
      apply (mul_right_cancel₀ (pow_ne_zero 2 hq))
      calc
        x*q^2 = y*y := by rw [mul_comm]; exact hy
        _ = ((y/q)*(y/q))*q^2 := by field_simp
    · rintro ⟨y, rfl⟩
      exact ⟨q*y, by ring⟩
  unfold squareIndicator
  rw [hs]
  have hn : q^2*x ≠ 0 ↔ x ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact and_iff_right (pow_ne_zero 2 hq)
  simp only [hn]

lemma tupleValidity_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (fun i => q^2 * Y i + a) = tupleValidity S Y := by
  unfold tupleValidity
  apply prod_congr rfl
  intro e _
  rw [show (q^2*Y e.2+a)-(q^2*Y e.1+a)=q^2*(Y e.2-Y e.1) by ring]
  exact squareIndicator_mul_sq q hq _

end SquareDifference
end

end OAI
