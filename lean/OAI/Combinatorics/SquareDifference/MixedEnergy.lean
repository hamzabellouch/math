import OAI.Combinatorics.SquareDifference.GaussSum

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

def directedCrossEdge {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) : ((I × A) ⊕ (J × B)) × ((I × A) ⊕ (J × B)) :=
  if dir e.1.1 e.1.2 then
    (Sum.inl (e.1.1, e.2.1), Sum.inr (e.1.2, e.2.2))
  else (Sum.inr (e.1.2, e.2.2), Sum.inl (e.1.1, e.2.1))

lemma directedCrossEdge_injective {I J A B : Type*} (dir : I → J → Bool) :
    Function.Injective (directedCrossEdge (A := A) (B := B) dir) := by
  rintro ⟨⟨i,j⟩,⟨a,b⟩⟩ ⟨⟨i',j'⟩,⟨a',b'⟩⟩ h
  dsimp [directedCrossEdge] at h
  split_ifs at h <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false]

lemma directedCrossEdge_noloop {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) :
    (directedCrossEdge dir e).1 ≠ (directedCrossEdge dir e).2 := by
  dsimp [directedCrossEdge]
  split_ifs <;> simp

lemma directedCrossEdge_noopp {I J A B : Type*} (dir : I → J → Bool)
    (e e' : (I × J) × (A × B)) :
    directedCrossEdge dir e' ≠ ((directedCrossEdge dir e).2, (directedCrossEdge dir e).1) := by
  rcases e with ⟨⟨i,j⟩,⟨a,b⟩⟩
  rcases e' with ⟨⟨i',j'⟩,⟨a',b'⟩⟩
  dsimp [directedCrossEdge]
  split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, not_false_eq_true]
  all_goals rintro ⟨⟨hi,ha⟩,⟨hj,hb⟩⟩; subst_vars; simp_all

noncomputable def listKernel {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) : ℝ :=
  ∏ e ∈ E, if dir e.1 e.2 then squareIndicator (y e.2 - x e.1)
    else squareIndicator (x e.1 - y e.2)

lemma copied_graph_count {I J A B : Type*}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) (F : Finset (A × B)) :
    |(𝔼 z : (I × A) ⊕ (J × B) → ZMod p,
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2)))) - (1 / 2 : ℝ) ^ (E.card * F.card)| ≤
      (E.card * F.card : ℕ) * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let G := (E ×ˢ F).image (directedCrossEdge dir)
  have hnoloop : ∀ e ∈ G, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact directedCrossEdge_noloop dir a
  have hnoopp : ∀ e ∈ G, (e.2, e.1) ∉ G := by
    intro e he h
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    obtain ⟨a', _, ha'⟩ := mem_image.mp h
    exact directedCrossEdge_noopp dir a a' ha'
  have hc : G.card = E.card * F.card := by
    rw [card_image_of_injective _ (directedCrossEdge_injective dir), card_product]
  have hprod (z : (I × A) ⊕ (J × B) → ZMod p) :
      (∏ e ∈ G, squareIndicator (z e.2 - z e.1)) =
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2))) := by
    rw [prod_image (directedCrossEdge_injective dir).injOn, prod_product, prod_comm]
    apply prod_congr rfl
    intro ab _
    dsimp [listKernel]
    apply prod_congr rfl
    intro ij _
    dsimp [directedCrossEdge]
    split_ifs <;> rfl
  have h := graph_count hp G hnoloop hnoopp
  simpa only [hc, hprod] using h

lemma centered_product_moment_bound {T X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq T] (S : Finset T) (hS : S.Nonempty) (K : T → X → ℝ)
    {c δ : ℝ} (hc : |c| ≤ 1) (hδ : 0 ≤ δ)
    (hmom : ∀ F ⊆ S, |(𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card| ≤ F.card * δ) :
    |𝔼 x : X, ∏ i ∈ S, (K i x - c)| ≤
      (∑ F ∈ S.powerset, (F.card : ℝ)) * δ := by
  classical
  have hmain : (∑ F ∈ S.powerset, c ^ F.card * (-c) ^ (S \ F).card) = 0 := by
    have h := prod_add (fun _ : T => c) (fun _ : T => -c) S
    simpa [hS.card_pos.ne'] using h.symm
  have hexpand : (𝔼 x : X, ∏ i ∈ S, (K i x - c)) =
      ∑ F ∈ S.powerset, (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card := by
    simp_rw [sub_eq_add_neg, prod_add, prod_const, expect_sum_comm, ← expect_mul]
  rw [hexpand, ← sub_zero (∑ F ∈ S.powerset,
    (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card), ← hmain, ← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ F ∈ S.powerset,
        |((𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card) * (-c) ^ (S \ F).card| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ F ∈ S.powerset, (F.card : ℝ) * δ := by
      apply sum_le_sum
      intro F hF
      rw [abs_mul]
      have hpow : |(-c) ^ (S \ F).card| ≤ 1 := by
        rw [abs_pow, abs_neg]
        exact pow_le_one₀ (abs_nonneg _) hc
      calc
        _ ≤ (F.card * δ) * 1 :=
          mul_le_mul (hmom F (mem_powerset.mp hF)) hpow (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hδ)
        _ = _ := mul_one _
    _ = _ := (sum_mul _ _ _).symm

def fourListsEquiv (I J X : Type*) :
    ((I × Bool) ⊕ (J × Bool) → X) ≃ ((I → X) × (I → X)) × ((J → X) × (J → X)) where
  toFun z := ((fun i => z (.inl (i, false)), fun i => z (.inl (i, true))),
    (fun j => z (.inr (j, false)), fun j => z (.inr (j, true))))
  invFun z := fun w => match w with
    | .inl (i, false) => z.1.1 i
    | .inl (i, true) => z.1.2 i
    | .inr (j, false) => z.2.1 j
    | .inr (j, true) => z.2.2 j
  left_inv z := by funext w; rcases w with ⟨i, b⟩ | ⟨j, b⟩ <;> cases b <;> rfl
  right_inv z := rfl

lemma expect_fourLists {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]
    [DecidableEq I] [DecidableEq J]
    (H : (I → X) → (I → X) → (J → X) → (J → X) → ℝ) :
    (𝔼 z : (I × Bool) ⊕ (J × Bool) → X,
      H (fun i => z (.inl (i, false))) (fun i => z (.inl (i, true)))
        (fun j => z (.inr (j, false))) (fun j => z (.inr (j, true)))) =
      𝔼 x : I → X, 𝔼 x' : I → X, 𝔼 y : J → X, 𝔼 y' : J → X, H x x' y y' := by
  classical
  calc
    _ = 𝔼 z : ((I → X) × (I → X)) × ((J → X) × (J → X)),
        H z.1.1 z.1.2 z.2.1 z.2.2 :=
      Fintype.expect_equiv (fourListsEquiv I J X) _ _ (fun _ => rfl)
    _ = _ := by simp_rw [← univ_product_univ, expect_product]

lemma list_four_cycle {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) :
    |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card)| ≤
      32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let S : Finset (Bool × Bool) := univ
  let K (ab : Bool × Bool) (z : (I × Bool) ⊕ (J × Bool) → ZMod p) :=
    listKernel E dir (fun i => z (.inl (i, ab.1))) (fun j => z (.inr (j, ab.2)))
  have h := centered_product_moment_bound S univ_nonempty K
    (c := (1 / 2 : ℝ) ^ E.card) (δ := E.card * ((Real.sqrt p + 1) / (2 * p)))
    (by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num))
    (by positivity) (fun F _ => by
      have h := copied_graph_count hp E dir F
      simpa only [K, pow_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h)
  have hsum : (∑ F ∈ S.powerset, (F.card : ℝ)) = 32 := by
    rw [sum_powerset_apply_card]
    norm_num [S, Fintype.card_prod, Fintype.card_bool, sum_range_succ, Nat.choose]
  rw [hsum] at h
  have heq : (𝔼 z : (I × Bool) ⊕ (J × Bool) → ZMod p,
      ∏ ab ∈ S, (K ab z - (1 / 2 : ℝ) ^ E.card)) =
      𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card) := by
    rw [← expect_fourLists]
    apply expect_congr rfl
    intro z _
    simp only [S, K, Fintype.prod_prod_type, Fintype.prod_bool]
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

lemma square_delta_le {p : ℕ} [Fact p.Prime] :
    (Real.sqrt p + 1) / (2 * p) ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt Fact.out).le
  have hs : (1 : ℝ) ≤ Real.sqrt p := by simpa using Real.sqrt_le_sqrt hp1
  rw [show -(1 : ℝ) / 2 = 1 / 2 - 1 by norm_num, Real.rpow_sub hp,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith

lemma list_mixing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (f : (I → ZMod p) → ℝ) (g : (J → ZMod p) → ℝ) :
    |𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p,
      f x * (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) * g y| ≤
      (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
        Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2) := by
  let B (x : I → ZMod p) (y : J → ZMod p) :=
    listKernel E dir x y - (1 / 2 : ℝ) ^ E.card
  let C : ℝ := (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCp : C ^ 4 = 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) := by
    dsimp [C]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have ht := list_four_cycle hp E dir
  have ht' : (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        B x y * B x y' * B x' y * B x' y') ≤ C ^ 4 := by
    calc
      _ ≤ |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          B x y * B x y' * B x' y * B x' y'| := le_abs_self _
      _ ≤ 32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := ht
      _ ≤ 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left square_delta_le (by positivity)
      _ = _ := hCp.symm
  have hF : 0 ≤ 𝔼 x : I → ZMod p, (f x) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have hG : 0 ≤ 𝔼 y : J → ZMod p, (g y) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have h4 : (𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p, f x * B x y * g y) ^ 4 ≤
      (C * Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by
    calc
      _ ≤ (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
          𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
            B x y * B x y' * B x' y * B x' y') *
          (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := four_cycle_bound B f g
      _ ≤ C ^ 4 * (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by gcongr
      _ = _ := by
        have hf4 : (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 =
            (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hF]
        have hg4 : (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 =
            (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hG]
        calc
          _ = C ^ 4 * (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 *
              (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by rw [hf4, hg4]
          _ = _ := by ring
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  have habs (a : ℝ) : |a| ^ 4 = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  simpa only [habs] using h4

lemma posSemidef_entrywise_pow {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => A i j ^ k).PosSemidef := by
  induction k with
  | zero => simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | succ k hk => simpa [Matrix.hadamard, pow_succ] using hk.hadamard hA

lemma posSemidef_entrywise_exp {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of fun i j => Real.exp (A i j)).PosSemidef := by
  classical
  let T (n : ℕ) : Matrix I I ℝ :=
    ∑ k ∈ range n, (Nat.factorial k : ℝ)⁻¹ • (Matrix.of fun i j => A i j ^ k)
  have hT (n : ℕ) : (T n).PosSemidef := by
    exact Matrix.posSemidef_sum (range n) fun k _ =>
      (posSemidef_entrywise_pow hA k).smul (by positivity)
  have ht (i j : I) : Filter.Tendsto (fun n => T n i j)
      Filter.atTop (nhds (Real.exp (A i j))) := by
    simpa [T, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    rw [show A j i = A i j by simpa using hA.isHermitian.apply i j]
  · have ht' : Filter.Tendsto (fun n => star v ⬝ᵥ (T n).mulVec v)
        Filter.atTop (nhds (star v ⬝ᵥ (Matrix.of fun i j => Real.exp (A i j)).mulVec v)) := by
      simp only [dotProduct, Matrix.mulVec]
      apply tendsto_finsetSum
      intro i _
      apply Filter.Tendsto.const_mul
      apply tendsto_finsetSum
      intro j _
      exact (ht i j).mul_const _
    apply ge_of_tendsto ht'
    exact Filter.Eventually.of_forall fun n =>
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hT n)).2 v

lemma posSemidef_entrywise_prod {I L : Type*} [Fintype I]
    (s : Finset L) (A : L → Matrix I I ℝ) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => ∏ l ∈ s, A l i j).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | @insert l s hl hs =>
    simpa [prod_insert hl, Matrix.hadamard] using
      (hA l (mem_insert_self _ _)).hadamard
        (hs fun k hk => hA k (mem_insert_of_mem hk))

lemma posSemidef_product_gap {I L : Type*} [Fintype I]
    (s : Finset L) (a : L → ℝ) (A : L → Matrix I I ℝ)
    (ha : ∀ l ∈ s, 0 ≤ a l) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => (∏ l ∈ s, (1 + a l * A l i j)) -
      (∏ l ∈ s, a l) * (∏ l ∈ s, A l i j)).PosSemidef := by
  classical
  have hOne : (Matrix.of fun _ _ : I => (1 : ℝ)).PosSemidef := by
    simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  induction s using Finset.induction_on with
  | empty =>
    convert (Matrix.PosSemidef.zero : (0 : Matrix I I ℝ).PosSemidef) using 1
    ext i j
    simp
  | @insert l s hl hs =>
    have hal := ha l (mem_insert_self _ _)
    have hAl := hA l (mem_insert_self _ _)
    have has : ∀ k ∈ s, 0 ≤ a k := fun k hk => ha k (mem_insert_of_mem hk)
    have hAs : ∀ k ∈ s, (A k).PosSemidef := fun k hk => hA k (mem_insert_of_mem hk)
    have hfactors (k : L) (hk : k ∈ s) :
        (Matrix.of fun i j => 1 + a k * A k i j).PosSemidef := by
      convert hOne.add ((hAs k hk).smul (has k hk)) using 1
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply]
    have hc := posSemidef_entrywise_prod s
      (fun k => Matrix.of fun i j => 1 + a k * A k i j) hfactors
    have hd := hc.add ((hAl.hadamard (hs has hAs)).smul hal)
    convert hd using 1
    ext i j
    simp only [Matrix.of_apply, prod_insert hl, Matrix.add_apply, Matrix.smul_apply,
      Matrix.hadamard_apply, smul_eq_mul]
    ring

lemma posSemidef_equality {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) : (Matrix.of fun i j => if f i = f j then (1 : ℝ) else 0).PosSemidef := by
  have hd : (Matrix.diagonal (fun _ : J => (1 : ℝ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => zero_le_one)
  simpa [Matrix.submatrix, Matrix.diagonal_apply] using hd.submatrix f

lemma posSemidef_exp_agreement_gap {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (κ : ℝ) (hκ : 0 ≤ κ) :
    (Matrix.of fun j k : I → J =>
      Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      (Real.exp κ - 1) ^ Fintype.card I * (if j = k then 1 else 0)).PosSemidef := by
  classical
  have h := posSemidef_product_gap (univ : Finset I) (fun _ => Real.exp κ - 1)
    (fun x => Matrix.of fun j k : I → J => if j x = k x then (1 : ℝ) else 0)
    (fun _ _ => sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ))
    (fun x _ => posSemidef_equality (fun j : I → J => j x))
  convert h using 1
  ext j k
  simp only [Matrix.of_apply, prod_const, card_univ, prod_boole, mem_univ, forall_true_left]
  simp only [← funext_iff]
  congr 1
  rw [mul_sum, Real.exp_sum]
  apply prod_congr rfl
  intro x _
  split_ifs with hx <;> simp

lemma posSemidef_gram {I K : Type*} [Fintype I] [Fintype K]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (v : K → I → ℝ) :
    (Matrix.of fun j k => ∑ x : I, ∑ y : I, v j x * A x y * v k y).PosSemidef := by
  convert hA.mul_mul_conjTranspose_same (Matrix.of v) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    sum_mul]
  rw [sum_comm]

noncomputable def indexCross {I J : Type*} [Fintype I] [DecidableEq J]
    (A : Matrix I I ℝ) (j k : I → J) : ℝ :=
  ∑ x : I, ∑ y : I, A x y * (if j x = k y then 1 else 0)

lemma posSemidef_indexCross {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of (indexCross (J := J) A)).PosSemidef := by
  classical
  have h (a : J) := posSemidef_gram hA (fun j : I → J =>
    fun x => if j x = a then (1 : ℝ) else 0)
  convert Matrix.posSemidef_sum univ (fun a _ => h a) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.sum_apply, indexCross]
  symm
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp [ite_mul, mul_ite, eq_comm]

lemma indexCross_sub_scalar_one {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (j k : I → J) :
    indexCross (A - κ • 1) j k = indexCross A j k -
      κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0 := by
  simp only [indexCross, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, sub_mul, sum_sub_distrib]
  congr 1
  have hxy (x y : I) : κ * (if x = y then (1 : ℝ) else 0) *
      (if j x = k y then 1 else 0) =
      if y = x then κ * (if j x = k x then 1 else 0) else 0 := by
    by_cases h : y = x
    · subst y; simp
    · simp [h, Ne.symm h]
  simp_rw [hxy]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [mul_sum]

lemma exponential_index_matrix_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) :
    (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      (Real.exp κ - 1) ^ Fintype.card I • 1).PosSemidef := by
  classical
  let lam := (Real.exp κ - 1) ^ Fintype.card I
  let D := Matrix.of (indexCross (J := J) (A - κ • 1))
  let R := Matrix.of (fun j k => Real.exp (D j k))
  have hD : D.PosSemidef := posSemidef_indexCross hA
  have hR : R.PosSemidef := posSemidef_entrywise_exp hD
  have hlam : 0 ≤ lam := pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _
  have hdiag : (Matrix.diagonal (fun j => lam * (R j j - 1))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    apply mul_nonneg hlam
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hD.diag_nonneg)
  let E := Matrix.of fun j k : I → J =>
    Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      lam * (if j = k then 1 else 0)
  have hE : E.PosSemidef := posSemidef_exp_agreement_gap κ hκ
  have hmat : (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      lam • 1) = E.hadamard R + Matrix.diagonal (fun j => lam * (R j j - 1)) := by
    ext j k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.add_apply, Matrix.hadamard_apply, Matrix.diagonal_apply, smul_eq_mul]
    have he : Real.exp (indexCross A j k) =
        Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) * R j k := by
      dsimp [R, D]
      rw [indexCross_sub_scalar_one, Real.exp_sub]
      field_simp
    rw [he]
    dsimp only [E, Matrix.of_apply]
    by_cases hjk : j = k
    · subst k
      simp only [ite_true]
      ring
    · simp only [hjk, ite_false, mul_zero, sub_zero, add_zero]
  change (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
    lam • (1 : Matrix (I → J) (I → J) ℝ)).PosSemidef
  rw [hmat]
  exact (hE.hadamard hR).add hdiag

lemma posSemidef_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ A i i) : A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hμ : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    change hA.eigenvalues i ∈ spectrum ℝ (Matrix.toLinAlgEquiv' A)
    rw [AlgEquiv.spectrum_eq]
    exact hA.eigenvalues_mem_spectrum_real i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  simp only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] at hk
  have ht := (abs_le.mp hk).1
  have hd := hdom k
  change 0 ≤ hA.eigenvalues i
  linarith

lemma matrix_gap_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (κ : ℝ)
    (hdom : ∀ i, κ + ∑ j ∈ univ.erase i, |A i j| ≤ A i i) :
    (A - κ • 1).PosSemidef := by
  apply posSemidef_of_diagonal_dominance
    (hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
  intro i
  calc
    ∑ j ∈ univ.erase i, |(A - κ • 1) i j| = ∑ j ∈ univ.erase i, |A i j| := by
      apply sum_congr rfl
      intro j hj
      have hji := (mem_erase.mp hj).1
      simp [Matrix.sub_apply, Matrix.smul_apply, Ne.symm hji]
    _ ≤ A i i - κ := by linarith [hdom i]
    _ = (A - κ • 1) i i := by simp

lemma matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (v : I → ℝ) :
    lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * C i j * v j := by
  have h := hC.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  have hid : star v ⬝ᵥ (lam • (1 : Matrix I I ℝ)).mulVec v = lam * ∑ i, (v i) ^ 2 := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hc : star v ⬝ᵥ C.mulVec v = ∑ i, ∑ j, v i * C i j * v j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, mul_sum, mul_assoc]
  rw [hid, hc] at h
  linarith

end SquareDifference
end

end OAI
