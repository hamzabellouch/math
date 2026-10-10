import OAI.Combinatorics.SquareDifference.MixedEnergy

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

lemma weighted_matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (hlam : 0 ≤ lam)
    (a f : I → ℝ) (ha : ∀ i, 1 ≤ a i) :
    lam * ∑ i, (f i) ^ 2 ≤ ∑ i, ∑ j, (a i * f i) * C i j * (a j * f j) := by
  calc
    lam * ∑ i, (f i) ^ 2 ≤ lam * ∑ i, (a i * f i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hlam
      apply sum_le_sum
      intro i _
      have ha2 : 0 ≤ (a i) ^ 2 - 1 := by nlinarith [ha i]
      nlinarith [mul_nonneg ha2 (sq_nonneg (f i))]
    _ ≤ _ := matrix_lower_quadratic hC _

lemma marked_index_average {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) (a f : (I → J) → ℝ) (ha : ∀ j, 1 ≤ a j) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I → J, 𝔼 k : I → J,
        (a j * f j) * Real.exp (indexCross A j k) * (a k * f k) := by
  classical
  have h := weighted_matrix_lower_quadratic (exponential_index_matrix_lower A κ hκ hA)
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _) a f ha
  have hd := div_le_div_of_nonneg_right h
    (sq_nonneg (Fintype.card (I → J) : ℝ))
  simp only [Matrix.of_apply] at hd
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow, ← sum_div,
    div_div] at hd ⊢
  convert hd using 1 <;> first | rfl | ring

abbrev WordVertex (B : Type*) (h : ℕ) := B → Equiv.Perm (Fin h)

abbrev PositionPair (h : ℕ) := {p : Fin h × Fin h // p.1 < p.2}

def vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) : WordVertex B h :=
  Function.update v b (v b * Equiv.swap p.1.1 p.1.2)

def reflect {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) : WordVertex B h :=
  Function.update v b (Equiv.swap α β * v b)

def cutPlus {B : Type*} {h : ℕ} (b : B) (α β : Fin h) (v : WordVertex B h) : Prop :=
  (v b).symm α < (v b).symm β

instance cutPlusDecidable {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :
    DecidablePred (cutPlus b α β) :=
  fun v => inferInstanceAs (Decidable ((v b).symm α < (v b).symm β))

lemma vertexSwap_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (p : PositionPair h) : Function.Involutive (fun v : WordVertex B h => vertexSwap v b p) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [vertexSwap, mul_assoc]
  · simp [vertexSwap, hab]

lemma reflect_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Function.Involutive (reflect b α β) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [reflect, ← mul_assoc]
  · simp [reflect, hab]

lemma reflect_vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (p : PositionPair h) (v : WordVertex B h) :
    reflect b α β (vertexSwap v c p) = vertexSwap (reflect b α β v) c p := by
  ext a
  by_cases hab : a = b <;> by_cases hac : a = c <;>
    simp_all [reflect, vertexSwap, mul_assoc]

lemma reflect_cutPlus {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ (v b).symm β < (v b).symm α := by
  simp [cutPlus, reflect, Equiv.Perm.mul_def]

lemma reflect_ne_self {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) (v : WordVertex B h) :
    reflect b α β v ≠ v := by
  intro heq
  have hh := congrArg (fun w : WordVertex B h => w b ((v b).symm α)) heq
  simp [reflect, Equiv.Perm.mul_apply] at hh
  exact hαβ hh.symm

lemma swap_reverse_gap {h : ℕ} (i j a b : Fin h) (hij : i < j) (hab : a < b)
    (hrev : Equiv.swap a b j < Equiv.swap a b i) (hnot : ¬ (a = i ∧ b = j)) :
    j.val - i.val + 1 ≤ b.val - a.val := by
  simp only [Equiv.swap_apply_def] at hrev
  split_ifs at hrev <;> subst_vars <;> simp_all <;> omega

lemma vertexSwap_symm_apply {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) (α : Fin h) :
    (vertexSwap v b p b).symm α = Equiv.swap p.1.1 p.1.2 ((v b).symm α) := by
  simp [vertexSwap, Equiv.Perm.mul_def]

lemma reflect_eq_positional {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (α β : Fin h) (hp : cutPlus b α β v) :
    reflect b α β v = vertexSwap v b ⟨((v b).symm α, (v b).symm β), hp⟩ := by
  ext a x
  by_cases hab : a = b
  · subst a
    simp only [reflect, vertexSwap, Function.update_self, Equiv.Perm.mul_apply]
    have hh := Equiv.trans_swap_trans_symm α β (v b)
    have hh' := congrArg (fun e : Fin h ≃ Fin h => (v b) (e x)) hh
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg Fin.val hh'
  · simp [reflect, vertexSwap, hab]

lemma ordered_swap_injective {h : ℕ} :
    Function.Injective (fun p : PositionPair h => Equiv.swap p.1.1 p.1.2) := by
  intro p q heq
  change Equiv.swap p.1.1 p.1.2 = Equiv.swap q.1.1 q.1.2 at heq
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have h1 : p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 := by
    apply Equiv.eq_or_eq_of_swap_apply_ne_self
    rw [← heq, Equiv.swap_apply_left]
    exact hp.symm
  have h2 : p.1.2 = q.1.1 ∨ p.1.2 = q.1.2 := by
    apply Equiv.eq_or_eq_of_swap_apply_ne_self
    rw [← heq, Equiv.swap_apply_right]
    exact hp
  apply Subtype.ext
  apply Prod.ext <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first | assumption | omega

lemma vertexSwap_ne_self {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) : vertexSwap v b p ≠ v := by
  intro heq
  have hh := congrArg (fun w : WordVertex B h => w b p.1.1) heq
  simp only [vertexSwap, Function.update_self, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left] at hh
  exact (ne_of_lt p.2).symm ((v b).injective hh)

lemma vertexSwap_generator_injective {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) :
    Function.Injective (fun bp : B × PositionPair h => vertexSwap v bp.1 bp.2) := by
  rintro ⟨b, p⟩ ⟨c, q⟩ heq
  have hbc : b = c := by
    by_contra hbc
    have hh := congrArg (fun w : WordVertex B h => w b p.1.1) heq
    simp only [vertexSwap, Function.update_self, Function.update_of_ne hbc,
      Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hh
    exact (ne_of_lt p.2).symm ((v b).injective hh)
  subst c
  have hh := congrArg (fun w : WordVertex B h => w b) heq
  simp only [vertexSwap, Function.update_self] at hh
  exact Prod.ext rfl (ordered_swap_injective (mul_left_cancel hh))

noncomputable def interaction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) : ℝ :=
  ∑ b ∈ S, ∑ p : PositionPair h,
    if w = vertexSwap v b p then δ ^ (p.1.2.val - p.1.1.val) else 0

lemma interaction_nonneg {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (v w : WordVertex B h) :
    0 ≤ interaction S δ v w := by
  unfold interaction
  positivity

lemma interaction_self {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v : WordVertex B h) : interaction S δ v v = 0 := by
  classical
  simp [interaction, Ne.symm (vertexSwap_ne_self v _ _)]

lemma interaction_neighbour {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v : WordVertex B h) (b : B) (hb : b ∈ S)
    (p : PositionPair h) :
    interaction S δ v (vertexSwap v b p) = δ ^ (p.1.2.val - p.1.1.val) := by
  classical
  simp only [interaction, show ∀ c q, (vertexSwap v b p = vertexSwap v c q) ↔
      b = c ∧ p = q by
    intro c q
    constructor
    · intro hh
      have hpair : (b, p) = (c, q) := vertexSwap_generator_injective v hh
      exact Prod.mk.inj hpair
    · rintro ⟨rfl, rfl⟩
      rfl]
  simp only [ite_and]
  simp [hb]

lemma interaction_eq_zero_of_not_neighbour {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h)
    (hw : ∀ b ∈ S, ∀ p : PositionPair h, w ≠ vertexSwap v b p) :
    interaction S δ v w = 0 := by
  classical
  apply sum_eq_zero
  intro b hb
  exact sum_eq_zero fun p _ => ite_eq_right (hw b hb p)

lemma interaction_symm {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) :
    interaction S δ v w = interaction S δ w v := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro p _
  simp only [show (w = vertexSwap v b p) ↔ (v = vertexSwap w b p) from
    ⟨fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p v)).symm,
     fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p w)).symm⟩]

lemma interaction_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) (v w : WordVertex B h) :
    interaction S δ (reflect b α β v) (reflect b α β w) = interaction S δ v w := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro p _
  simp only [← reflect_vertexSwap, (reflect_involutive b α β).injective.eq_iff]

lemma cross_gap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (x y : WordVertex B h)
    (hx : cutPlus b α β x) (hy : cutPlus b α β y) (hxy : y ≠ x)
    (p : PositionPair h) (heq : reflect b α β y = vertexSwap x c p) :
    b = c ∧ ((x b).symm β).val - ((x b).symm α).val + 1 ≤ p.1.2.val - p.1.1.val := by
  have hrev : (vertexSwap x c p b).symm β < (vertexSwap x c p b).symm α := by
    rw [← heq]
    simpa [reflect, cutPlus, Equiv.Perm.mul_def] using hy
  have hbc : b = c := by
    by_contra hn
    simp only [vertexSwap, Function.update_of_ne hn] at hrev
    exact lt_asymm hx hrev
  subst c
  refine ⟨rfl, ?_⟩
  rw [vertexSwap_symm_apply, vertexSwap_symm_apply] at hrev
  apply swap_reverse_gap _ _ _ _ hx p.2 hrev
  rintro ⟨ha, hb⟩
  apply hxy
  apply (reflect_involutive b α β).injective
  rw [heq, reflect_eq_positional x b α β hx]
  congr 1
  apply Subtype.ext
  exact Prod.ext ha hb

abbrev CutHalf {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :=
  {v : WordVertex B h // cutPlus b α β v}

noncomputable def crossInteraction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    Matrix (CutHalf b α β) (CutHalf b α β) ℝ :=
  Matrix.of fun x y => interaction S δ x.1 (reflect b α β y.1)

lemma crossInteraction_symmetric {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    (crossInteraction S δ b α β).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, crossInteraction, Matrix.of_apply]
  calc
    interaction S δ y.1 (reflect b α β x.1) =
        interaction S δ (reflect b α β y.1) x.1 := by
      rw [← interaction_reflect S δ b α β y.1 (reflect b α β x.1),
        reflect_involutive b α β x.1]
    _ = interaction S δ x.1 (reflect b α β y.1) := interaction_symm _ _ _ _

lemma crossInteraction_diagonal_lower {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val) ≤
      crossInteraction S δ b α β x x := by
  classical
  let p : PositionPair h := ⟨((x.1 b).symm α, (x.1 b).symm β), x.2⟩
  let f (c : B) (q : PositionPair h) : ℝ :=
    if reflect b α β x.1 = vertexSwap x.1 c q then δ ^ (q.1.2.val - q.1.1.val) else 0
  have hf (c : B) (q : PositionPair h) : 0 ≤ f c q :=
    ite_nonneg (pow_nonneg hδ _) le_rfl
  have hp : f b p ≤ ∑ q : PositionPair h, f b q :=
    single_le_sum (fun q _ => hf b q) (mem_univ p)
  have hb' : (∑ q : PositionPair h, f b q) ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q :=
    single_le_sum (fun c _ => sum_nonneg fun q _ => hf c q) hb
  change δ ^ _ ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q
  refine le_trans ?_ (hp.trans hb')
  dsimp [f]
  rw [ite_eq_left (reflect_eq_positional x.1 b α β x.2)]

lemma crossInteraction_generator_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b c : B)
    (α β : Fin h) (x : CutHalf b α β) (p : PositionPair h) :
    ∑ y ∈ univ.erase x, (if reflect b α β y.1 = vertexSwap x.1 c p then
      δ ^ (p.1.2.val - p.1.1.val) else 0) ≤
    if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
  classical
  by_cases hex : ∃ y ∈ (univ : Finset (CutHalf b α β)).erase x,
      reflect b α β y.1 = vertexSwap x.1 c p
  · obtain ⟨y, hy, heq⟩ := hex
    have hyx : y.1 ≠ x.1 := fun hh => (mem_erase.mp hy).1 (Subtype.ext hh)
    obtain ⟨hbc, hgap⟩ := cross_gap b c α β x.1 y.1 x.2 y.2 hyx p heq
    subst c
    rw [ite_eq_left rfl]
    calc
      _ = δ ^ (p.1.2.val - p.1.1.val) := by
        rw [sum_eq_single y, ite_eq_left heq]
        · intro z _ hzy
          rw [ite_eq_right]
          intro hz
          apply hzy
          apply Subtype.ext
          exact (reflect_involutive b α β).injective (hz.trans heq.symm)
        · exact fun hn => False.elim (hn hy)
      _ ≤ _ := pow_le_pow_of_le_one hδ hδ1 hgap
  · have hz : ∀ y ∈ (univ : Finset (CutHalf b α β)).erase x,
        reflect b α β y.1 ≠ vertexSwap x.1 c p := by simpa using hex
    rw [sum_eq_zero (fun y hy => ite_eq_right (hz y hy))]
    split_ifs <;> positivity

lemma crossInteraction_offdiag_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    ∑ y ∈ univ.erase x, |crossInteraction S δ b α β x y| ≤
      (h : ℝ) ^ 2 * δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
  classical
  simp only [crossInteraction, Matrix.of_apply]
  simp_rw [abs_of_nonneg (interaction_nonneg S hδ _ _)]
  unfold interaction
  rw [sum_comm]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  calc
    _ ≤ ∑ c ∈ S, ∑ _p : PositionPair h,
        if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
      apply sum_le_sum
      intro c hc
      apply sum_le_sum
      intro p hp
      exact crossInteraction_generator_bound hδ hδ1 b c α β x p
    _ = (Fintype.card (PositionPair h) : ℝ) *
        δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
      simp [sum_ite_eq', hb]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
      have hc : Fintype.card (PositionPair h) ≤ h ^ 2 := by
        have hh := Fintype.card_subtype_le (fun p : Fin h × Fin h => p.1 < p.2)
        simpa [Fintype.card_prod, pow_two] using hh
      exact_mod_cast hc

lemma crossInteraction_diagonal_dominance {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : (h : ℝ) ^ 2 * δ = 1 / 10) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    (9 / 10 : ℝ) * δ ^ (h - 1) + ∑ y ∈ univ.erase x,
      |crossInteraction S δ b α β x y| ≤ crossInteraction S δ b α β x x := by
  classical
  let g := ((x.1 b).symm β).val - ((x.1 b).symm α).val
  have hg : g ≤ h - 1 := by
    have hh := ((x.1 b).symm β).isLt
    dsimp [g]
    omega
  have hpow : δ ^ (h - 1) ≤ δ ^ g := pow_le_pow_of_le_one hδ hδ1 hg
  have hoff := crossInteraction_offdiag_bound S hδ hδ1 b hb α β x
  have hdiag := crossInteraction_diagonal_lower S hδ b hb α β x
  have heq : (h : ℝ) ^ 2 * δ ^ (g + 1) = (1 / 10 : ℝ) * δ ^ g := by
    rw [pow_succ]
    calc
      (h : ℝ) ^ 2 * (δ ^ g * δ) = ((h : ℝ) ^ 2 * δ) * δ ^ g := by ring
      _ = _ := by rw [hscale]
  change _ ≤ (h : ℝ) ^ 2 * δ ^ (g + 1) at hoff
  rw [heq] at hoff
  linarith

def tupleH : ℕ := 24

def tupleT : ℕ := 80

def tupleBlocks : ℕ := 2 * tupleT + 1

noncomputable def tupleDelta : ℝ := 1 / (10 * (tupleH : ℝ) ^ 2)

noncomputable def tupleKappa : ℝ := (9 / 10) * tupleDelta ^ (tupleH - 1)

lemma tupleDelta_pos : 0 < tupleDelta := by norm_num [tupleDelta, tupleH]

lemma tupleDelta_le_one : tupleDelta ≤ 1 := by norm_num [tupleDelta, tupleH]

lemma tupleDelta_scale : (tupleH : ℝ) ^ 2 * tupleDelta = 1 / 10 := by
  norm_num [tupleDelta, tupleH]

lemma tupleKappa_pos : 0 < tupleKappa := by
  unfold tupleKappa
  exact mul_pos (by norm_num) (pow_pos tupleDelta_pos _)

lemma cutPlus_reflect_iff_not {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ ¬ cutPlus b α β v := by
  rw [reflect_cutPlus]
  have hne : (v b).symm α ≠ (v b).symm β := (v b).symm.injective.ne hαβ
  exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans (or_iff_left hne)))

noncomputable def halfSumEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    CutHalf b α β ⊕ CutHalf b α β ≃ WordVertex B h where
  toFun := Sum.elim Subtype.val (fun v => reflect b α β v.1)
  invFun := fun v => if hp : cutPlus b α β v then Sum.inl ⟨v, hp⟩ else
    Sum.inr ⟨reflect b α β v, (cutPlus_reflect_iff_not b hαβ v).mpr hp⟩
  left_inv := by
    rintro (x | x)
    · simp [x.2]
    · have hn : ¬ cutPlus b α β (reflect b α β x.1) := by
        rw [cutPlus_reflect_iff_not b hαβ]
        exact not_not.mpr x.2
      simp [hn]
      exact Subtype.ext (reflect_involutive b α β x.1)
  right_inv := by
    intro v
    by_cases hv : cutPlus b α β v
    · simp [hv]
    · simp only [dite_eq_right hv, Sum.elim_inr]
      exact reflect_involutive b α β v

lemma card_cutHalf {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    2 * Fintype.card (CutHalf b α β) = (Nat.factorial h) ^ Fintype.card B := by
  classical
  have hh := Fintype.card_congr (halfSumEquiv b hαβ)
  simpa [Fintype.card_sum, Fintype.card_fun, Fintype.card_perm, two_mul] using hh

def addressEdge {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (u v : B → G) : Prop :=
  T ≤ (univ.filter fun b => v b = u b * c).card

lemma addressEdge_irrefl {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ≠ 1) {T : ℕ} (hT : 0 < T) (u : B → G) : ¬ addressEdge c T u u := by
  have hh (b : B) : u b ≠ u b * c := by
    intro hh
    apply hc
    exact (mul_left_cancel (show u b * c = u b * 1 by simpa using hh.symm))
  simp [addressEdge, hh, hT.not_ge]

lemma addressEdge_asymm {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ^ 2 ≠ 1) {T : ℕ} (hT : Fintype.card B < 2 * T)
    {u v : B → G} (huv : addressEdge c T u v) : ¬ addressEdge c T v u := by
  classical
  intro hvu
  let s := univ.filter fun b : B => v b = u b * c
  let t := univ.filter fun b : B => u b = v b * c
  have hdis : Disjoint s t := by
    rw [disjoint_left]
    intro b hbs hbt
    have hs : v b = u b * c := (mem_filter.mp hbs).2
    have ht : u b = v b * c := (mem_filter.mp hbt).2
    apply hc
    apply mul_left_cancel (a := u b)
    calc
      u b * c ^ 2 = (u b * c) * c := by rw [pow_two, mul_assoc]
      _ = u b := by rw [← hs, ← ht]
      _ = u b * 1 := (mul_one _).symm
  have hcard : s.card + t.card ≤ Fintype.card B := by
    rw [← card_union_of_disjoint hdis]
    exact card_le_univ _
  change T ≤ s.card at huv
  change T ≤ t.card at hvu
  omega

lemma addressEdge_left_translate {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (a u v : B → G) :
    addressEdge c T (fun b => a b * u b) (fun b => a b * v b) ↔ addressEdge c T u v := by
  simp only [addressEdge, mul_assoc, mul_right_inj]

lemma addressEdge_mono_blocks {B C G : Type*} [Fintype B] [Fintype C]
    [DecidableEq G] [Group G] (c : G) (T : ℕ) (f : B ↪ C) (u v : C → G)
    (hedge : addressEdge c T (u ∘ f) (v ∘ f)) : addressEdge c T u v := by
  classical
  apply le_trans hedge
  apply card_le_card_of_injOn f
  · intro b hb
    simpa using hb
  · exact f.injective.injOn

lemma addressEdge_full_shift {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (hT : T ≤ Fintype.card B) (u : B → G) :
    addressEdge c T u (fun b => u b * c) := by
  simpa [addressEdge] using hT

lemma crossInteraction_gap {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (b : B) (hb : b ∈ S) (α β : Fin tupleH) :
    (crossInteraction S tupleDelta b α β - tupleKappa • 1).PosSemidef := by
  classical
  apply matrix_gap_of_diagonal_dominance (crossInteraction_symmetric S tupleDelta b α β)
  exact crossInteraction_diagonal_dominance S tupleDelta_pos.le tupleDelta_le_one
    tupleDelta_scale b hb α β

lemma marked_interaction_index_average {B : Type*} [Fintype B] [DecidableEq B]
    {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset B) (b : B) (hb : b ∈ S) (α β : Fin tupleH)
    (a f : (CutHalf b α β → J) → ℝ) (ha : ∀ j, 1 ≤ a j) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card J : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 j : CutHalf b α β → J, (f j) ^ 2) ≤
      𝔼 j : CutHalf b α β → J, 𝔼 k : CutHalf b α β → J,
        (a j * f j) * Real.exp (indexCross (crossInteraction S tupleDelta b α β) j k) *
          (a k * f k) := by
  exact marked_index_average _ tupleKappa tupleKappa_pos.le
    (crossInteraction_gap S b hb α β) a f ha

end SquareDifference
end

end OAI
