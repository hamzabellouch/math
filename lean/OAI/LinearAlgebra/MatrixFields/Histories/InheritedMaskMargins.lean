import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.CompleteWordPair
import OAI.LinearAlgebra.MatrixFields.Entropy.FiniteAverage
import OAI.LinearAlgebra.MatrixFields.Extraction.JointPairClassWindows
import OAI.LinearAlgebra.MatrixFields.Histories.InverseLinearRecovery

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section ClassWords

variable {C : Type*} (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev ClassWords := ∀ c, P c → A c

def SameClassOrbit (w v : ClassWords P A) : Prop :=
  ∃ e : ∀ c, Equiv.Perm (P c), ∀ c, w c ∘ e c = v c

omit [∀ c, DecidableEq (P c)] [∀ c, Fintype (A c)] in
theorem sameClassOrbit_iff (w v : ClassWords P A) :
    SameClassOrbit P A w v ↔
      ∀ c a, wordPopulation (v c) a = wordPopulation (w c) a := by
  constructor
  · rintro ⟨e, he⟩ c a
    rw [← he c]
    exact wordPopulation_reindex (w c) (e c) a
  · intro h
    have he : ∀ c, ∃ e : Equiv.Perm (P c), w c ∘ e = v c :=
      fun c => (samePopulation_iff_permutation (w c) (v c)).mp (h c)
    choose e he using he
    exact ⟨e, he⟩

abbrev Profile := ∀ c, A c → Fin (Fintype.card (P c) + 1)

noncomputable def profile (w : ClassWords P A) : Profile P A :=
  fun c a => ⟨wordPopulation (w c) a,
    Nat.lt_succ_of_le (Fintype.card_subtype_le _)⟩

omit [∀ c, DecidableEq (P c)] [∀ c, Fintype (A c)] in
theorem profile_eq_iff (w v : ClassWords P A) :
    profile P A w = profile P A v ↔ SameClassOrbit P A w v := by
  rw [sameClassOrbit_iff]
  constructor
  · intro h c a
    have hh := congrArg (fun f : Profile P A => (f c a).val) h
    exact hh.symm
  · intro h
    funext c a
    apply Fin.ext
    exact (h c a).symm

omit [∀ c, DecidableEq (P c)] in
theorem card_profile [Fintype C] [DecidableEq C] :
    Fintype.card (Profile P A) =
      ∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (A c) := by
  simp [Profile, Fintype.card_pi]

end ClassWords

section TensorAction

variable {F C : Type*} [CommSemiring F] [Fintype C]
  {P X Y Z : C → Type*} [∀ c, Fintype (P c)]

def classProduct (T : ∀ c, Tensor F (X c) (Y c) (Z c)) :
    Tensor F (∀ c, P c → X c) (∀ c, P c → Y c) (∀ c, P c → Z c) :=
  fun x y z => ∏ c, ∏ i, T c (x c i) (y c i) (z c i)

theorem classProduct_permutation
    (T : ∀ c, Tensor F (X c) (Y c) (Z c))
    (e : ∀ c, Equiv.Perm (P c))
    (x : ∀ c, P c → X c) (y : ∀ c, P c → Y c) (z : ∀ c, P c → Z c) :
    classProduct T (fun c => x c ∘ e c) (fun c => y c ∘ e c)
      (fun c => z c ∘ e c) = classProduct T x y z := by
  apply Finset.prod_congr rfl
  intro c _
  exact Equiv.prod_comp (e c) (fun i => T c (x c i) (y c i) (z c i))

end TensorAction

theorem statisticPopulation_permutation {P A B : Type*}
    [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (w : P → A) (statistic : A → B) (e : Equiv.Perm P) (b : B) :
    wordPopulation (statistic ∘ w ∘ e) b = wordPopulation (statistic ∘ w) b :=
  wordPopulation_reindex (statistic ∘ w) e b

section EmpiricalWindows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def empiricalLaw (w : P → A) (a : A) : ℝ :=
  (wordPopulation w a : ℝ) / Fintype.card P

def typeWindow (ν : A → ℝ) (η : ℝ) (w : P → A) : Prop :=
  ∀ a, |empiricalLaw w a - ν a| ≤ η

omit [DecidableEq P] [Fintype A] in
theorem typeWindow_permutation (ν : A → ℝ) (η : ℝ) (w : P → A)
    (e : Equiv.Perm P) : typeWindow ν η (w ∘ e) ↔ typeWindow ν η w := by
  simp [typeWindow, empiricalLaw, wordPopulation_reindex]

omit [DecidableEq P] [Fintype A] [Fintype B] in
theorem wordPopulation_equiv (w : P → A) (e : A ≃ B) (a : A) :
    wordPopulation (e ∘ w) (e a) = wordPopulation w a := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => e.injective.eq_iff

omit [DecidableEq P] [Fintype A] [Fintype B] in
theorem typeWindow_equiv (ν : A → ℝ) (η : ℝ) (w : P → A) (e : A ≃ B) :
    typeWindow (ν ∘ e.symm) η (e ∘ w) ↔ typeWindow ν η w := by
  constructor
  · intro h a
    have hh := h (e a)
    simpa [empiricalLaw, wordPopulation_equiv] using hh
  · intro h b
    obtain ⟨a, rfl⟩ := e.surjective b
    simpa [empiricalLaw, wordPopulation_equiv] using h a

end EmpiricalWindows

section Windows

variable {I : Type*} [Fintype I]

theorem weighted_window (w x : I → ℝ) (μ η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hx : ∀ i, |x i - μ| ≤ η) :
    |(∑ i, w i * x i) - μ| ≤ η := by
  have heq : (∑ i, w i * x i) - μ = ∑ i, w i * (x i - μ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [heq]
  calc
    |∑ i, w i * (x i - μ)| ≤ ∑ i, |w i * (x i - μ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |x i - μ| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * η := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)
    _ = η := by rw [← Finset.sum_mul, hsum, one_mul]

theorem product_coordinate_error {a b a' b' τ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb' : 0 ≤ b') (hb1' : b' ≤ 1)
    (hea : |a - a'| ≤ τ) (heb : |b - b'| ≤ τ) :
    |a * b - a' * b'| ≤ 2 * τ := by
  have ht : 0 ≤ τ := le_trans (abs_nonneg _) hea
  have heq : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [heq]
  calc
    |a * (b - b') + (a - a') * b'| ≤ |a * (b - b')| + |(a - a') * b'| := abs_add_le _ _
    _ = a * |b - b'| + |a - a'| * b' := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb']
    _ ≤ a * τ + τ * b' := add_le_add
      (mul_le_mul_of_nonneg_left heb ha) (mul_le_mul_of_nonneg_right hea hb')
    _ ≤ 2 * τ := by nlinarith

theorem inherited_margin {actual expected prescribed η τ α : ℝ}
    (hchild : |expected - prescribed| ≤ 2 * τ)
    (happrox : |actual - expected| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    |actual - prescribed| ≤ η / 2 := by
  calc
    |actual - prescribed| = |(actual - expected) + (expected - prescribed)| := by ring_nf
    _ ≤ |actual - expected| + |expected - prescribed| := abs_add_le _ _
    _ ≤ α + 2 * τ := add_le_add happrox hchild
    _ ≤ η / 2 := by linarith

end Windows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section Pushforward

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

def pushforwardLaw (statistic : A → B) (ν : A → ℝ) (b : B) : ℝ :=
  ∑ a with statistic a = b, ν a

omit [DecidableEq A] in
theorem pushforwardLaw_nonneg (statistic : A → B) (ν : A → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (b : B) : 0 ≤ pushforwardLaw statistic ν b := by
  exact Finset.sum_nonneg fun a _ => hν a

omit [DecidableEq A] in
theorem pushforwardLaw_le_one (statistic : A → B) (ν : A → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hsum : ∑ a, ν a = 1) (b : B) :
    pushforwardLaw statistic ν b ≤ 1 := by
  calc
    pushforwardLaw statistic ν b ≤ ∑ a, ν a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => hν a)
    _ = 1 := hsum

end Pushforward

section Windows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq P] [Fintype B] in
theorem wordPopulation_statistic (w : P → A) (statistic : A → B) (b : B) :
    wordPopulation (statistic ∘ w) b =
      ∑ a with statistic a = b, wordPopulation w a := by
  simpa only [wordPopulation, Fintype.card_subtype, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.comp_apply] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset P)
      (Finset.univ.filter fun a => statistic a = b) w).symm

omit [DecidableEq P] [Fintype B] in
theorem empiricalLaw_statistic (w : P → A) (statistic : A → B) (b : B) :
    empiricalLaw (statistic ∘ w) b =
      pushforwardLaw statistic (empiricalLaw w) b := by
  simp only [empiricalLaw, wordPopulation_statistic, pushforwardLaw,
    Nat.cast_sum, Finset.sum_div]

omit [DecidableEq P] [Fintype A] in
theorem typeWindow_mono (ν : A → ℝ) (w : P → A) {τ η : ℝ}
    (hτη : τ ≤ η) (hw : typeWindow ν τ w) : typeWindow ν η w := by
  intro a
  exact (hw a).trans hτη

omit [DecidableEq P] [Fintype B] in
theorem typeWindow_statistic_coordinate (ν : A → ℝ) (τ : ℝ) (w : P → A)
    (statistic : A → B) (hw : typeWindow ν τ w) (b : B) :
    |empiricalLaw (statistic ∘ w) b - pushforwardLaw statistic ν b| ≤
      ((Finset.univ.filter fun a => statistic a = b).card : ℝ) * τ := by
  rw [empiricalLaw_statistic]
  unfold pushforwardLaw
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a with statistic a = b, |empiricalLaw w a - ν a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.univ.filter (fun a => statistic a = b), τ :=
      Finset.sum_le_sum fun a _ => hw a
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq P] [Fintype B] in
theorem typeWindow_statistic (ν : A → ℝ) (τ : ℝ) (w : P → A)
    (statistic : A → B) (hτ : 0 ≤ τ) (hw : typeWindow ν τ w) :
    typeWindow (pushforwardLaw statistic ν) (Fintype.card A * τ)
      (statistic ∘ w) := by
  intro b
  calc
    _ ≤ ((Finset.univ.filter fun a => statistic a = b).card : ℝ) * τ :=
      typeWindow_statistic_coordinate ν τ w statistic hw b
    _ ≤ Fintype.card A * τ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) hτ

end Windows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.PermutationMatching
open MatrixMultiplication.InheritedMasks

namespace MatrixMultiplication.HistorySymmetry

variable {C : Type*} {P X Y : C → Type*}

def completeWordPairEquiv : CompleteWordPair P X Y ≃
    ((∀ c, P c → X c) × (∀ c, P c → Y c)) where
  toFun w := (w.left, w.right)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance completeWordPairFintype
    [Fintype C] [DecidableEq C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] : Fintype (CompleteWordPair P X Y) :=
  Fintype.ofEquiv _ completeWordPairEquiv.symm

theorem card_completeWordPair
    [Fintype C] [DecidableEq C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] :
    Fintype.card (CompleteWordPair P X Y) =
      (∏ c, Fintype.card (X c) ^ Fintype.card (P c)) *
      ∏ c, Fintype.card (Y c) ^ Fintype.card (P c) := by
  rw [Fintype.card_congr completeWordPairEquiv]
  simp

section Coefficients

variable {K : Type*} [CommSemiring K] [Fintype C] [∀ c, Fintype (P c)]
    {XL YL ZL XR YR ZR : C → Type*}

def pairClassProduct
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c)) :
    Tensor K (CompleteWordPair P XL XR) (CompleteWordPair P YL YR) (CompleteWordPair P ZL ZR) :=
  fun x y z => classProduct TL x.left y.left z.left * classProduct TR x.right y.right z.right

theorem pairClassProduct_smul
    (TL : ∀ c, Tensor K (XL c) (YL c) (ZL c))
    (TR : ∀ c, Tensor K (XR c) (YR c) (ZR c))
    (g : HalfClassPermutations P)
    (x : CompleteWordPair P XL XR) (y : CompleteWordPair P YL YR)
    (z : CompleteWordPair P ZL ZR) :
    pairClassProduct TL TR (g • x) (g • y) (g • z) = pairClassProduct TL TR x y z := by
  change classProduct TL (fun c => x.left c ∘ (g.1 c).symm)
      (fun c => y.left c ∘ (g.1 c).symm) (fun c => z.left c ∘ (g.1 c).symm) *
    classProduct TR (fun c => x.right c ∘ (g.2 c).symm)
      (fun c => y.right c ∘ (g.2 c).symm) (fun c => z.right c ∘ (g.2 c).symm) = _
  rw [classProduct_permutation, classProduct_permutation]
  rfl

end Coefficients

section Windows

variable [Fintype C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    {SL SR : C → Type*} [∀ c, Fintype (SL c)] [∀ c, Fintype (SR c)]
    [∀ c, DecidableEq (SL c)] [∀ c, DecidableEq (SR c)]

def childWindows (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  ∀ c, typeWindow (νl c) (ηl c) (sl c ∘ w.left c) ∧
    typeWindow (νr c) (ηr c) (sr c ∘ w.right c)

omit [Fintype C] [∀ c, DecidableEq (P c)] [∀ c, Fintype (SL c)]
  [∀ c, Fintype (SR c)] in
theorem childWindows_smul
    (sl : ∀ c, X c → SL c) (sr : ∀ c, Y c → SR c)
    (νl : ∀ c, SL c → ℝ) (νr : ∀ c, SR c → ℝ) (ηl ηr : C → ℝ)
    (g : HalfClassPermutations P) (w : CompleteWordPair P X Y) :
    childWindows sl sr νl νr ηl ηr (g • w) ↔ childWindows sl sr νl νr ηl ηr w := by
  unfold childWindows
  change (∀ c, typeWindow (νl c) (ηl c) ((sl c ∘ w.left c) ∘ (g.1 c).symm) ∧
    typeWindow (νr c) (ηr c) ((sr c ∘ w.right c) ∘ (g.2 c).symm)) ↔ _
  simp only [typeWindow_permutation]

end Windows

theorem delete_invariant {K G U V W : Type*} [CommSemiring K] [Group G]
    [MulAction G U] [MulAction G V] [MulAction G W]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hQ : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    (hx : ∀ (g : G) x, px (g • x) ↔ px x)
    (hy : ∀ (g : G) y, py (g • y) ↔ py y)
    (hz : ∀ (g : G) z, pz (g • z) ↔ pz z)
    (g : G) (x : U) (y : V) (z : W) :
    ExactRecovery.delete Q px py pz (g • x) (g • y) (g • z) =
      ExactRecovery.delete Q px py pz x y z := by
  simp only [ExactRecovery.delete, hx, hy, hz, hQ]

theorem delete_used_left {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (x : U)
    (h : ∃ y z, ExactRecovery.delete Q px py pz x y z ≠ 0) : px x := by
  obtain ⟨y, z, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

theorem delete_used_middle {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (y : V)
    (h : ∃ x z, ExactRecovery.delete Q px py pz x y z ≠ 0) : py y := by
  obtain ⟨x, z, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

theorem delete_used_right {K U V W : Type*} [CommSemiring K]
    (Q : Tensor K U V W) (px : U → Prop) (py : V → Prop) (pz : W → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz] (z : W)
    (h : ∃ x y, ExactRecovery.delete Q px py pz x y z ≠ 0) : pz z := by
  obtain ⟨x, y, h⟩ := h
  by_contra hn
  simp [ExactRecovery.delete, hn] at h

end MatrixMultiplication.HistorySymmetry

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [DecidableEq P]

def membership (B : Finset P) (p : Equiv.Perm P) (i : P) : ℝ :=
  if p i ∈ B then 1 else 0

@[simp] theorem membership_sq (B : Finset P) (p : Equiv.Perm P) (i : P) :
    membership B p i * membership B p i = membership B p i := by
  simp only [membership]
  split_ifs <;> norm_num

theorem membership_nonneg (B : Finset P) (p : Equiv.Perm P) (i : P) :
    0 ≤ membership B p i := by
  simp only [membership]
  split_ifs <;> norm_num

theorem membership_le_one (B : Finset P) (p : Equiv.Perm P) (i : P) :
    membership B p i ≤ 1 := by
  simp only [membership]
  split_ifs <;> norm_num

variable [Fintype P]

theorem sum_membership (B : Finset P) (p : Equiv.Perm P) :
    (∑ i : P, membership B p i) = (B.card : ℝ) := by
  unfold membership
  rw [Equiv.sum_comp p (fun i => if i ∈ B then (1 : ℝ) else 0)]
  simp

theorem sum_perm_right (f : Equiv.Perm P → ℝ) (q : Equiv.Perm P) :
    (∑ p : Equiv.Perm P, f (p * q)) = ∑ p : Equiv.Perm P, f p := by
  exact Equiv.sum_comp (Equiv.mulRight q) f

theorem sum_membership_position_eq (B : Finset P) (i j : P) :
    (∑ p : Equiv.Perm P, membership B p i) =
      ∑ p : Equiv.Perm P, membership B p j := by
  calc
    _ = ∑ p : Equiv.Perm P, membership B (p * Equiv.swap i j) j := by
      simp [membership, Equiv.Perm.mul_apply]
    _ = _ := sum_perm_right (fun p => membership B p j) _

theorem card_mul_sum_membership (B : Finset P) (i : P) :
    (Fintype.card P : ℝ) * (∑ p : Equiv.Perm P, membership B p i) =
      (Fintype.card (Equiv.Perm P) : ℝ) * B.card := by
  calc
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p i := by simp
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p j := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_membership_position_eq B i j
    _ = ∑ p : Equiv.Perm P, ∑ j : P, membership B p j := Finset.sum_comm
    _ = _ := by simp [sum_membership]

theorem average_membership [Nonempty P] (B : Finset P) (i : P) :
    average (fun p : Equiv.Perm P => membership B p i) =
      (B.card : ℝ) / Fintype.card P := by
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp hn).2
  simpa only [mul_comm] using card_mul_sum_membership B i

theorem sum_membership_mul_position_eq (B : Finset P) {i j k : P}
    (hij : i ≠ j) (hik : i ≠ k) :
    (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ∑ p : Equiv.Perm P, membership B p i * membership B p k := by
  calc
    _ = ∑ p : Equiv.Perm P,
        membership B (p * Equiv.swap j k) i *
          membership B (p * Equiv.swap j k) k := by
      simp [membership, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hij hik]
    _ = _ := sum_perm_right (fun p => membership B p i * membership B p k) _

theorem card_sub_one_mul_sum_membership_mul (B : Finset P) {i j : P}
    (hij : i ≠ j) :
    ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ((B.card : ℝ) - 1) * (∑ p : Equiv.Perm P, membership B p i) := by
  have hcard : (((Finset.univ : Finset P).erase i).card : ℝ) =
      (Fintype.card P : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_erase_add_one (Finset.mem_univ i))
    simp only [Nat.cast_add, Nat.cast_one, Finset.card_univ] at h
    linarith
  have herase :
      (∑ k ∈ (Finset.univ : Finset P).erase i,
        ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) := by
    calc
      _ = ∑ k ∈ (Finset.univ : Finset P).erase i,
          ∑ p : Equiv.Perm P, membership B p i * membership B p j := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_membership_mul_position_eq B (Finset.mem_erase.mp hk).1.symm hij
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have htotal :
      (∑ k : P, ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      (B.card : ℝ) * (∑ p : Equiv.Perm P, membership B p i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_membership]
    rw [← Finset.sum_mul, mul_comm]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset P)
    (fun k => ∑ p : Equiv.Perm P, membership B p i * membership B p k)
    (Finset.mem_univ i)
  rw [herase, htotal] at hsplit
  simp only [membership_sq] at hsplit
  nlinarith only [hsplit]

theorem average_membership_mul_of_ne (B : Finset P) {i j : P} (hij : i ≠ j) :
    average (fun p : Equiv.Perm P => membership B p i * membership B p j) =
      (B.card : ℝ) * ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  have hnlarge : 1 < Fintype.card P := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hnlarge' : (1 : ℝ) < Fintype.card P := by exact_mod_cast hnlarge
  have hn : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp (mul_ne_zero hn hn1)).2
  calc
    _ = (Fintype.card P : ℝ) * (((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j)) := by ring
    _ = (Fintype.card P : ℝ) * (((B.card : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i)) := by
      rw [card_sub_one_mul_sum_membership_mul B hij]
    _ = ((B.card : ℝ) - 1) * ((Fintype.card P : ℝ) *
        (∑ p : Equiv.Perm P, membership B p i)) := by ring
    _ = ((B.card : ℝ) - 1) * ((Fintype.card (Equiv.Perm P) : ℝ) * B.card) := by
      rw [card_mul_sum_membership B i]
    _ = _ := by ring

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

def matchingCount (A B : Finset P) (p : Equiv.Perm P) : ℝ :=
  ∑ i ∈ A, membership B p i

theorem average_matchingCount [Nonempty P] (A B : Finset P) :
    average (matchingCount A B) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) := by
  unfold matchingCount
  rw [average_finset_sum]
  simp only [average_membership, Finset.sum_const, nsmul_eq_mul]
  ring

theorem average_matchingCount_sq [Nonempty P] (A B : Finset P) :
    average (fun p => matchingCount A B p ^ 2) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) +
      (A.card : ℝ) * ((A.card : ℝ) - 1) * (B.card : ℝ) *
        ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  let u : ℝ := (B.card : ℝ) / (Fintype.card P : ℝ)
  let v : ℝ := (B.card : ℝ) * ((B.card : ℝ) - 1) /
    ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1))
  have hpair (i j : P) :
      average (fun p => membership B p i * membership B p j) =
        v + if i = j then u - v else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [membership_sq]
      rw [average_membership]
      dsimp [u]
      ring
    · rw [average_membership_mul_of_ne B hij]
      simp [hij, v]
  have hsq (p : Equiv.Perm P) : matchingCount A B p ^ 2 =
      ∑ i ∈ A, ∑ j ∈ A, membership B p i * membership B p j := by
    unfold matchingCount
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [average_finset_sum]
  simp_rw [average_finset_sum, hpair]
  have hinner (i : P) (hi : i ∈ A) :
      (∑ j ∈ A, (v + (if i = j then u - v else 0))) =
        (A.card : ℝ) * v + (u - v) := by
    rw [Finset.sum_add_distrib]
    simp [hi]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [u, v]
  ring

theorem matchingCount_variance [Nonempty P] (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) =
      (A.card : ℝ) * ((Fintype.card P : ℝ) - (A.card : ℝ)) *
        (B.card : ℝ) * ((Fintype.card P : ℝ) - (B.card : ℝ)) /
        ((Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1)) := by
  rw [average_centered_sq, average_matchingCount_sq, average_matchingCount]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hn0 : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn0, hn1]
  ring

theorem matchingCount_variance_le (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) ≤
      (Fintype.card P : ℝ) / 8 := by
  have : Nonempty P := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hn)
  rw [matchingCount_variance A B hn]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have ha : (A.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ A
  have hb : (B.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ B
  have ha0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hna : 0 ≤ (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) :=
    mul_nonneg ha0 (sub_nonneg.mpr ha)
  have hnb : 0 ≤ (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) :=
    mul_nonneg hb0 (sub_nonneg.mpr hb)
  have hqa : (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((A.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hqb : (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((B.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hprod := mul_le_mul hqa hqb hnb (by positivity :
    (0 : ℝ) ≤ (Fintype.card P : ℝ) ^ 2 / 4)
  have hn3 : 0 ≤ (Fintype.card P : ℝ) ^ 3 * ((Fintype.card P : ℝ) - 2) :=
    mul_nonneg (by positivity) (by linarith)
  have hn1pos : (0 : ℝ) < (Fintype.card P : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < Fintype.card P := by linarith
  apply (div_le_iff₀ (show (0 : ℝ) <
    (Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1) by positivity)).mpr
  nlinarith only [hprod, hn3]

noncomputable def statisticPositions {A B : Type*} (w : P → A)
    (statistic : A → B) (b : B) : Finset P := by
  classical
  exact Finset.univ.filter fun i => statistic (w i) = b

noncomputable def statisticMatchingCount {A B S T : Type*}
    (left : P → A) (right : P → B) (sl : A → S) (sr : B → T)
    (s : S) (t : T) : Equiv.Perm P → ℝ :=
  matchingCount (statisticPositions left sl s) (statisticPositions right sr t)

theorem statisticMatchingCount_variance_le {A B S T : Type*}
    (left : P → A) (right : P → B) (sl : A → S) (sr : B → T)
    (s : S) (t : T) (hn : 2 ≤ Fintype.card P) :
    average (fun p =>
      (statisticMatchingCount left right sl sr s t p -
        average (statisticMatchingCount left right sl sr s t)) ^ 2) ≤
      (Fintype.card P : ℝ) / 8 :=
  matchingCount_variance_le _ _ hn

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

variable {P : Type*} [Fintype P] [DecidableEq P]

def twoHalfCount (A B : Finset P) (left right : Equiv.Perm P) : ℝ :=
  ∑ i : P, if left i ∈ A ∧ right i ∈ B then 1 else 0

theorem twoHalfCount_eq_matchingCount (A B : Finset P)
    (left right : Equiv.Perm P) :
    twoHalfCount A B left right =
      matchingCount A B (left.symm.trans right) := by
  classical
  unfold twoHalfCount matchingCount membership
  calc
    _ = ∑ i : P, if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.sum_comp left (fun i =>
          if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0)
    _ = ∑ i : P, if i ∈ A then
        (if right (left.symm i) ∈ B then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by
      simp only [Equiv.trans_apply, Finset.sum_ite_mem_eq]
      rfl

def relativePairEquiv :
    (Equiv.Perm P × Equiv.Perm P) ≃ (Equiv.Perm P × Equiv.Perm P) where
  toFun lr := (lr.1, lr.1.symm.trans lr.2)
  invFun lq := (lq.1, lq.1.trans lq.2)
  left_inv := by
    rintro ⟨left, right⟩
    dsimp only
    apply Prod.ext
    · rfl
    · ext i
      simp
  right_inv := by
    rintro ⟨left, relative⟩
    dsimp only
    apply Prod.ext
    · rfl
    · ext i
      simp

theorem average_relativePerm (f : Equiv.Perm P → ℝ) :
    average (fun lr : Equiv.Perm P × Equiv.Perm P =>
      f (lr.1.symm.trans lr.2)) = average f := by
  calc
    _ = average (fun lq : Equiv.Perm P × Equiv.Perm P => f lq.2) :=
      average_equiv relativePairEquiv (fun lq => f lq.2)
    _ = _ := average_prod_snd f

theorem average_twoHalfCount (A B : Finset P) (f : ℝ → ℝ) :
    average (fun lr : Equiv.Perm P × Equiv.Perm P =>
      f (twoHalfCount A B lr.1 lr.2)) =
      average (fun p : Equiv.Perm P => f (matchingCount A B p)) := by
  simp_rw [twoHalfCount_eq_matchingCount]
  exact average_relativePerm (fun p => f (matchingCount A B p))

theorem twoHalfCount_statisticPositions {X Y S T : Type*}
    (leftWord : P → X) (rightWord : P → Y) (sl : X → S) (sr : Y → T)
    (s : S) (t : T) (left right : Equiv.Perm P) :
    twoHalfCount (statisticPositions leftWord sl s)
        (statisticPositions rightWord sr t) left right =
      ∑ i : P, if sl (leftWord (left i)) = s ∧ sr (rightWord (right i)) = t
        then (1 : ℝ) else 0 := by
  classical
  simp [twoHalfCount, statisticPositions]

section Families

variable {C : Type*} (Q : C → Type*)

def relativeFamily
    (left right : ∀ c, Equiv.Perm (Q c)) : ∀ c, Equiv.Perm (Q c) :=
  fun c => (left c).symm.trans (right c)

def relativeFamilyPairEquiv :
    ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) ≃
      ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) where
  toFun lr := (lr.1, relativeFamily Q lr.1 lr.2)
  invFun lq := (lq.1, fun c => (lq.1 c).trans (lq.2 c))
  left_inv := by
    rintro ⟨left, right⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]
  right_inv := by
    rintro ⟨left, relative⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]

variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (Q c)] [∀ c, DecidableEq (Q c)]

theorem average_relativeFamily (f : (∀ c, Equiv.Perm (Q c)) → ℝ) :
    average (fun lr :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) =>
      f (relativeFamily Q lr.1 lr.2)) = average f := by
  calc
    _ = average (fun lq :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) => f lq.2) :=
      average_equiv (relativeFamilyPairEquiv Q) (fun lq => f lq.2)
    _ = _ := average_prod_snd f

omit [DecidableEq C] in
theorem sum_twoHalfCount_eq_matchingCount
    (A B : ∀ c, Finset (Q c)) (left right : ∀ c, Equiv.Perm (Q c)) :
    (∑ c, twoHalfCount (A c) (B c) (left c) (right c)) =
      ∑ c, matchingCount (A c) (B c) (relativeFamily Q left right c) := by
  simp only [twoHalfCount_eq_matchingCount, relativeFamily]

end Families

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

section ClassProducts

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

abbrev ClassPermutations (P : C → Type*) := ∀ c, Equiv.Perm (P c)

def populationSize (P : C → Type*) [∀ c, Fintype (P c)] : ℝ :=
  ∑ c, (Fintype.card (P c) : ℝ)

def totalMatchingCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P) : ℝ :=
  ∑ c, matchingCount (A c) (B c) (p c)

def totalMatchingMean (A B : ∀ c, Finset (P c)) : ℝ :=
  ∑ c, average (matchingCount (A c) (B c))

theorem average_totalMatchingCount (A B : ∀ c, Finset (P c)) :
    average (totalMatchingCount A B) = totalMatchingMean A B := by
  classical
  unfold totalMatchingCount totalMatchingMean
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact average_pi_eval (X := fun c => Equiv.Perm (P c)) c
    (matchingCount (A c) (B c))

omit [DecidableEq C] in
theorem totalMatchingMean_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) :
    totalMatchingMean A B =
      ∑ c, ((A c).card : ℝ) * ((B c).card : ℝ) / (Fintype.card (P c) : ℝ) := by
  classical
  unfold totalMatchingMean
  apply Finset.sum_congr rfl
  intro c _
  exact average_matchingCount (A c) (B c)

theorem totalMatchingCount_variance_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) :
    average (fun p : ClassPermutations P =>
      (totalMatchingCount A B p - totalMatchingMean A B) ^ 2) ≤
        populationSize P / 8 := by
  classical
  calc
    _ = ∑ c, average (fun p : Equiv.Perm (P c) =>
        (matchingCount (A c) (B c) p - average (matchingCount (A c) (B c))) ^ 2) := by
      simpa only [totalMatchingCount, totalMatchingMean, Finset.sum_sub_distrib]
        using average_pi_sum_centered_sq (fun c => matchingCount (A c) (B c))
    _ ≤ ∑ c, (Fintype.card (P c) : ℝ) / 8 :=
      Finset.sum_le_sum fun c _ => matchingCount_variance_le (A c) (B c) (hn c)
    _ = populationSize P / 8 := by rw [← Finset.sum_div]; rfl

theorem totalMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (δ : ℝ) (hδ : 0 < δ) :
    average (fun p : ClassPermutations P =>
      if δ ≤ |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) ≤
        populationSize P / (8 * δ ^ 2) := by
  classical
  have h := (deviation_bound (totalMatchingCount A B) (totalMatchingMean A B) δ hδ).trans
    (totalMatchingCount_variance_le A B hn)
  calc
    _ ≤ (populationSize P / 8) / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 h
    _ = _ := by rw [div_div]

theorem normalizedMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η : ℝ) (hη : 0 < η) :
    average (fun p : ClassPermutations P =>
      if η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  have hδ : 0 < populationSize P * η / 2 := by positivity
  calc
    _ ≤ average (fun p : ClassPermutations P =>
        if populationSize P * η / 2 ≤
          |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) := by
      apply average_mono
      intro p
      have hi : η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| →
          populationSize P * η / 2 ≤
            |totalMatchingCount A B p - totalMatchingMean A B| := by
        intro hp
        rw [← sub_div, abs_div, abs_of_pos hm] at hp
        have hh := (le_div_iff₀ hm).mp hp
        nlinarith
      split_ifs <;> simp_all
    _ ≤ populationSize P / (8 * (populationSize P * η / 2) ^ 2) :=
      totalMatchingCount_deviation_le A B hn _ hδ
    _ = _ := by
      field_simp [ne_of_gt hm, ne_of_gt hη]
      ring

theorem inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P =>
      if η < |totalMatchingCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  refine le_trans (average_mono ?_) (normalizedMatchingCount_deviation_le A B hn hm η hη)
  intro p
  have hi : η < |totalMatchingCount A B p / populationSize P - ν| →
      η / 2 ≤ |totalMatchingCount A B p / populationSize P -
        totalMatchingMean A B / populationSize P| := by
    intro hp
    have ht : |totalMatchingCount A B p / populationSize P - ν| ≤
        |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| +
        |totalMatchingMean A B / populationSize P - ν| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (totalMatchingCount A B p / populationSize P - totalMatchingMean A B / populationSize P)
        (totalMatchingMean A B / populationSize P - ν)
    linarith
  split_ifs <;> simp_all

theorem finite_inheritedMask_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P =>
      if ∃ i, η i < |totalMatchingCount (A i) (B i) p / populationSize P - ν i|
        then 1 else 0) ≤ ∑ i, 1 / (2 * populationSize P * (η i) ^ 2) := by
  classical
  refine le_trans (average_indicator_exists_le_sum _) ?_
  exact Finset.sum_le_sum fun i _ =>
    inheritedMask_rejection_le (A i) (B i) hn hm (η i) (ν i) (hη i) (hmargin i)

theorem pushforward_sum_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η : ℝ) (ν : I → ℝ) (hη : 0 < η)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤
      (η / Fintype.card I) / 2) :
    average (fun p : ClassPermutations P =>
      if η < |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) - ∑ i, ν i|
        then 1 else 0) ≤
          ∑ _i : I, 1 / (2 * populationSize P * (η / Fintype.card I) ^ 2) := by
  classical
  by_cases hIcard : Fintype.card I = 0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.mp hIcard
    simp [not_lt.mpr (le_of_lt hη)]
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hIcard)
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have htol : 0 < η / (Fintype.card I : ℝ) := div_pos hη hcard
  refine le_trans (average_mono ?_)
    (finite_inheritedMask_rejection_le A B hn hm (fun _ => η / Fintype.card I)
      ν (fun _ => htol) hmargin)
  intro p
  have hi : η < |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) -
      ∑ i, ν i| →
      ∃ i, η / Fintype.card I <
        |totalMatchingCount (A i) (B i) p / populationSize P - ν i| := by
    intro hp
    by_contra h
    push Not at h
    have he : |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) -
        ∑ i, ν i| ≤ η := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i, |totalMatchingCount (A i) (B i) p / populationSize P - ν i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : I, η / Fintype.card I := Finset.sum_le_sum fun i _ => h i
        _ = η := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp [ne_of_gt hcard]
    linarith
  split_ifs <;> simp_all

def totalTwoHalfCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  ∑ c, twoHalfCount (A c) (B c) (p.1 c) (p.2 c)

theorem average_totalTwoHalfCount_test (A B : ∀ c, Finset (P c)) (f : ℝ → ℝ) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      f (totalTwoHalfCount A B p)) =
        average (fun p : ClassPermutations P => f (totalMatchingCount A B p)) := by
  calc
    _ = average (fun p : ClassPermutations P × ClassPermutations P =>
        f (totalMatchingCount A B (relativeFamily P p.1 p.2))) := by
      apply average_congr
      intro p
      exact congrArg f (sum_twoHalfCount_eq_matchingCount P A B p.1 p.2)
    _ = _ := average_relativeFamily P (fun p => f (totalMatchingCount A B p))

theorem average_totalTwoHalfCounts_test {I : Type*}
    (A B : I → ∀ c, Finset (P c)) (f : (I → ℝ) → ℝ) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      f (fun i => totalTwoHalfCount (A i) (B i) p)) =
        average (fun p : ClassPermutations P =>
          f (fun i => totalMatchingCount (A i) (B i) p)) := by
  calc
    _ = average (fun p : ClassPermutations P × ClassPermutations P =>
        f (fun i => totalMatchingCount (A i) (B i) (relativeFamily P p.1 p.2))) := by
      apply average_congr
      intro p
      apply congrArg f
      funext i
      exact sum_twoHalfCount_eq_matchingCount P (A i) (B i) p.1 p.2
    _ = _ := average_relativeFamily P
      (fun p => f (fun i => totalMatchingCount (A i) (B i) p))

theorem twoHalf_pushforward_sum_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η : ℝ) (ν : I → ℝ) (hη : 0 < η)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤
      (η / Fintype.card I) / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |(∑ i, totalTwoHalfCount (A i) (B i) p / populationSize P) - ∑ i, ν i|
        then 1 else 0) ≤
          ∑ _i : I, 1 / (2 * populationSize P * (η / Fintype.card I) ^ 2) := by
  classical
  rw [average_totalTwoHalfCounts_test A B
    (fun k => if η < |(∑ i, k i / populationSize P) - ∑ i, ν i| then 1 else 0)]
  exact pushforward_sum_rejection_le A B hn hm η ν hη hmargin

theorem twoHalf_inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  rw [average_totalTwoHalfCount_test A B
    (fun k => if η < |k / populationSize P - ν| then 1 else 0)]
  exact inheritedMask_rejection_le A B hn hm η ν hη hmargin

def selectedTwoHalfCount (D : Finset C) (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
    ((fun c => p.1 c), (fun c => p.2 c))

theorem selectedTwoHalfMask_rejection_le (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c)) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean (fun c : D => A c) (fun c : D => B c) /
      populationSize (fun c : D => P c) - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p / populationSize (fun c : D => P c) - ν|
        then 1 else 0) ≤ 1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  classical
  have havg := average_prod_pi_restrict (X := fun c => Equiv.Perm (P c)) D
    (fun p : ClassPermutations (fun c : D => P c) ×
        ClassPermutations (fun c : D => P c) =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c) p /
        populationSize (fun c : D => P c) - ν| then (1 : ℝ) else 0)
  change average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
        ((fun c => p.1 c), (fun c => p.2 c)) /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤ _
  rw [havg]
  exact twoHalf_inheritedMask_rejection_le (P := fun c : D => P c)
    (fun c : D => A c) (fun c : D => B c)
    (fun c : D => hn c c.property) hm η ν hη hmargin

theorem finite_selectedTwoHalfMask_rejection_le {I : Type*} [Fintype I]
    (D : I → Finset C) (A B : I → ∀ c, Finset (P c))
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (hm : ∀ i, 0 < populationSize (fun c : D i => P c))
    (η ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hmargin : ∀ i,
      |totalMatchingMean (fun c : D i => A i c) (fun c : D i => B i c) /
        populationSize (fun c : D i => P c) - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if ∃ i, η i < |selectedTwoHalfCount (D i) (A i) (B i) p /
        populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤
      ∑ i, 1 / (2 * populationSize (fun c : D i => P c) * (η i) ^ 2) := by
  classical
  refine le_trans (average_indicator_exists_le_sum _) ?_
  exact Finset.sum_le_sum fun i _ => selectedTwoHalfMask_rejection_le
    (D i) (A i) (B i) (hn i) (hm i) (η i) (ν i) (hη i) (hmargin i)

theorem inverse_linear_mask_constant {I : Type*} [Fintype I]
    (mass η : I → ℝ) (N : ℝ) :
    (∑ i, 1 / (2 * (mass i * N) * (η i) ^ 2)) =
      (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_div]
  congr 1
  ring

theorem finite_selectedTwoHalfMask_inverse_linear {I : Type*} [Fintype I]
    (D : I → Finset C) (A B : I → ∀ c, Finset (P c))
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass η ν : I → ℝ) (N : ℝ) (hN : 0 < N)
    (hmass : ∀ i, 0 < mass i) (hη : ∀ i, 0 < η i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (hmargin : ∀ i,
      |totalMatchingMean (fun c : D i => A i c) (fun c : D i => B i c) /
        populationSize (fun c : D i => P c) - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if ∃ i, η i < |selectedTwoHalfCount (D i) (A i) (B i) p /
        populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤
      (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  have hm (i : I) : 0 < populationSize (fun c : D i => P c) := by
    rw [hsize]
    exact mul_pos (hmass i) hN
  have h := finite_selectedTwoHalfMask_rejection_le D A B hn hm η ν hη hmargin
  simpa only [hsize, inverse_linear_mask_constant] using h

end ClassProducts

section CompleteSymbols

variable {P A S : Type*} [Fintype P] [DecidableEq P] [DecidableEq S]

omit [DecidableEq P] in
theorem statisticPositions_card [Fintype S]
    (w : P → A) (statistic : A → S) (s : S) :
    (statisticPositions w statistic s).card =
      MatrixMultiplication.Foundation.wordPopulation (statistic ∘ w) s := by
  unfold statisticPositions MatrixMultiplication.Foundation.wordPopulation
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext i
  simp

end CompleteSymbols

section OrbitFractions

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

theorem average_bad_shift_eq_orbit_fraction (x : X) (bad : X → Prop)
    [DecidablePred bad] :
    average (fun g : G => if bad (g • x) then 1 else 0) =
      (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card := by
  rw [average_indicator_eq]
  exact OrbitCounting.bad_shift_fraction x bad

end OrbitFractions

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

section ClassMixtures

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

def classWeight (P : C → Type*) [∀ c, Fintype (P c)] (c : C) : ℝ :=
  (Fintype.card (P c) : ℝ) / populationSize P

def classDensity (A : ∀ c, Finset (P c)) (c : C) : ℝ :=
  ((A c).card : ℝ) / Fintype.card (P c)

def classProductMixture (P : C → Type*) [∀ c, Fintype (P c)]
    (left right : C → ℝ) : ℝ :=
  ∑ c, classWeight P c * (left c * right c)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classWeight_nonneg (hm : 0 < populationSize P) (c : C) :
    0 ≤ classWeight P c := div_nonneg (Nat.cast_nonneg _) (le_of_lt hm)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem sum_classWeight (hm : 0 < populationSize P) :
    ∑ c, classWeight P c = 1 := by
  unfold classWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hm)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_nonneg (A : ∀ c, Finset (P c)) (c : C) :
    0 ≤ classDensity A c := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_le_one [∀ c, Nonempty (P c)]
    (A : ∀ c, Finset (P c)) (c : C) : classDensity A c ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card (P c) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hn).2
  simpa using (Nat.cast_le.mpr (Finset.card_le_univ (A c)) :
    ((A c).card : ℝ) ≤ Fintype.card (P c))

omit [DecidableEq C] in
theorem totalMatchingMean_normalized_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P) :
    totalMatchingMean A B / populationSize P =
      classProductMixture P (classDensity A) (classDensity B) := by
  classical
  rw [totalMatchingMean_eq, Finset.sum_div]
  unfold classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  have hn : (Fintype.card (P c) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := P c)))
  dsimp [classWeight, classDensity]
  field_simp [hn, ne_of_gt hm]

omit [DecidableEq C] in
theorem totalMatchingMean_prescribed_error [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (τ : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ) :
    |totalMatchingMean A B / populationSize P -
      classProductMixture P left right| ≤ 2 * τ := by
  rw [totalMatchingMean_normalized_eq A B hm]
  have h := weighted_window (classWeight P)
    (fun c => classDensity A c * classDensity B c - left c * right c)
    0 (2 * τ) (classWeight_nonneg hm) (sum_classWeight hm) (by
      intro c
      simpa only [sub_zero] using product_coordinate_error
        (classDensity_nonneg A c) (classDensity_le_one A c)
        (hright0 c) (hright1 c) (hleft c) (hright c))
  simpa only [classProductMixture, sub_zero, mul_sub, Finset.sum_sub_distrib] using h

omit [DecidableEq C] in
theorem totalMatchingMean_inherited_margin [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (η τ α ν : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    |totalMatchingMean A B / populationSize P - ν| ≤ η / 2 := by
  have hchild := totalMatchingMean_prescribed_error A B hm left right τ
    hright0 hright1 hleft hright
  have h := inherited_margin (actual := ν)
    (expected := classProductMixture P left right)
    (prescribed := totalMatchingMean A B / populationSize P)
    (by simpa only [abs_sub_comm] using hchild)
    (by simpa only [abs_sub_comm] using happrox) hτ hα
  simpa only [abs_sub_comm] using h

theorem inheritedMask_rejection_of_windows_le [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (left right : C → ℝ) (η τ α ν : ℝ)
    (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P =>
      if η < |totalMatchingCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  exact inheritedMask_rejection_le A B hn hm η ν hη
    (totalMatchingMean_inherited_margin A B hm left right η τ α ν
      hright0 hright1 hleft hright happrox hτ hα)

theorem twoHalf_inheritedMask_rejection_of_windows_le [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (left right : C → ℝ) (η τ α ν : ℝ)
    (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  exact twoHalf_inheritedMask_rejection_le A B hn hm η ν hη
    (totalMatchingMean_inherited_margin A B hm left right η τ α ν
      hright0 hright1 hleft hright happrox hτ hα)

theorem selectedTwoHalfMask_rejection_of_windows_le
    (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (left right : C → ℝ) (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, 0 ≤ right c) (hright1 : ∀ c ∈ D, right c ≤ 1)
    (hleft : ∀ c ∈ D, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c ∈ D, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => left c) (fun c => right c) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤
      1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  let : ∀ c : D, Nonempty (P c) := fun c =>
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) (hn c c.property))
  apply selectedTwoHalfMask_rejection_le D A B hn hm η ν hη
  exact totalMatchingMean_inherited_margin (fun c : D => A c) (fun c : D => B c)
    hm (fun c => left c) (fun c => right c) η τ α ν
    (fun c => hright0 c c.property) (fun c => hright1 c c.property)
    (fun c => hleft c c.property) (fun c => hright c c.property) happrox hτ hα

end ClassMixtures

section CompleteWordStatistics

variable {C : Type*} [Fintype C] [DecidableEq C] {P X Y S T : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
  [∀ c, Fintype (T c)] [∀ c, DecidableEq (T c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_statisticPositions (w : ∀ c, P c → X c)
    (statistic : ∀ c, X c → S c) (s : ∀ c, S c) (c : C) :
    classDensity (fun c => statisticPositions (w c) (statistic c) (s c)) c =
      empiricalLaw (statistic c ∘ w c) (s c) := by
  rw [classDensity, statisticPositions_card, empiricalLaw]

omit [DecidableEq C] in
theorem totalMatchingMean_statistic_eq [∀ c, Nonempty (P c)]
    (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (hm : 0 < populationSize P) :
    totalMatchingMean (fun c => statisticPositions (w c) (leftStat c) (s c))
        (fun c => statisticPositions (v c) (rightStat c) (t c)) / populationSize P =
      classProductMixture P
        (fun c => empiricalLaw (leftStat c ∘ w c) (s c))
        (fun c => empiricalLaw (rightStat c ∘ v c) (t c)) := by
  rw [totalMatchingMean_normalized_eq _ _ hm]
  simp only [classProductMixture, classDensity_statisticPositions]

theorem twoHalf_statistic_rejection_of_typeWindows_le [∀ c, Nonempty (P c)]
    (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (leftLaw : ∀ c, S c → ℝ) (rightLaw : ∀ c, T c → ℝ)
    (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ rightLaw c (t c))
    (hright1 : ∀ c, rightLaw c (t c) ≤ 1)
    (hleft : ∀ c, typeWindow (leftLaw c) τ (leftStat c ∘ w c))
    (hright : ∀ c, typeWindow (rightLaw c) τ (rightStat c ∘ v c))
    (happrox : |classProductMixture P
      (fun c => leftLaw c (s c)) (fun c => rightLaw c (t c)) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount
          (fun c => statisticPositions (w c) (leftStat c) (s c))
          (fun c => statisticPositions (v c) (rightStat c) (t c)) p /
          populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  apply twoHalf_inheritedMask_rejection_of_windows_le _ _ hn hm
    (fun c => leftLaw c (s c)) (fun c => rightLaw c (t c)) η τ α ν hη
    hright0 hright1
  · intro c
    simpa only [classDensity_statisticPositions] using hleft c (s c)
  · intro c
    simpa only [classDensity_statisticPositions] using hright c (t c)
  · exact happrox
  · exact hτ
  · exact hα

theorem selectedTwoHalf_statistic_rejection_of_completeWindows_le
    [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
    [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]
    (D : Finset C) (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (leftLaw : ∀ c, X c → ℝ) (rightLaw : ∀ c, Y c → ℝ)
    (leftε rightε : C → ℝ) (η α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, ∀ y, 0 ≤ rightLaw c y)
    (hrightSum : ∀ c ∈ D, ∑ y, rightLaw c y = 1)
    (hleftε : ∀ c ∈ D, 0 ≤ leftε c) (hrightε : ∀ c ∈ D, 0 ≤ rightε c)
    (hleft : ∀ c ∈ D, typeWindow (leftLaw c) (leftε c) (w c))
    (hright : ∀ c ∈ D, typeWindow (rightLaw c) (rightε c) (v c))
    (hleftFactor : ∀ c ∈ D, (Fintype.card (X c) : ℝ) * leftε c ≤ η / 8)
    (hrightFactor : ∀ c ∈ D, (Fintype.card (Y c) : ℝ) * rightε c ≤ η / 8)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => pushforwardLaw (leftStat c) (leftLaw c) (s c))
      (fun c => pushforwardLaw (rightStat c) (rightLaw c) (t c)) - ν| ≤ α)
    (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D
          (fun c => statisticPositions (w c) (leftStat c) (s c))
          (fun c => statisticPositions (v c) (rightStat c) (t c)) p /
          populationSize (fun c : D => P c) - ν| then 1 else 0) ≤
        1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  apply selectedTwoHalfMask_rejection_of_windows_le D _ _ hn hm
    (fun c => pushforwardLaw (leftStat c) (leftLaw c) (s c))
    (fun c => pushforwardLaw (rightStat c) (rightLaw c) (t c))
    η (η / 8) α ν hη
  · intro c hc
    exact pushforwardLaw_nonneg (rightStat c) (rightLaw c) (hright0 c hc) (t c)
  · intro c hc
    exact pushforwardLaw_le_one (rightStat c) (rightLaw c)
      (hright0 c hc) (hrightSum c hc) (t c)
  · intro c hc
    rw [classDensity_statisticPositions]
    exact (typeWindow_statistic (leftLaw c) (leftε c) (w c) (leftStat c)
      (hleftε c hc) (hleft c hc) (s c)).trans (hleftFactor c hc)
  · intro c hc
    rw [classDensity_statisticPositions]
    exact (typeWindow_statistic (rightLaw c) (rightε c) (v c) (rightStat c)
      (hrightε c hc) (hright c hc) (t c)).trans (hrightFactor c hc)
  · exact happrox
  · exact le_rfl
  · exact hα

end CompleteWordStatistics

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

end OAI
