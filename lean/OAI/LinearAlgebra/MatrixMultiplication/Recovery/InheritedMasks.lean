import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section ClassWords

variable {C : Type*} (P A : C → Type*)
  [∀ c, Fintype (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev ClassWords := ∀ c, P c → A c

def SameClassOrbit (w v : ClassWords P A) : Prop :=
  ∃ e : ∀ c, Equiv.Perm (P c), ∀ c, w c ∘ e c = v c

omit [∀ label, Fintype (A label)] in
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

omit [∀ label, Fintype (A label)] in
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

variable {P A B : Type*} [Fintype P] [DecidableEq A] [DecidableEq B]

noncomputable def empiricalLaw (w : P → A) (a : A) : ℝ :=
  (wordPopulation w a : ℝ) / Fintype.card P

def typeWindow (ν : A → ℝ) (η : ℝ) (w : P → A) : Prop :=
  ∀ a, |empiricalLaw w a - ν a| ≤ η

theorem typeWindow_permutation (ν : A → ℝ) (η : ℝ) (w : P → A)
    (e : Equiv.Perm P) : typeWindow ν η (w ∘ e) ↔ typeWindow ν η w := by
  simp [typeWindow, empiricalLaw, wordPopulation_reindex]

theorem wordPopulation_equiv (w : P → A) (e : A ≃ B) (a : A) :
    wordPopulation (e ∘ w) (e a) = wordPopulation w a := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => e.injective.eq_iff

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

end OAI
