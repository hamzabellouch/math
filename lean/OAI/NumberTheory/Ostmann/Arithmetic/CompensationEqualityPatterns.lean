import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem value_eq_of_rel {τ : ι → ℕ} (p : Pattern τ)
    (w : ι → κ) (hw : patternOf τ w = p) {i j : ι} (h : p.val.r i j) : w i = w j := by
  cases hw
  exact congrArg Prod.snd h

def collapse {τ : ι → ℕ} (p : Pattern τ)
    (w : {w : ι → κ // patternOf τ w = p}) : BlockDraw p κ := by
  refine ⟨Quotient.lift w.val (fun _ _ h => value_eq_of_rel p w.val w.property h), ?_⟩
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro i j h
  apply Quotient.sound
  have hh : (patternOf τ w.val).val.r i j := h
  exact (congrArg (fun r : Pattern τ => r.val.r i j) w.property).mp hh

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem collapse_label {τ : ι → ℕ} (p : Pattern τ)
    (w : {w : ι → κ // patternOf τ w = p}) (i : ι) :
    (collapse p w).val (label p i) = w.val i := rfl

def fiberEquiv {τ : ι → ℕ} (p : Pattern τ) :
    {w : ι → κ // patternOf τ w = p} ≃ BlockDraw p κ where
  toFun := collapse p
  invFun b := ⟨expand p b, patternOf_expand p b⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    rfl
  right_inv b := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl

theorem sum_eq_patterns [Fintype κ] (τ : ι → ℕ) {A : Type*} [AddCommMonoid A]
    (F : (ι → κ) → A) :
    (∑ w : ι → κ, F w) = ∑ p : Pattern τ, ∑ b : BlockDraw p κ, F (expand p b) := by
  classical
  rw [← Fintype.sum_fiberwise (patternOf τ) F]
  apply Finset.sum_congr rfl
  intro p _
  exact ((fiberEquiv (κ := κ) p).symm.sum_comp (fun w => F w.val)).symm

abbrev Fiber {τ : ι → ℕ} (p : Pattern τ) (q : Block p) := {i : ι // label p i = q}

instance fiberFintype {τ : ι → ℕ} (p : Pattern τ) (q : Block p) : Fintype (Fiber p q) :=
  inferInstanceAs (Fintype {i : ι // label p i = q})

def multiplicity {τ : ι → ℕ} (p : Pattern τ) (q : Block p) : ℕ := Fintype.card (Fiber p q)

omit [Fintype ι] [DecidableEq ι] in
theorem fiber_nonempty {τ : ι → ℕ} (p : Pattern τ) (q : Block p) : Nonempty (Fiber p q) := by
  obtain ⟨i, hi⟩ := label_surjective p q
  exact ⟨i, hi⟩

omit [DecidableEq ι] in
theorem multiplicity_pos {τ : ι → ℕ} (p : Pattern τ) (q : Block p) : 0 < multiplicity p q := by
  let := fiber_nonempty p q
  exact Fintype.card_pos

def blockWeight {τ : ι → ℕ} (p : Pattern τ) (μ : ι → κ → ℝ)
    (q : Block p) (v : κ) : ℝ := ∏ i : Fiber p q, μ i.val v

omit [DecidableEq ι] in
theorem product_weights_by_blocks {τ : ι → ℕ} (p : Pattern τ)
    (μ : ι → κ → ℝ) (b : BlockDraw p κ) :
    (∏ i, μ i (expand p b i)) = ∏ q : Block p, blockWeight p μ q (b.val q) := by
  rw [← Fintype.prod_fiberwise (label p) (fun i => μ i (expand p b i))]
  apply Finset.prod_congr rfl
  intro q _
  apply Finset.prod_congr rfl
  intro i _
  simp only [expand, i.property]

omit [DecidableEq ι] in
theorem product_by_multiplicity {τ : ι → ℕ} (p : Pattern τ)
    (b : BlockDraw p κ) {A : Type*} [CommMonoid A] (f : κ → A) :
    (∏ i, f (expand p b i)) = ∏ q : Block p, f (b.val q) ^ multiplicity p q := by
  unfold expand
  rw [← Fintype.prod_fiberwise' (label p) (fun q => f (b.val q))]
  simp only [Finset.prod_const, Finset.card_univ, multiplicity]

theorem product_weighted_sum_eq_patterns [Fintype κ] (τ : ι → ℕ)
    (μ : ι → κ → ℝ) (F : (ι → κ) → ℂ) :
    (∑ w : ι → κ, ((∏ i, μ i (w i)) : ℝ) • F w) =
      ∑ p : Pattern τ, ∑ b : BlockDraw p κ,
        (∏ q : Block p, blockWeight p μ q (b.val q)) • F (expand p b) := by
  rw [sum_eq_patterns τ]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  rw [product_weights_by_blocks]

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
