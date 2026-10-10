import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Logic.Equiv.Prod
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler

namespace OAI


namespace PerfectCompleteness.HiddenBucketBias

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators TensorProduct Classical

noncomputable section

abbrev F2 := BucketSampler.F2

variable {ℓ : Nat} {Ω H : Type*} [Fintype Ω]
  [AddCommGroup H] [Module F2 H]

abbrev HiddenDirection (W : Submodule F2 (Fin ℓ → F2)) :=
  {v : BucketSampler.Direction ℓ // v.val ∈ W}

abbrev VisibleDirection (W : Submodule F2 (Fin ℓ → F2)) :=
  {v : BucketSampler.Direction ℓ // v.val ∉ W}

abbrev HiddenTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) := HiddenDirection W → Ω
abbrev VisibleTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) := VisibleDirection W → Ω

def hiddenTapeLaw (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution Ω) :
    FiniteDistribution (HiddenTape W Ω) :=
  FiniteProduct.law (fun _ : HiddenDirection W => μ)

def visibleTapeLaw (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution Ω) :
    FiniteDistribution (VisibleTape W Ω) :=
  FiniteProduct.law (fun _ : VisibleDirection W => μ)

def splitTape (W : Submodule F2 (Fin ℓ → F2)) (Ω : Type*) :
    BucketSampler.Tape ℓ Ω ≃ HiddenTape W Ω × VisibleTape W Ω :=
  Equiv.piEquivPiSubtypeProd (fun v : BucketSampler.Direction ℓ => v.val ∈ W) (fun _ => Ω)

theorem split_tapeLaw (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution Ω) :
    (BucketSampler.tapeLaw ℓ μ).transport (splitTape W Ω) =
      (hiddenTapeLaw W μ).product (visibleTapeLaw W μ) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ v : BucketSampler.Direction ℓ, μ.weight ((splitTape W Ω).symm y v)) =
    (∏ v : HiddenDirection W, μ.weight (y.1 v)) *
      ∏ v : VisibleDirection W, μ.weight (y.2 v)
  calc
    _ = ∏ v : BucketSampler.Direction ℓ,
        if h : v.val ∈ W then μ.weight (y.1 ⟨v, h⟩) else μ.weight (y.2 ⟨v, h⟩) := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v.val ∈ W <;> simp [splitTape, Equiv.piEquivPiSubtypeProd, hv]
    _ = _ := Fintype.prod_dite _ _

theorem split_tapeLaw_pushforward (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) :
    (BucketSampler.tapeLaw ℓ μ).pushforward (splitTape W Ω) =
      (hiddenTapeLaw W μ).product (visibleTapeLaw W μ) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact split_tapeLaw W μ

theorem product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.fst = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  calc
    _ = (μ.product ν).expectation (fun x => if x.1 = a then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = μ.expectation (fun x => ν.expectation (fun _ => if x = a then 1 else 0)) :=
      FiniteDistribution.expectation_product μ ν _
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite, ν.normalized]

theorem hidden_marginal (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution Ω) :
    (BucketSampler.tapeLaw ℓ μ).pushforward
        (fun ω (v : HiddenDirection W) => ω v.val) = hiddenTapeLaw W μ := by
  change (BucketSampler.tapeLaw ℓ μ).pushforward
    (fun ω => (splitTape W Ω ω).1) = _
  rw [← FiniteDistribution.pushforward_comp (BucketSampler.tapeLaw ℓ μ)
    (splitTape W Ω) Prod.fst, split_tapeLaw_pushforward, product_fst]

theorem hidden_coordinate_marginal (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (v : HiddenDirection W) :
    (hiddenTapeLaw W μ).pushforward (fun ω => ω v) = μ :=
  FiniteProduct.eval_pushforward (fun _ : HiddenDirection W => μ) v

theorem hidden_coordinates_independent (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (v w : HiddenDirection W) (hvw : v ≠ w)
    (f g : Ω → ℝ) :
    (hiddenTapeLaw W μ).expectation (fun ω => f (ω v) * g (ω w)) =
      μ.expectation f * μ.expectation g :=
  FiniteProduct.expectation_eval_mul (fun _ : HiddenDirection W => μ) v w hvw f g

def directionIn (W : Submodule F2 (Fin ℓ → F2)) (v : HiddenDirection W) : W :=
  ⟨v.val.val, v.property⟩

theorem directionIn_ne_zero (W : Submodule F2 (Fin ℓ → F2)) (v : HiddenDirection W) :
    directionIn W v ≠ 0 := by
  intro h
  exact v.val.property (congrArg Subtype.val h)

def hiddenSum (W : Submodule F2 (Fin ℓ → F2)) (eval : Ω → H) (ω : HiddenTape W Ω) :
    W ⊗[F2] H :=
  ∑ v : HiddenDirection W, directionIn W v ⊗ₜ[F2] eval (ω v)

def scalarRestriction (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (v : W) : Module.Dual F2 H :=
  Φ.comp (TensorProduct.mk F2 W H v)

@[simp] theorem scalarRestriction_apply (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (v : W) (h : H) :
    scalarRestriction W Φ v h = Φ (v ⊗ₜ[F2] h) := rfl

theorem exists_nonzero_restriction (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    ∃ v : HiddenDirection W, scalarRestriction W Φ (directionIn W v) ≠ 0 := by
  by_contra hn
  apply hΦ
  apply TensorProduct.ext'
  intro v h
  by_cases hv : v = 0
  · simp [hv]
  · let d : HiddenDirection W :=
      ⟨⟨v.val, fun hzero => hv (Subtype.ext hzero)⟩, v.property⟩
    have hs : scalarRestriction W Φ (directionIn W d) = 0 := by
      by_contra hs
      exact hn ⟨d, hs⟩
    simpa only [scalarRestriction_apply, directionIn, d, LinearMap.zero_apply] using
      LinearMap.congr_fun hs h

theorem abs_character (χ : AddChar F2 ℝ) (b : F2) : |χ b| = 1 := by
  have hs : χ b * χ b = 1 := by
    rw [← χ.map_add_eq_mul, CharTwo.add_self_eq_zero, χ.map_zero_eq_one]
  have hs' : χ b ^ 2 = 1 := by simpa only [pow_two] using hs
  rcases sq_eq_one_iff.mp hs' with hb | hb <;> rw [hb] <;> norm_num

def signCharacter : AddChar F2 ℝ where
  toFun := QuarterBalance.sign
  map_zero_eq_one' := QuarterBalance.sign_zero
  map_add_eq_mul' := QuarterBalance.sign_add

theorem character_sum {I : Type*} [Fintype I] (χ : AddChar F2 ℝ) (f : I → F2) :
    χ (∑ i, f i) = ∏ i, χ (f i) := by
  have h (s : Finset I) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]
  exact h Finset.univ

omit [Fintype Ω] in
theorem character_hiddenSum (W : Submodule F2 (Fin ℓ → F2))
    (eval : Ω → H) (χ : AddChar F2 ℝ) (Φ : Module.Dual F2 (W ⊗[F2] H))
    (ω : HiddenTape W Ω) :
    χ (Φ (hiddenSum W eval ω)) =
      ∏ v : HiddenDirection W, χ (scalarRestriction W Φ (directionIn W v) (eval (ω v))) := by
  simp only [hiddenSum, map_sum, scalarRestriction_apply]
  exact character_sum χ _

theorem character_expectation_product (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) :
    (hiddenTapeLaw W μ).expectation (fun ω => χ (Φ (hiddenSum W eval ω))) =
      ∏ v : HiddenDirection W,
        μ.expectation (fun ω => χ (scalarRestriction W Φ (directionIn W v) (eval ω))) := by
  let f : HiddenDirection W → Ω → ℝ :=
    fun v ω => χ (scalarRestriction W Φ (directionIn W v) (eval ω))
  have hprod := FiniteProduct.expectation_product
    (I := HiddenDirection W) (Ω := fun _ : HiddenDirection W => Ω)
    (fun _ : HiddenDirection W => μ) f
  calc
    _ = (hiddenTapeLaw W μ).expectation (fun ω => ∏ v : HiddenDirection W, f v (ω v)) :=
      FiniteDistribution.expectation_congr _ (fun ω => character_hiddenSum W eval χ Φ ω)
    _ = _ := hprod

theorem abs_expectation_character_le_one (μ : FiniteDistribution Ω)
    (χ : AddChar F2 ℝ) (f : Ω → F2) : |μ.expectation (fun ω => χ (f ω))| ≤ 1 := by
  calc
    _ ≤ ∑ ω, |μ.weight ω * χ (f ω)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, μ.weight ω := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (μ.nonnegative ω), abs_character, mul_one]
    _ = 1 := μ.normalized

theorem hidden_bias_le (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => χ (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(hiddenTapeLaw W μ).expectation (fun ω => χ (Φ (hiddenSum W eval ω)))| ≤ bound := by
  obtain ⟨v, hv⟩ := exists_nonzero_restriction W Φ hΦ
  rw [character_expectation_product, Finset.abs_prod]
  let a : HiddenDirection W → ℝ := fun w =>
    |μ.expectation (fun ω => χ (scalarRestriction W Φ (directionIn W w) (eval ω)))|
  change (∏ w, a w) ≤ bound
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v)]
  have hrest : (∏ w ∈ Finset.univ.erase v, a w) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun w _ => abs_expectation_character_le_one μ χ _)
  calc
    _ ≤ a v * 1 := mul_le_mul_of_nonneg_left hrest (abs_nonneg _)
    _ = a v := mul_one _
    _ ≤ bound := scalar_bias _ hv

theorem hidden_sign_bias_le (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (eval : Ω → H) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => QuarterBalance.sign (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(hiddenTapeLaw W μ).expectation
      (fun ω => QuarterBalance.sign (Φ (hiddenSum W eval ω)))| ≤ bound :=
  hidden_bias_le W μ eval signCharacter bound scalar_bias Φ hΦ

instance tensorFinite (W : Submodule F2 (Fin ℓ → F2)) [Finite H] :
    Finite (W ⊗[F2] H) := by
  let : Fintype W := Fintype.ofFinite _
  apply Finite.of_surjective (fun f : W → H => ∑ w, w ⊗ₜ[F2] f w)
  intro z
  obtain ⟨s, hs⟩ := TensorProduct.exists_finsupp_left z
  refine ⟨fun w => s w, ?_⟩
  exact (s.sum_fintype (fun w h => w ⊗ₜ[F2] h) (fun _ => by simp)).symm.trans hs.symm

instance tensorFintype (W : Submodule F2 (Fin ℓ → F2)) [Finite H] :
    Fintype (W ⊗[F2] H) := Fintype.ofFinite _

def law (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) : FiniteDistribution (W ⊗[F2] H) :=
  (hiddenTapeLaw W μ).pushforward (hiddenSum W eval)

theorem law_from_full_buckets (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) :
    (BucketSampler.tapeLaw ℓ μ).pushforward
        (fun ω => hiddenSum W eval (fun v => ω v.val)) = law W μ eval := by
  rw [← FiniteDistribution.pushforward_comp (BucketSampler.tapeLaw ℓ μ)
    (fun ω (v : HiddenDirection W) => ω v.val) (hiddenSum W eval), hidden_marginal]
  rfl

theorem law_bias_le (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => χ (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(law W μ eval).expectation (fun x => χ (Φ x))| ≤ bound := by
  rw [law, FiniteDistribution.expectation_pushforward]
  exact hidden_bias_le W μ eval χ bound scalar_bias Φ hΦ

theorem law_sign_bias_le (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => QuarterBalance.sign (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(law W μ eval).expectation (fun x => QuarterBalance.sign (Φ x))| ≤ bound :=
  law_bias_le W μ eval signCharacter bound scalar_bias Φ hΦ

section Recursive

universe u
variable {branch : Nat → Nat} {n m : Nat}

def recursiveLaw (W : Submodule F2 (Fin ℓ → F2)) (repeats : Nat → Nat)
    (p : DescendantSpaces.Path branch n m) (A : RecursiveSpaces.Slots branch n → Type u)
    [∀ s, Finite (A s)] :
    FiniteDistribution (W ⊗[F2] RecursiveSpaces.space F2 branch n A) :=
  law W (RecursiveSampler.tapeLaw F2 repeats p A) (RecursiveSampler.evaluate F2 repeats p A)

theorem recursive_law_sign_bias_le (W : Submodule F2 (Fin ℓ → F2)) (repeats : Nat → Nat)
    (p : DescendantSpaces.Path branch n m) (A : RecursiveSpaces.Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (RecursiveSpaces.space F2 branch n A)]
    (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 (RecursiveSpaces.space F2 branch n A), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats p A).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] RecursiveSpaces.space F2 branch n A)) (hΦ : Φ ≠ 0) :
    |(recursiveLaw W repeats p A).expectation (fun x => QuarterBalance.sign (Φ x))| ≤ bound := by
  apply law_sign_bias_le W (RecursiveSampler.tapeLaw F2 repeats p A)
    (RecursiveSampler.evaluate F2 repeats p A) bound ?_ Φ hΦ
  intro f hf
  simpa only [RecursiveSampler.law, FiniteDistribution.expectation_pushforward] using
    scalar_bias f hf

end Recursive


variable {E : Type*} [Fintype E]

def exposedLaw (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution E) :
    FiniteDistribution (HiddenTape W Ω × (VisibleTape W Ω × E)) :=
  (hiddenTapeLaw W μ).product ((visibleTapeLaw W μ).product ν)

theorem hidden_condition_exterior (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution E)
    (event : VisibleTape W Ω × E → Bool)
    (positive : 0 < (exposedLaw W μ ν).probability (fun x => event x.2)) :
    ((exposedLaw W μ ν).condition (fun x => event x.2) positive).pushforward Prod.fst =
      hiddenTapeLaw W μ :=
  CleanConditioning.source_condition_of_constant (hiddenTapeLaw W μ)
    (fun _ => (visibleTapeLaw W μ).product ν) (fun x => event x.2)
    (((visibleTapeLaw W μ).product ν).probability event) (fun _ => rfl) positive

theorem law_condition_exterior (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution E) (eval : Ω → H)
    (event : VisibleTape W Ω × E → Bool)
    (positive : 0 < (exposedLaw W μ ν).probability (fun x => event x.2)) :
    ((exposedLaw W μ ν).condition (fun x => event x.2) positive).pushforward
        (fun x => hiddenSum W eval x.1) = law W μ eval := by
  rw [← FiniteDistribution.pushforward_comp
    ((exposedLaw W μ ν).condition (fun x => event x.2) positive) Prod.fst (hiddenSum W eval),
    hidden_condition_exterior]
  rfl

end

end PerfectCompleteness.HiddenBucketBias

end OAI
