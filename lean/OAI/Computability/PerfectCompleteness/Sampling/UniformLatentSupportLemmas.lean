import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatent

namespace OAI


namespace PerfectCompleteness.UniformLatentSupport

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section Latent

variable {S J D : Type*} [Fintype S] [Fintype J] [DecidableEq J] [Fintype D]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

theorem latentKernel_weight_zero_of_tag_ne (s : S) (raw : UniformLatent.Raw Ω)
    (hne : raw.1 ≠ s) : (UniformLatent.latentKernel Ω s).weight raw = 0 := by
  simp only [UniformLatent.latentKernel, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro x _
  have hx : (⟨s, x⟩ : UniformLatent.Raw Ω) ≠ raw := by
    intro h
    exact hne (congrArg (fun z : UniformLatent.Raw Ω => z.1) h).symm
  simp only [ite_eq_right hx]

theorem latentKernel_tag (s : S) (raw : UniformLatent.Raw Ω)
    (hraw : (UniformLatent.latentKernel Ω s).weight raw ≠ 0) : raw.1 = s := by
  by_contra hne
  exact hraw (latentKernel_weight_zero_of_tag_ne Ω s raw hne)

theorem projectedKernel_weight_inr (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) (raw : UniformLatent.Raw Ω) :
    (UniformLatent.projectedKernel Ω flag nonprojected s).weight (Sum.inr raw) =
      flag.weight true * (UniformLatent.latentKernel Ω s).weight raw := by
  simp [UniformLatent.projectedKernel, FiniteDistribution.mixture,
    FiniteDistribution.pushforward]

theorem projectedKernel_tag (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) (raw : UniformLatent.Raw Ω)
    (hraw : (UniformLatent.projectedKernel Ω flag nonprojected s).weight (Sum.inr raw) ≠ 0) :
    raw.1 = s := by
  apply latentKernel_tag Ω s raw
  intro hz
  apply hraw
  rw [projectedKernel_weight_inr, hz, mul_zero]

end Latent


variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]
  (μ : (i : I) → FiniteDistribution (E i))
  (ν : (i : I) → FiniteDistribution (R i))
  (flag : (i : I) → FiniteDistribution Bool)
  (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))

def childLaw (i : I) :
    FiniteDistribution (E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i)) :=
  CleanConditioning.kernelJoint (μ i) (fun e =>
    CleanConditioning.kernelJoint (ν i) (UniformCleanSources.childKernel Ω flag nonprojected i e))

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childLaw_weight (i : I)
    (x : E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i)) :
    (childLaw Ω μ ν flag nonprojected i).weight x =
      (μ i).weight x.1 * ((ν i).weight x.2.1 *
        (UniformLatent.projectedKernel (Ω i) (flag i) (nonprojected i) (x.1, x.2.1)).weight
          x.2.2) := rfl

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childLaw_projected_tag (i : I)
    (x : E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i))
    (hx : (childLaw Ω μ ν flag nonprojected i).weight x ≠ 0)
    (raw : UniformLatent.Raw (Ω i)) (hraw : x.2.2 = Sum.inr raw) :
    raw.1 = (x.1, x.2.1) := by
  apply projectedKernel_tag (Ω i) (flag i) (nonprojected i) (x.1, x.2.1) raw
  intro hz
  apply hx
  rw [childLaw_weight, hraw, hz, mul_zero, mul_zero]

omit [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_child_weight_ne_zero
    (x : (i : I) → E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag nonprojected).weight x ≠ 0)
    (i : I) : (childLaw Ω μ ν flag nonprojected i).weight (x i) ≠ 0 := by
  intro hz
  apply hx
  change (∏ j, (childLaw Ω μ ν flag nonprojected j).weight (x j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

omit [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_projected_tag
    (x : (i : I) → E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag nonprojected).weight x ≠ 0)
    (i : I) (raw : UniformLatent.Raw (Ω i)) (hraw : (x i).2.2 = Sum.inr raw) :
    raw.1 = ((x i).1, (x i).2.1) :=
  childLaw_projected_tag Ω μ ν flag nonprojected i (x i)
    (childrenLaw_child_weight_ne_zero Ω μ ν flag nonprojected x hx i) raw hraw

omit [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem conditioned_childrenLaw_projected_tag
    (event : ((i : I) → E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i)) → Bool)
    (positive : 0 < (UniformCleanSources.childrenLaw Ω μ ν flag nonprojected).probability event)
    (x : (i : I) → E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i))
    (hx : ((UniformCleanSources.childrenLaw Ω μ ν flag nonprojected).condition event positive).weight x ≠ 0)
    (i : I) (raw : UniformLatent.Raw (Ω i)) (hraw : (x i).2.2 = Sum.inr raw) :
    raw.1 = ((x i).1, (x i).2.1) := by
  apply childrenLaw_projected_tag Ω μ ν flag nonprojected x _ i raw hraw
  intro hz
  apply hx
  simp only [FiniteDistribution.condition, hz, zero_div, ite_self]

end
end PerfectCompleteness.UniformLatentSupport



namespace PerfectCompleteness.NativeTaggedUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

abbrev Raw {S : Type*} (Native : S → Type*) := Σ s, Native s

def sourceTag {S J : Type*} (Native : S → Type*) (Ω : S → J → Type*) :
    Raw Native ⊕ UniformLatent.Raw Ω → S
  | .inl raw => raw.1
  | .inr raw => raw.1

section Native

variable {S : Type*} [Fintype S] [DecidableEq S]
  (Native : S → Type*) [∀ s, Fintype (Native s)] [∀ s, Nonempty (Native s)]

def kernel (s : S) : FiniteDistribution (Raw Native) :=
  (FiniteDistribution.uniform (Native s)).pushforward (fun x => (⟨s, x⟩ : Raw Native))

omit [DecidableEq S] in
theorem kernel_weight_zero_of_tag_ne (s : S) (raw : Raw Native) (hne : raw.1 ≠ s) :
    (kernel Native s).weight raw = 0 := by
  unfold kernel FiniteDistribution.pushforward
  apply Finset.sum_eq_zero
  intro x _
  have hx : (⟨s, x⟩ : Raw Native) ≠ raw := by
    intro h
    exact hne (congrArg (fun z : Raw Native => z.1) h).symm
  exact ite_eq_right hx

theorem kernel_tag (s : S) (raw : Raw Native)
    (hraw : (kernel Native s).weight raw ≠ 0) : raw.1 = s := by
  by_contra hne
  exact hraw (kernel_weight_zero_of_tag_ne Native s raw hne)

end Native

section Projection

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (Native : S → Type*) [∀ s, Fintype (Native s)] [∀ s, Nonempty (Native s)]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

theorem projectedKernel_weight_inl (flag : FiniteDistribution Bool) (s : S)
    (raw : Raw Native) :
    (UniformLatent.projectedKernel Ω flag (kernel Native) s).weight (.inl raw) =
      flag.weight false * (kernel Native s).weight raw := by
  simp [UniformLatent.projectedKernel, FiniteDistribution.mixture,
    FiniteDistribution.pushforward]

theorem projectedKernel_sourceTag (flag : FiniteDistribution Bool) (s : S)
    (raw : Raw Native ⊕ UniformLatent.Raw Ω)
    (hraw : (UniformLatent.projectedKernel Ω flag (kernel Native) s).weight raw ≠ 0) :
    sourceTag Native Ω raw = s := by
  cases raw with
  | inl raw =>
      apply kernel_tag Native s raw
      intro hz
      apply hraw
      rw [projectedKernel_weight_inl, hz, mul_zero]
  | inr raw =>
      exact UniformLatentSupport.projectedKernel_tag Ω flag (kernel Native) s raw hraw

end Projection


variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)]
  (Native : (i : I) → E i × R i → Type*)
  [∀ i s, Fintype (Native i s)] [∀ i s, Nonempty (Native i s)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]
  (μ : (i : I) → FiniteDistribution (E i))
  (ν : (i : I) → FiniteDistribution (R i))
  (flag : (i : I) → FiniteDistribution Bool)

omit [Fintype I] [DecidableEq I] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childLaw_sourceTag (i : I)
    (x : E i × (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : (UniformLatentSupport.childLaw Ω μ ν flag (fun i => kernel (Native i)) i).weight
      x ≠ 0) :
    sourceTag (Native i) (Ω i) x.2.2 = (x.1, x.2.1) := by
  apply projectedKernel_sourceTag (Native i) (Ω i) (flag i) (x.1, x.2.1) x.2.2
  intro hz
  apply hx
  rw [UniformLatentSupport.childLaw_weight, hz, mul_zero, mul_zero]

omit [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_sourceTag
    (x : (i : I) → E i ×
      (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag (fun i => kernel (Native i))).weight
      x ≠ 0) (i : I) :
    sourceTag (Native i) (Ω i) (x i).2.2 = ((x i).1, (x i).2.1) :=
  childLaw_sourceTag Native Ω μ ν flag i (x i)
    (UniformLatentSupport.childrenLaw_child_weight_ne_zero Ω μ ν flag
      (fun i => kernel (Native i)) x hx i)

omit [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_native_tag
    (x : (i : I) → E i ×
      (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag (fun i => kernel (Native i))).weight
      x ≠ 0) (i : I) (raw : Raw (Native i)) (hraw : (x i).2.2 = .inl raw) :
    raw.1 = ((x i).1, (x i).2.1) := by
  have h := childrenLaw_sourceTag Native Ω μ ν flag x hx i
  rw [hraw] at h
  exact h

omit [∀ i s j, DecidableEq (Ω i s j)] in
theorem conditioned_childrenLaw_sourceTag
    (event : ((i : I) → E i ×
      (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i)) → Bool)
    (positive : 0 < (UniformCleanSources.childrenLaw Ω μ ν flag
      (fun i => kernel (Native i))).probability event)
    (x : (i : I) → E i ×
      (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : ((UniformCleanSources.childrenLaw Ω μ ν flag (fun i => kernel (Native i))).condition
      event positive).weight x ≠ 0) (i : I) :
    sourceTag (Native i) (Ω i) (x i).2.2 = ((x i).1, (x i).2.1) := by
  apply childrenLaw_sourceTag Native Ω μ ν flag x _ i
  intro hz
  apply hx
  simp only [FiniteDistribution.condition, hz, zero_div, ite_self]

end
end PerfectCompleteness.NativeTaggedUniform



namespace PerfectCompleteness.QuarterBalance

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]

theorem nonzero_linear_surjective (f : V →ₗ[F2] F2) (hf : f ≠ 0) :
    Function.Surjective f := by
  classical
  have hx : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hx
  intro b
  refine ⟨(b / f x) • x, ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ b hx

theorem uniform_bit_probability (f : V →ₗ[F2] F2) (hf : f ≠ 0) (b : F2) :
    (FiniteDistribution.uniform V).probability (fun x => decide (f x = b)) = (1 / 2 : ℝ) := by
  have h := UniformLinearImage.uniform_pushforward_linearMap f (nonzero_linear_surjective f hf)
  have hp := congrArg (fun μ : FiniteDistribution F2 =>
    μ.probability (fun y => decide (y = b))) h
  rw [FiniteDistribution.probability_pushforward] at hp
  rw [hp, UniformLatent.probability_uniform_singleton]
  norm_num [F2, ZMod.card]

theorem uniform_sign_expectation_eq_zero (f : V →ₗ[F2] F2) (hf : f ≠ 0) :
    (FiniteDistribution.uniform V).expectation (fun x => sign (f x)) = 0 := by
  rw [expectation_sign, uniform_bit_probability f hf]
  norm_num

theorem uniform_balanced : Balanced (FiniteDistribution.uniform V) := by
  intro f hf b
  rw [uniform_bit_probability f hf]
  norm_num

end
end PerfectCompleteness.QuarterBalance



namespace PerfectCompleteness.RecursiveSamplerBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler QuarterBalance
open RecursiveSamplerBiasAlgebra RecursiveSamplerBiasProducts

noncomputable section

universe u

variable {branch : Nat → Nat} {n m : Nat}

theorem sign_sum {I : Type*} [Fintype I] (a : I → F2) :
    sign (∑ i, a i) = ∏ i, sign (a i) := by
  classical
  have h (s : Finset I) : sign (∑ i ∈ s, a i) = ∏ i ∈ s, sign (a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]
  exact h Finset.univ

theorem abs_expectation_sign_le_one {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → F2) :
    |μ.expectation (fun x => sign (f x))| ≤ 1 := by
  calc
    _ ≤ ∑ x, |μ.weight x * sign (f x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, μ.weight x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (μ.nonnegative x), abs_sign, mul_one]
    _ = 1 := μ.normalized

def ordinaryCharacterMean (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] (f : space F2 branch (n + 1) A →ₗ[F2] F2) : ℝ := by
  letI : ∀ j : OffPath i, Fintype (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  letI : ∀ j : OffPath i, Nonempty (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => ⟨zeroDraw F2 repeats (.step i p) A (.inl j)⟩
  exact ∏ j : OffPath i,
    (FiniteDistribution.uniform (DrawSpace F2 repeats (.step i p) A (.inl j))).expectation
      (fun g => sign ((f.comp (childSquareLift F2 A j.val)) g))

def pairCharacterMean (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n (childFamily A i))]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) : ℝ :=
  ((law F2 repeats p (childFamily A i)).product
    (law F2 repeats p (childFamily A i))).expectation
      (fun z => sign (childBilinear F2 A i f z.1 z.2))

theorem law_step_character (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n (childFamily A i))]
    [Fintype (space F2 branch (n + 1) A)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) :
    (law F2 repeats (.step i p) A).expectation (fun g => sign (f g)) =
      ordinaryCharacterMean repeats i p A f *
        pairCharacterMean repeats i p A f ^ repeats (n + 1) := by
  classical
  let : ∀ j : OffPath i, Fintype (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  let : ∀ j : OffPath i, Nonempty (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => ⟨zeroDraw F2 repeats (.step i p) A (.inl j)⟩
  rw [law_step, FiniteDistribution.expectation_pushforward]
  have hsign (z : OrdinaryTape F2 repeats i p A ×
      (CallIndex repeats n → space F2 branch n (childFamily A i))) :
      sign (f (stepCombine F2 repeats i p A z)) =
        (∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (z.1 j))) *
          ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true))) := by
    have hm := map_combine F2 A i (repeats (n + 1)) f
      (fun j : OffPath i =>
        (show squareSpace (space F2 branch n (childFamily A j.val)) from z.1 j))
      (fun h => z.2 (h, false)) (fun h => z.2 (h, true))
    calc
      _ = sign ((∑ j : OffPath i, (f.comp (childSquareLift F2 A j.val)) (z.1 j)) +
          ∑ h : Fin (repeats (n + 1)),
            childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true))) := congrArg sign hm
      _ = _ := by rw [sign_add, sign_sum, sign_sum]
  have hord : (ordinaryLaw F2 repeats i p A).expectation
      (fun o => ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j))) =
      ordinaryCharacterMean repeats i p A f :=
    FiniteProduct.expectation_product
      (I := OffPath i)
      (Ω := fun j => DrawSpace F2 repeats (.step i p) A (.inl j))
      (fun j : OffPath i =>
        FiniteDistribution.uniform (DrawSpace F2 repeats (.step i p) A (.inl j)))
      (fun j (g : DrawSpace F2 repeats (.step i p) A (.inl j)) =>
        sign ((f.comp (childSquareLift F2 A j.val)) g))
  have hpair : (callScalarLaw F2 repeats i p A).expectation
      (fun x => ∏ h : Fin (repeats (n + 1)),
        sign (childBilinear F2 A i f (x (h, false)) (x (h, true)))) =
      pairCharacterMean repeats i p A f ^ repeats (n + 1) :=
    expectation_pairs (repeats (n + 1)) (law F2 repeats p (childFamily A i))
      (fun z => sign (childBilinear F2 A i f z.1 z.2))
  calc
    _ = ((ordinaryLaw F2 repeats i p A).product
        (callScalarLaw F2 repeats i p A)).expectation
          (fun z =>
            (∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (z.1 j))) *
              ∏ h : Fin (repeats (n + 1)),
                sign (childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true)))) :=
      FiniteDistribution.expectation_congr _ hsign
    _ = (ordinaryLaw F2 repeats i p A).expectation
          (fun o => ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j))) *
        (callScalarLaw F2 repeats i p A).expectation
          (fun x => ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (x (h, false)) (x (h, true)))) :=
      expectation_product_mul
        (V := OrdinaryTape F2 repeats i p A)
        (W := CallIndex repeats n → space F2 branch n (childFamily A i))
        (ordinaryLaw F2 repeats i p A) (callScalarLaw F2 repeats i p A)
        (fun o : OrdinaryTape F2 repeats i p A =>
          ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j)))
        (fun x : CallIndex repeats n → space F2 branch n (childFamily A i) =>
          ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (x (h, false)) (x (h, true))))
    _ = _ := congrArg₂ (fun a b : ℝ => a * b) hord hpair

theorem abs_ordinaryCharacterMean_le_one (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) :
    |ordinaryCharacterMean repeats i p A f| ≤ 1 := by
  unfold ordinaryCharacterMean
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro j _
  let : Fintype (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  let : Nonempty (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    ⟨zeroDraw F2 repeats (.step i p) A (.inl j)⟩
  exact abs_expectation_sign_le_one
    (FiniteDistribution.uniform (DrawSpace F2 repeats (.step i p) A (.inl j)))
    (fun g => (f.comp (childSquareLift F2 A j.val)) g)

theorem ordinaryCharacterMean_eq_zero (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2)
    (j : OffPath i) (hj : f.comp (childSquareLift F2 A j.val) ≠ 0) :
    ordinaryCharacterMean repeats i p A f = 0 := by
  classical
  unfold ordinaryCharacterMean
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  let : Fintype (squareSpace (space F2 branch n (childFamily A j.val))) :=
    drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  exact uniform_sign_expectation_eq_zero (f.comp (childSquareLift F2 A j.val)) hj

theorem law_step_bias_le (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n (childFamily A i))]
    [Fintype (space F2 branch (n + 1) A)]
    (hchild : Balanced (law F2 repeats p (childFamily A i)))
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats (.step i p) A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats (n + 1) := by
  rw [law_step_character]
  rcases ordinary_or_bilinear_ne_zero F2 A i f hf with ⟨j, hj⟩ | hB
  · rw [ordinaryCharacterMean_eq_zero repeats i p A f j hj, zero_mul, abs_zero]
    exact pow_nonneg (by norm_num) _
  · have hp : |pairCharacterMean repeats i p A f| ≤ (7 / 8 : ℝ) :=
      bilinear_bias _ _ hchild hchild (childBilinear F2 A i f) hB
    rw [abs_mul, abs_pow]
    calc
      _ ≤ 1 * |pairCharacterMean repeats i p A f| ^ repeats (n + 1) :=
        mul_le_mul_of_nonneg_right
          (abs_ordinaryCharacterMean_le_one repeats i p A f) (pow_nonneg (abs_nonneg _) _)
      _ = |pairCharacterMean repeats i p A f| ^ repeats (n + 1) := one_mul _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hp _

def RepetitionsBalanced (repeats : Nat → Nat) : Prop :=
  ∀ k : Nat, (7 / 8 : ℝ) ^ repeats (k + 1) ≤ 1 / 2

theorem repetitionsBalanced_of_six_le (repeats : Nat → Nat)
    (hrep : ∀ k : Nat, 6 ≤ repeats (k + 1)) : RepetitionsBalanced repeats := by
  intro k
  calc
    (7 / 8 : ℝ) ^ repeats (k + 1) ≤ (7 / 8 : ℝ) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hrep k)
    _ ≤ 1 / 2 := by norm_num

theorem law_balanced (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) [∀ s, Finite (A s)]
      [Fintype (space F2 branch n A)], Balanced (law F2 repeats p A) := by
  induction p with
  | refl n =>
      intro A hA hH
      rw [law_refl_uniform]
      apply balanced_of_bias_le_half
      intro f hf
      rw [uniform_sign_expectation_eq_zero f hf, abs_zero]
      norm_num
  | @step n m i p ih =>
      intro A hA hH
      let : Fintype (space F2 branch n (childFamily A i)) := Fintype.ofFinite _
      have hchild := ih (childFamily A i)
      apply balanced_of_bias_le_half
      intro f hf
      exact (law_step_bias_le repeats i p A hchild f hf).trans (hrep n)

theorem law_bias_le (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    [Fintype (space F2 branch (n + 1) A)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats (.step i p) A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats (n + 1) := by
  let : Fintype (space F2 branch n (childFamily A i)) := Fintype.ofFinite _
  exact law_step_bias_le repeats i p A
    (law_balanced repeats hrep p (childFamily A i)) f hf

theorem law_bias_le_height (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n A)]
    (f : space F2 branch n A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats p A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats n := by
  cases p with
  | refl n =>
      rw [law_refl_uniform, uniform_sign_expectation_eq_zero f hf, abs_zero]
      exact pow_nonneg (by norm_num) _
  | step i p => exact law_bias_le repeats hrep i p A f hf

theorem tape_bias_le (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(tapeLaw F2 repeats (.step i p) A).expectation
      (fun t => sign (f (evaluate F2 repeats (.step i p) A t)))| ≤
        (7 / 8 : ℝ) ^ repeats (n + 1) := by
  let : Fintype (space F2 branch (n + 1) A) := Fintype.ofFinite _
  have h := law_bias_le repeats hrep i p A f hf
  rw [law, FiniteDistribution.expectation_pushforward] at h
  exact h

end
end PerfectCompleteness.RecursiveSamplerBias

end OAI
