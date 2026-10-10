import OAI.Computability.PerfectCompleteness.Foundations.ManyGoodRowsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Sampling.GoodRowSampling

namespace OAI


namespace PerfectCompleteness.GoodAdviceEvents

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows PerfectCompleteness.GoodRowSampling

attribute [local instance] linearMapFintype

section FiniteLaws

variable {Ω P : Type*} [Fintype Ω] [Fintype P] [Nonempty Ω]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z =
      μ.probability (fun x => decide (p x = z) && event z x) := by
  unfold UsefulMark.lowerFiberMass
  congr 1
  funext x
  by_cases hx : p x = z <;> simp [hx]

omit [Fintype P] in
theorem adapted_uniform_fiber_probability (p : Ω → P)
    (event : P → Ω → Bool) (z : P) [Nonempty {x : Ω // p x = z}] :
    UsefulMark.lowerFiberMass (FiniteDistribution.uniform Ω) p
        (fun x => event (p x) x) z =
      (FiniteDistribution.uniform Ω).probability (fun x => decide (p x = z)) *
        (FiniteDistribution.uniform {x : Ω // p x = z}).probability
          (fun x => event z x.val) := by
  rw [adapted_fiber_probability]
  rw [FiniteDistribution.probability_inter_eq_mul_conditional _ _ _
    (UniformConditioning.uniform_probability_pos (fun x => p x = z))]
  rw [UniformConditioning.probability_condition_uniform]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability_zero (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) (h : ∀ x, event z x = false) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z = 0 := by
  rw [adapted_fiber_probability]
  simp only [h, Bool.and_false, FiniteDistribution.probability_false]

theorem uniform_probability_eq_expect (event : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability event =
      𝔼 x : Ω, if event x then (1 : ℝ) else 0 := by
  have h : (FiniteDistribution.uniform Ω).probability event =
      (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
    simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
      mul_ite, mul_one, mul_zero]
  rw [h, FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

omit [Nonempty Ω] in
theorem product_probability {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (event : Ω × Γ → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end FiniteLaws

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

def selectedColumn (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) (X : E →ₗ[F2] F) : Bool :=
  if h : GoodRow f r ρ A U then
    let w := selectWitness f r ρ A U h
    decide (X.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace)
  else false

def selectedAgreement (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) (X : E →ₗ[F2] F) : Bool :=
  if h : GoodRow f r ρ A U then
    let w := selectWitness f r ρ A U h
    decide (X.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace ∧
      f X = some w.value)
  else false

def J (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (sample : RowMap F r × (E →ₗ[F2] F)) : Bool :=
  selectedColumn f r ρ sample.1 (sample.1.comp sample.2) sample.2

def I (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (sample : RowMap F r × (E →ₗ[F2] F)) : Bool :=
  selectedAgreement f r ρ sample.1 (sample.1.comp sample.2) sample.2

def law (E F : Type*) [AddCommGroup E] [Module F2 E]
    [AddCommGroup F] [Module F2 F] [Fintype E] [Fintype F] (r : Nat) :
    FiniteDistribution (RowMap F r × (E →ₗ[F2] F)) :=
  (FiniteDistribution.uniform (RowMap F r)).product
    (FiniteDistribution.uniform (E →ₗ[F2] F))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem I_implies_J (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (sample : RowMap F r × (E →ₗ[F2] F)) (hI : I f r ρ sample = true) :
    J f r ρ sample = true := by
  unfold I selectedAgreement at hI
  unfold J selectedColumn
  by_cases h : GoodRow f r ρ sample.1 (sample.1.comp sample.2)
  · simp only [dite_eq_left h] at hI ⊢
    exact decide_eq_true_eq.mpr ((decide_eq_true_eq.mp hI).1)
  · simp [h] at hI

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_agreement_probability {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    letI : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    ρ * (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace =
          w.base.domRestrict w.columnSpace)) ≤
      (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace =
          w.base.domRestrict w.columnSpace ∧ f X.val = some w.value)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  let S₀ := MatrixSlice.Slice (⊥ : Submodule F2 E) (LinearMap.ker A) w.base
  let S := MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base
  let column : S₀ → Prop :=
    fun X => X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace
  let matchValue : S₀ → Bool := fun X => decide (f X.val = some w.value)
  let : Nonempty {X : S₀ // column X} :=
    ⟨⟨⟨w.base, rfl, rfl⟩, rfl⟩⟩
  have column_decide : (fun X => decide (column X)) =
      (fun X => @decide (column X) (Classical.propDecidable _)) := by
    funext sample
    exact decide_eq_decide.mpr Iff.rfl
  have positive : 0 < (FiniteDistribution.uniform S₀).probability
      (fun X => decide (column X)) := by
    rw [column_decide]
    exact UniformConditioning.uniform_probability_pos column
  have density :
      ρ ≤ (FiniteDistribution.uniform S).probability
        (fun X => decide (f X.val = some w.value)) := by
    calc
      ρ ≤ (𝔼 X : S, PartialTableInverse.indicator f w.value X.val) := w.density
      _ = (FiniteDistribution.uniform S).probability
          (fun X => decide (f X.val = some w.value)) := by
        rw [uniform_probability_eq_expect]
        simp only [PartialTableInverse.indicator, decide_eq_true_eq]
  have conditional :
      ρ ≤ ((FiniteDistribution.uniform S₀).condition
        (fun X => decide (column X)) positive).probability matchValue := by
    simp only [column_decide]
    rw [UniformConditioning.probability_condition_uniform]
    have he := UniformConditioning.uniform_probability_equiv
      (SliceMass.columnEventEquivSlice w.columnSpace (LinearMap.ker A) w.base)
      (fun X : S => decide (f X.val = some w.value))
    convert density.trans_eq he.symm using 1
    congr!
  have rowSlice :
      ρ * (FiniteDistribution.uniform S₀).probability
          (fun X => decide (column X)) ≤
        (FiniteDistribution.uniform S₀).probability
          (fun X => decide (column X) && matchValue X) := by
    rw [FiniteDistribution.probability_inter_eq_mul_conditional _ _ _ positive]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left conditional
      ((FiniteDistribution.uniform S₀).probability_nonnegative
        (fun X => decide (column X)))
  have hcolumn := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U => decide (X.val.domRestrict w.columnSpace =
      w.base.domRestrict w.columnSpace))
  have hmatch := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace) &&
        decide (f X.val = some w.value))
  have hand : (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace ∧
        f X.val = some w.value)) =
      (fun X : RowFiber A U =>
        decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace) &&
          decide (f X.val = some w.value)) := by
    funext X
    by_cases hcolumn : X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace <;>
      by_cases hvalue : f X.val = some w.value <;> simp [hcolumn, hvalue]
  rw [hand]
  rw [← hcolumn, ← hmatch]
  exact rowSlice

omit [Fintype Y] in
theorem J_probability_fixed_row (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) (A : RowMap F r) :
    (1 / (2 : ℝ) ^ (r * Module.finrank F2 F)) *
        (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
          (fun X => decide (GoodRow f r ρ A (A.comp X))) ≤
      (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => J f r ρ (A, X)) := by
  let μ := FiniteDistribution.uniform (E →ₗ[F2] F)
  let p : (E →ₗ[F2] F) → (E →ₗ[F2] (Fin r → F2)) := fun X => A.comp X
  rw [UsefulMark.probability_eq_sum_fibers μ p,
    UsefulMark.probability_eq_sum_fibers μ p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _
  by_cases hgood : GoodRow f r ρ A U
  · let w := selectWitness f r ρ A U hgood
    let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    have hG : UsefulMark.lowerFiberMass μ p
        (fun X => decide (GoodRow f r ρ A (A.comp X))) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) := by
      rw [adapted_fiber_probability μ p
        (fun V _X => decide (GoodRow f r ρ A V)) U]
      simp only [hgood, decide_true, Bool.and_true]
      rfl
    have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedColumn f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedColumn f r ρ A) U).trans ?_
      simp only [selectedColumn, dite_eq_left hgood]
      congr!
    rw [hG, hJ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (witness_column_probability w) (μ.probability_nonnegative _)
  · have hG : UsefulMark.lowerFiberMass μ p
        (fun X => decide (GoodRow f r ρ A (A.comp X))) U = 0 :=
      adapted_fiber_probability_zero μ p
        (fun V _X => decide (GoodRow f r ρ A V)) U (by intro X; simp [hgood])
    rw [hG, mul_zero]
    exact μ.probability_nonnegative _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem I_probability_fixed_row (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) (A : RowMap F r) :
    ρ * (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => J f r ρ (A, X)) ≤
      (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => I f r ρ (A, X)) := by
  let μ := FiniteDistribution.uniform (E →ₗ[F2] F)
  let p : (E →ₗ[F2] F) → (E →ₗ[F2] (Fin r → F2)) := fun X => A.comp X
  rw [UsefulMark.probability_eq_sum_fibers μ p,
    UsefulMark.probability_eq_sum_fibers μ p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _
  by_cases hgood : GoodRow f r ρ A U
  · let w := selectWitness f r ρ A U hgood
    let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedColumn f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedColumn f r ρ A) U).trans ?_
      simp only [selectedColumn, dite_eq_left hgood]
      congr!
    have hI : UsefulMark.lowerFiberMass μ p (fun X => I f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace ∧ f X.val = some w.value)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedAgreement f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedAgreement f r ρ A) U).trans ?_
      simp only [selectedAgreement, dite_eq_left hgood]
      congr!
    rw [hJ, hI]
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
      (witness_agreement_probability w) (μ.probability_nonnegative _)
  · have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U = 0 :=
      adapted_fiber_probability_zero μ p (selectedColumn f r ρ A) U
        (by intro X; simp [selectedColumn, hgood])
    rw [hJ, mul_zero]
    exact μ.probability_nonnegative _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem good_probability_eq_adviceMass (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) :
    (law E F r).probability
        (fun s => decide (GoodRow f r ρ s.1 (s.1.comp s.2))) = adviceMass f r ρ := by
  simp only [law, product_probability, uniform_probability_eq_expect,
    FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card,
    adviceMass, decide_eq_true_eq]

omit [Fintype Y] in
theorem J_probability_ge (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    adviceMass f r ρ / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      (law E F r).probability (J f r ρ) := by
  calc
    _ = (1 / (2 : ℝ) ^ (r * Module.finrank F2 F)) *
        (law E F r).probability
          (fun s => decide (GoodRow f r ρ s.1 (s.1.comp s.2))) := by
      rw [good_probability_eq_adviceMass]
      ring
    _ ≤ _ := by
      simp only [law, product_probability, FiniteDistribution.expectation, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro A _
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
        (J_probability_fixed_row f r ρ A)
        ((FiniteDistribution.uniform (RowMap F r)).nonnegative A)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem I_probability_ge (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    ρ * (law E F r).probability (J f r ρ) ≤
      (law E F r).probability (I f r ρ) := by
  simp only [law, product_probability, FiniteDistribution.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (I_probability_fixed_row f r ρ A)
    ((FiniteDistribution.uniform (RowMap F r)).nonnegative A)

end
end PerfectCompleteness.GoodAdviceEvents



namespace PerfectCompleteness.GoodAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E Y : P → Type*} {F : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F] [Fintype F]
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)] [∀ p, Fintype (Y p)]

abbrev Sample (r : Nat) := Σ p : P, RowMap F r × (E p →ₗ[F2] F)

def law (μ : FiniteDistribution P) (r : Nat) :
    FiniteDistribution (Sample (E := E) (F := F) r) :=
  CompletionSoundness.sigmaLaw μ (fun p => GoodAdviceEvents.law (E p) F r)

def J (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.J (f sample.1) r ρ sample.2

def I (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p))
    (r : Nat) (ρ : ℝ) (sample : Sample (E := E) (F := F) r) : Bool :=
  GoodAdviceEvents.I (f sample.1) r ρ sample.2

omit [FiniteDimensional F2 F] [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (Y p)] in
theorem J_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (J f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) F r).probability (GoodAdviceEvents.J (f p) r ρ)) := by
  exact CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) F r) (J f r ρ)

omit [FiniteDimensional F2 F] [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (Y p)] in
theorem I_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (I f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) F r).probability (GoodAdviceEvents.I (f p) r ρ)) := by
  exact CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) F r) (I f r ρ)

omit [∀ p, Fintype (Y p)] in
theorem J_probability_ge_mean_advice (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    μ.expectation (fun p => adviceMass (f p) r ρ) /
        (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  rw [J_probability_eq_mean]
  simp only [FiniteDistribution.expectation, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  simpa only [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left (GoodAdviceEvents.J_probability_ge (f p) r ρ)
      (μ.nonnegative p)

omit [FiniteDimensional F2 F] [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (Y p)] in
theorem I_probability_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    ρ * (law (E := E) (F := F) μ r).probability (J f r ρ) ≤
      (law (E := E) (F := F) μ r).probability (I f r ρ) := by
  rw [J_probability_eq_mean, I_probability_eq_mean]
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (GoodAdviceEvents.I_probability_ge (f p) r ρ) (μ.nonnegative p)

theorem J_probability_ge [Nontrivial F] (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p))
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * Module.finrank F2 F)) ^ 2 ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  calc
    _ = ((η ^ 2 / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F)) /
        (2 : ℝ) ^ (r * Module.finrank F2 F) := by ring
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) /
        (2 : ℝ) ^ (r * Module.finrank F2 F) :=
      div_le_div_of_nonneg_right
        (FamilyGoodRows.mean_adviceMass_ge μ f r ρ η hη hρ hρ1 hconstants hmean)
        (by positivity)
    _ ≤ _ := J_probability_ge_mean_advice μ f r ρ

end
end PerfectCompleteness.GoodAdviceFamily

end OAI
