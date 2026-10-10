import Mathlib
import OAI.Computability.MaxCut.PCP.Rounding

namespace OAI

/-! Comparison of the actual classical game value with the squared collision
norm. Both directions are proved for the normalized conditional kernel, including
partial projection constraints and zero-weight questions. -/

namespace MaxCutGames.Repetition

noncomputable section

namespace ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem sq_expectation_le_expectation_sq {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    μ.expectation f ^ 2 ≤ μ.expectation (fun x => f x ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset Ω))
    (r := fun x => μ.weight x * f x)
    (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (fun x _ => μ.nonnegative x)
    (fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _))
    (fun x _ => by ring_nf; exact le_rfl)
  simpa only [μ.normalized, one_mul, FiniteDistribution.expectation] using h

theorem apply_assignment_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    0 ≤ K.apply (assignment labels) y b := by
  rw [apply_assignment]
  exact (K.inner y).probability_nonnegative (fun x => K.accepts x y (labels x) b)

/-- The projected distribution has total mass at most one; missing mass is the
possibility that a partial projection rejects the chosen left answer. -/
theorem sum_apply_assignment_le_one (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) :
    (∑ b, K.apply (assignment labels) y b) ≤ 1 := by
  classical
  simp only [apply_assignment]
  rw [Finset.sum_comm, ← (K.inner y).normalized]
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ b, K.accepts x y (labels x) b = true
  · obtain ⟨b₀, hb₀⟩ := hex
    have hiff : ∀ b, K.accepts x y (labels x) b = true ↔ b = b₀ := by
      intro b
      constructor
      · intro hb
        exact K.projection x y (labels x) b b₀ hb hb₀
      · rintro rfl
        exact hb₀
    simp only [hiff]
    simp
  · have hnone : ∀ b, K.accepts x y (labels x) b ≠ true := by
      intro b hb
      exact hex ⟨b, hb⟩
    simpa [hnone] using (K.inner y).nonnegative x

theorem success_eq_outer_apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s =
      K.outer.expectation (fun y => K.apply (assignment s.1) y (s.2 y)) := by
  classical
  simp only [Game.success, Game.wins, toGame, FiniteDistribution.probability,
    FiniteDistribution.expectation, apply_assignment, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : K.accepts x y (s.1 x) (s.2 y) = true <;> simp [h]

theorem success_sq_le_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s ^ 2 ≤ K.assignmentEnergy s.1 := by
  rw [success_eq_outer_apply]
  calc
    _ ≤ K.outer.expectation
        (fun y => K.apply (assignment s.1) y (s.2 y) ^ 2) :=
      sq_expectation_le_expectation_sq K.outer _
    _ ≤ K.assignmentEnergy s.1 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      exact Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ (s.2 y))

theorem value_sq_le_collisionValue [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.toGame.value ^ 2 ≤ K.collisionValue := by
  obtain ⟨s, hs⟩ := K.toGame.exists_optimal_strategy
  rw [← hs]
  exact (K.success_sq_le_assignmentEnergy s).trans (K.assignmentEnergy_le_collisionValue s.1)

/-- Choose the actual best right answer separately at each right question. -/
theorem exists_best_response [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    ∃ answers : Q₂ → A₂, ∀ y b,
      K.apply (assignment labels) y b ≤ K.apply (assignment labels) y (answers y) := by
  classical
  have h : ∀ y, ∃ b : A₂, ∀ b',
      K.apply (assignment labels) y b' ≤ K.apply (assignment labels) y b := by
    intro y
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset A₂)) Finset.univ_nonempty
      (fun b => K.apply (assignment labels) y b)
    refine ⟨b, fun b' => ?_⟩
    rw [← hb]
    exact Finset.le_sup' _ (Finset.mem_univ b')
  exact ⟨fun y => Classical.choose (h y), fun y b => Classical.choose_spec (h y) b⟩

theorem assignmentEnergy_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.toGame.value := by
  obtain ⟨answers, hanswers⟩ := K.exists_best_response labels
  calc
    _ ≤ K.toGame.success (labels, answers) := by
      rw [success_eq_outer_apply]
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      calc
        _ ≤ ∑ b, K.apply (assignment labels) y b *
            K.apply (assignment labels) y (answers y) := by
          apply Finset.sum_le_sum
          intro b _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (hanswers y b)
            (K.apply_assignment_nonneg labels y b)
        _ = (∑ b, K.apply (assignment labels) y b) *
            K.apply (assignment labels) y (answers y) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * K.apply (assignment labels) y (answers y) :=
          mul_le_mul_of_nonneg_right (K.sum_apply_assignment_le_one labels y)
            (K.apply_assignment_nonneg labels y (answers y))
        _ = _ := one_mul _
    _ ≤ K.toGame.value := K.toGame.success_le_value _

theorem collisionValue_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.collisionValue ≤ K.toGame.value :=
  (K.collisionValue_le_iff _).mpr K.assignmentEnergy_le_value

theorem collisionValue_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : K.collisionValue ≤ 1 :=
  K.collisionValue_le_value.trans K.toGame.value_le_one

/-! The alphabet-independent high-value bound for the actual projection
operator. Positive vectors are determinized, padded, and rounded using proved
finite constructions. No rounding or repetition hypothesis is exposed. -/

private theorem distribution_nonempty_inline_RoundingKernel {T : Type*} [Fintype T]
    (μ : FiniteDistribution T) : Nonempty T := by
  by_contra h
  have : IsEmpty T := not_nonempty_iff.mp h
  have hz : (∑ t, μ.weight t) = 0 := by simp
  linarith [μ.normalized]

/-- Unit mass form of the Dinur--Steurer positive-vector approximation bound.
The loss is independent of both alphabets and of the auxiliary dimension. -/
theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty_inline_RoundingKernel K.outer
  let : Nonempty Q₁ := distribution_nonempty_inline_RoundingKernel
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end ProjectionKernel

/-!
Finite-sum tensor factorization used by projection-game collision operators.
No restriction to coordinatewise strategies occurs: `f` below is an arbitrary
function of both input questions and both input answers.
-/

section

open scoped BigOperators

variable {X A Y B U D Z C I : Type*}
  [Fintype X] [Fintype A] [Fintype U] [Fintype D] [Fintype I]

/-- Apply a finite real kernel. Output indices need no finiteness assumption. -/
def kernelApply (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (y : Y) (b : B) : ℝ :=
  ∑ x, ∑ a, K y b x a * f x a

/-- Independent tensor of two kernels. -/
def tensorKernel (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (yz : Y × Z) (bc : B × C) (xu : X × U) (ad : A × D) : ℝ :=
  K yz.1 bc.1 xu.1 ad.1 * L yz.2 bc.2 xu.2 ad.2

/-- Applying the tensor first applies `L` separately for every fixed input of
`K`, and then applies `K`. This is valid for arbitrary coupled inputs. -/
theorem kernelApply_tensor
    (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (f : (X × U) → (A × D) → ℝ) (y : Y) (z : Z) (b : B) (c : C) :
    kernelApply (tensorKernel K L) f (y,z) (b,c) =
      kernelApply K (fun x a => kernelApply L (fun u d => f (x,u) (a,d)) z c) y b := by
  classical
  simp only [kernelApply, tensorKernel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, mul_assoc]

theorem kernelApply_nonnegative
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ)
    (hK : ∀ y b x a, 0 ≤ K y b x a) (hf : ∀ x a, 0 ≤ f x a)
    (y : Y) (b : B) : 0 ≤ kernelApply K f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (hK y b x a) (hf x a)

/-- Summing a family of input functions commutes with the finite operator. -/
theorem kernelApply_sum
    (K : Y → B → X → A → ℝ) (f : I → X → A → ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => ∑ i, f i x a) y b =
      ∑ i, kernelApply K (f i) y b := by
  classical
  simp only [kernelApply, Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ i, K y b x a * f i x a) =
        ∑ x, ∑ i, ∑ a, K y b x a * f i x a := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem kernelApply_smul
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (r : ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => r * f x a) y b = r * kernelApply K f y b := by
  simp only [kernelApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm _ _ _

omit [Fintype X] in
/-- Marginalizing the first answer of a joint input strategy after applying
the second kernel is the same as applying the kernel to the answer marginal. -/
theorem kernelApply_slice_mass
    (L : Z → C → U → D → ℝ) (f : (X × U) → (A × D) → ℝ)
    (x : X) (z : Z) (c : C) :
    (∑ a, kernelApply L (fun u d => f (x,u) (a,d)) z c) =
      kernelApply L (fun u d => ∑ a, f (x,u) (a,d)) z c := by
  symm
  exact kernelApply_sum L (fun a u d => f (x,u) (a,d)) z c

end
namespace ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Ω I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Ω] [Fintype I]

/-! Exact tensor identities for normalized finite projection kernels. -/

/-- The coefficient form of the conditional projection operator. -/
def coefficients (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (b : A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner y).weight x * if K.accepts x y a b then 1 else 0

theorem apply_eq_kernelApply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply f y b = kernelApply K.coefficients f y b := by
  classical
  unfold apply kernelApply coefficients
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : K.accepts x y a b = true <;> simp [h]

theorem apply_nonnegative (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (hf : ∀ x a, 0 ≤ f x a) (y : Q₂) (b : A₂) :
    0 ≤ K.apply f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((K.inner y).nonnegative x)
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hf x a
  · exact le_rfl

theorem apply_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : I → Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => ∑ i, f i x a) y b = ∑ i, K.apply (f i) y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_sum _ _ _ _

theorem apply_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => r * f x a) y b = r * K.apply f y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_smul _ _ _ _ _

/-- Independent product of the outer and conditional laws. -/
def product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    ProjectionKernel (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  outer := K.outer.product H.outer
  inner q := (K.inner q.1).product (H.inner q.2)
  accepts x y a b := K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2
  projection x y a b b' hb hb' := by
    have h₁ := Bool.and_eq_true_iff.mp hb
    have h₂ := Bool.and_eq_true_iff.mp hb'
    exact Prod.ext (K.projection _ _ _ _ _ h₁.1 h₂.1)
      (H.projection _ _ _ _ _ h₁.2 h₂.2)

theorem coefficients_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).coefficients = tensorKernel K.coefficients H.coefficients := by
  funext yz bc xu ad
  unfold coefficients product tensorKernel FiniteDistribution.product
  by_cases hk : K.accepts xu.1 yz.1 ad.1 bc.1 = true <;>
    by_cases hh : H.accepts xu.2 yz.2 ad.2 bc.2 = true <;> simp [hk, hh]

/-- Arbitrary product inputs factor through the second game operator. -/
theorem apply_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (f : (Q₁ × R₁) → (A₁ × B₁) → ℝ)
    (y : Q₂) (z : R₂) (b : A₂) (c : B₂) :
    (K.product H).apply f (y,z) (b,c) =
      K.apply (fun x a => H.apply (fun u d => f (x,u) (a,d)) z c) y b := by
  simp_rw [apply_eq_kernelApply]
  rw [coefficients_product]
  exact kernelApply_tensor _ _ _ _ _ _ _

/-- The kernel tensor realizes the ordinary independent conjunction game. -/
theorem toGame_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).toGame = MaxCutGames.Repetition.product K.toGame H.toGame := by
  have hquestions : (K.product H).toGame.questions =
      (MaxCutGames.Repetition.product K.toGame H.toGame).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change (K.outer.weight q.2.1 * H.outer.weight q.2.2) *
      ((K.inner q.2.1).weight q.1.1 * (H.inner q.2.2).weight q.1.2) =
      (K.outer.weight q.2.1 * (K.inner q.2.1).weight q.1.1) *
        (H.outer.weight q.2.2 * (H.inner q.2.2).weight q.1.2)
    ring
  exact congrArg
    (fun questions : FiniteDistribution ((Q₁ × R₁) × (Q₂ × R₂)) =>
      ({ questions := questions
         accepts := fun x y a b =>
           K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2 } :
        Game (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂))) hquestions

/-!
The tensor-domination reduction before the Dinur--Steurer rounding theorem.
Every deterministic strategy for the product gives a nonnegative vector table
for the first kernel. Its energy is exactly the product collision energy, and
each input-question mass is bounded by the second kernel's collision value.
-/

/-- Apply the second game to a fixed first question and first answer. The
square-root factor changes its weighted output space into counting measure. -/
def tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁))
    (ω : R₂ × B₂) (x : Q₁) (a : A₁) : ℝ :=
  Real.sqrt (H.outer.weight ω.1) *
    H.apply (fun u d => assignment labels (x,u) (a,d)) ω.1 ω.2

omit [Fintype Q₁] [Fintype A₁] in
theorem tensorSlice_nonnegative (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) (a : A₁) :
    0 ≤ H.tensorSlice labels ω x a := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply H.apply_nonnegative
  intro u d
  unfold assignment
  split
  · exact zero_le_one
  · exact le_rfl

omit [Fintype Q₁] [Fintype R₁] [Fintype B₁] in
/-- Marginalizing the first label of a deterministic product strategy leaves
the deterministic second-label strategy. -/
theorem sum_assignment_product (labels : (Q₁ × R₁) → (A₁ × B₁))
    (x : Q₁) (u : R₁) (d : B₁) :
    (∑ a, assignment labels (x,u) (a,d)) =
      assignment (fun r => (labels (x,r)).2) u d := by
  classical
  by_cases h : (labels (x,u)).2 = d <;> simp [assignment, Prod.ext_iff, h]

omit [Fintype Q₁] in
theorem tensorSlice_label_mass (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) :
    (∑ a, H.tensorSlice labels ω x a) =
      Real.sqrt (H.outer.weight ω.1) *
        H.apply (assignment (fun r => (labels (x,r)).2)) ω.1 ω.2 := by
  unfold tensorSlice
  rw [← Finset.mul_sum, ← apply_sum]
  simp_rw [sum_assignment_product]

omit [Fintype Q₁] in
/-- The fiber mass is an actual collision energy of the second game, not a
free normalization assumption. -/
theorem vectorMass_tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x =
      H.assignmentEnergy (fun r => (labels (x,r)).2) := by
  classical
  unfold vectorMass assignmentEnergy energy
  simp_rw [tensorSlice_label_mass, mul_pow]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sq_sqrt (H.outer.nonnegative y), Finset.mul_sum]

omit [Fintype Q₁] in
theorem vectorMass_tensorSlice_le [Nonempty B₁]
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x ≤ H.collisionValue := by
  rw [vectorMass_tensorSlice]
  exact H.assignmentEnergy_le_collisionValue _

/-- Exact Hilbert-norm factorization, with every marginal weight retained. -/
theorem vectorEnergy_tensorSlice (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) :
    K.vectorEnergy (H.tensorSlice labels) = (K.product H).assignmentEnergy labels := by
  classical
  let p := fun y z b c =>
    K.apply (fun x a => H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b ^ 2
  have hlhs : K.vectorEnergy (H.tensorSlice labels) =
      ∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [vectorEnergy, energy, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change K.outer.weight y *
      (K.apply (fun x a => Real.sqrt (H.outer.weight z) *
        H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b) ^ 2 = _
    rw [apply_smul, mul_pow, Real.sq_sqrt (H.outer.nonnegative z)]
    exact (mul_assoc _ _ _).symm
  have hrhs : (K.product H).assignmentEnergy labels =
      ∑ y, ∑ z, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [assignmentEnergy, energy, product, FiniteDistribution.product,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact congrArg (fun r : ℝ => r ^ 2)
      (apply_product K H (assignment labels) y z b c)
  rw [hlhs, hrhs]
  calc
    (∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c) =
        ∑ z, ∑ y, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

omit [Fintype Q₁] in
theorem vectorMass_smul (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) (x : Q₁) :
    vectorMass (fun ω x a => r * f ω x a) x = r ^ 2 * vectorMass f x := by
  unfold vectorMass
  simp_rw [← Finset.mul_sum, mul_pow]
  exact (Finset.mul_sum _ _ _).symm

theorem energy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) :
    K.energy (fun x a => r * f x a) = r ^ 2 * K.energy f := by
  unfold energy
  simp_rw [apply_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_left_comm _ _ _

theorem vectorEnergy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) :
    K.vectorEnergy (fun ω x a => r * f ω x a) = r ^ 2 * K.vectorEnergy f := by
  unfold vectorEnergy
  simp_rw [energy_smul]
  exact (Finset.mul_sum _ _ _).symm

omit [Fintype Q₁] in
theorem entry_eq_zero_of_vectorMass_nonpositive
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) (ω : Ω) (x : Q₁) (a : A₁) :
    f ω x a = 0 := by
  classical
  have hsquare : (∑ b, f ω x b) ^ 2 ≤ vectorMass f x :=
    Finset.single_le_sum (fun τ _ => sq_nonneg (∑ b, f τ x b)) (Finset.mem_univ ω)
  have hsum : ∑ b, f ω x b = 0 := by
    nlinarith [hmass x, sq_nonneg (∑ b, f ω x b)]
  have hentry : f ω x a ≤ ∑ b, f ω x b :=
    Finset.single_le_sum (fun b _ => hf ω x b) (Finset.mem_univ a)
  rw [hsum] at hentry
  exact le_antisymm hentry (hf ω x a)

theorem vectorEnergy_eq_zero_of_mass_nonpositive
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) : K.vectorEnergy f = 0 := by
  have hfzero : f = fun _ _ _ => 0 := by
    funext ω x a
    exact entry_eq_zero_of_vectorMass_nonpositive f hf hmass ω x a
  rw [hfzero]
  simp [vectorEnergy, energy, apply]

/-- A unit-mass estimate extends to any nonnegative mass bound, including
zero. The hypothesis is precisely the unit-mass analytic estimate being
normalized; the normalization itself assumes no repetition bound. -/
theorem vectorEnergy_le_of_unit_bound
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (ρ C : ℝ)
    (unit_bound : ∀ f : Ω → Q₁ → A₁ → ℝ,
      (∀ ω x a, 0 ≤ f ω x a) → (∀ x, vectorMass f x ≤ 1) → K.vectorEnergy f ≤ ρ)
    (hC : 0 ≤ C) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ C) :
    K.vectorEnergy f ≤ ρ * C := by
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · have hCzero : C = 0 := hzero.symm
    subst C
    rw [K.vectorEnergy_eq_zero_of_mass_nonpositive f hf hmass, mul_zero]
  · have hsqrt : 0 ≤ (Real.sqrt C)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg C)
    have hscale : ((Real.sqrt C)⁻¹) ^ 2 = C⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hC]
    have hnorm : ∀ x, vectorMass (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a) x ≤ 1 := by
      intro x
      rw [vectorMass_smul, hscale]
      have h := mul_le_mul_of_nonneg_left (hmass x) (inv_nonneg.mpr hC)
      simpa [ne_of_gt hpositive] using h
    have hbound := unit_bound (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a)
      (fun ω x a => mul_nonneg hsqrt (hf ω x a)) hnorm
    rw [vectorEnergy_smul, hscale] at hbound
    have h := mul_le_mul_of_nonneg_left hbound hC
    simpa [← mul_assoc, ne_of_gt hpositive, mul_comm C ρ] using h

/-!
Collision norms are unchanged by bijective encodings of either player's
questions and answers. The distributions, acceptance predicate, and assignment
tables are transported together. This provides the finite-tuple regrouping
needed to pass from one product step to arbitrary parallel repetition.
-/

/-- Transport both normalized question laws and the projection predicate. -/
def reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) : ProjectionKernel R₁ R₂ B₁ B₂ where
  outer := K.outer.transport eQ₂
  inner y := (K.inner (eQ₂.symm y)).transport eQ₁
  accepts x y a b := K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
  projection := by
    intro x y a b b' hb hb'
    exact eA₂.symm.injective (K.projection _ _ _ _ _ hb hb')

/-- Reindexing the operator equals pulling back its assignment table. -/
theorem apply_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂)
    (f : R₁ → B₁ → ℝ) (y : R₂) (b : B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).apply f y b =
      K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) := by
  classical
  unfold apply
  change (∑ x, (K.inner (eQ₂.symm y)).weight (eQ₁.symm x) *
    ∑ a, if K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
      then f x a else 0) = _
  refine Fintype.sum_equiv eQ₁.symm _ _ ?_
  intro x
  simp only [Equiv.apply_symm_apply]
  congr 1
  refine Fintype.sum_equiv eA₁.symm _ _ ?_
  intro a
  simp only [Equiv.apply_symm_apply]

theorem energy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (f : R₁ → B₁ → ℝ) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).energy f =
      K.energy (fun x a => f (eQ₁ x) (eA₁ a)) := by
  classical
  unfold energy
  simp_rw [apply_reindex]
  change (∑ y, K.outer.weight (eQ₂.symm y) *
    ∑ b, K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) ^ 2) = _
  refine Fintype.sum_equiv eQ₂.symm _ _ ?_
  intro y
  congr 1
  exact Fintype.sum_equiv eA₂.symm _ _ (fun _ => rfl)

theorem assignmentEnergy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (labels : R₁ → B₁) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy labels =
      K.assignmentEnergy (fun x => eA₁.symm (labels (eQ₁ x))) := by
  classical
  unfold assignmentEnergy
  rw [energy_reindex]
  congr 1
  funext x a
  unfold assignment
  have h : labels (eQ₁ x) = eA₁ a ↔ eA₁.symm (labels (eQ₁ x)) = a := by
    constructor
    · intro ha
      rw [ha, Equiv.symm_apply_apply]
    · intro ha
      calc
        labels (eQ₁ x) = eA₁ (eA₁.symm (labels (eQ₁ x))) :=
          (eA₁.apply_symm_apply _).symm
        _ = eA₁ a := congrArg eA₁ ha
  rw [h]

/-- No strategy is lost under bijective question and answer encodings. -/
theorem collisionValue_reindex [Nonempty A₁] [Nonempty B₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue = K.collisionValue := by
  classical
  apply le_antisymm
  · apply ((K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue_le_iff _).2
    intro labels
    rw [assignmentEnergy_reindex]
    exact K.assignmentEnergy_le_collisionValue _
  · apply (K.collisionValue_le_iff _).2
    intro labels
    have h := (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy_le_collisionValue
      (fun x => eA₁ (labels (eQ₁.symm x)))
    simpa only [assignmentEnergy_reindex, Equiv.symm_apply_apply] using h

end ProjectionKernel

end

end MaxCutGames.Repetition

end OAI
