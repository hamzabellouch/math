import Mathlib
import OAI.Computability.DirectedFeedback.Games.Collision

namespace OAI


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

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

end ProjectionKernel
end
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel
open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

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

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) : ProjectionKernel R₁ R₂ B₁ B₂ where
  outer := K.outer.transport eQ₂
  inner y := (K.inner (eQ₂.symm y)).transport eQ₁
  accepts x y a b := K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
  projection := by
    intro x y a b b' hb hb'
    exact eA₂.symm.injective (K.projection _ _ _ _ _ hb hb')

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

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    ProjectionKernel (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { outer := K.outer.iid n
      inner := fun y => FiniteDistribution.table (fun i : Fin n => K.inner (y i))
      accepts := fun x y a b => decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)
      projection := by
        intro x y a b b' hb hb'
        simp only [decide_eq_true_eq] at hb hb'
        funext i
        exact K.projection _ _ _ _ _ (hb i) (hb' i) }

@[simp] theorem repetition_accepts_iff (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (K.repetition n).accepts x y a b = true ↔
      ∀ i, K.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

@[simp] theorem toGame_repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition n).toGame = K.toGame.repetition n := by
  classical
  have hq : (K.repetition n).toGame.questions = (K.toGame.repetition n).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change ((∏ i, K.outer.weight (q.2 i)) *
        (∏ i, (K.inner (q.2 i)).weight (q.1 i))) =
      ∏ i, K.outer.weight (q.2 i) * (K.inner (q.2 i)).weight (q.1 i)
    exact Finset.prod_mul_distrib.symm
  change Game.mk (K.repetition n).toGame.questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)) =
    Game.mk (K.toGame.repetition n).questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true))
  rw [hq]

theorem eq_of_data_eq {K H : ProjectionKernel Q₁ Q₂ A₁ A₂}
    (houter : K.outer = H.outer) (hinner : K.inner = H.inner)
    (haccepts : K.accepts = H.accepts) : K = H := by
  cases K
  cases H
  cases houter
  cases hinner
  cases haccepts
  rfl

theorem repetition_succ (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    K.repetition (n + 1) =
      (K.product (K.repetition n)).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₂))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₂)) := by
  classical
  apply eq_of_data_eq
  · apply FiniteDistribution.eq_of_weight_eq
    intro y
    change (∏ i : Fin (n + 1), K.outer.weight (y i)) =
      K.outer.weight (y 0) * ∏ i : Fin n, K.outer.weight (y i.succ)
    exact Fin.prod_univ_succ _
  · funext y
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change (∏ i : Fin (n + 1), (K.inner (y i)).weight (x i)) =
      (K.inner (y 0)).weight (x 0) *
        ∏ i : Fin n, (K.inner (y i.succ)).weight (x i.succ)
    exact Fin.prod_univ_succ _
  · funext x y a b
    apply Bool.eq_iff_iff.mpr
    change (decide (∀ i : Fin (n + 1), K.accepts (x i) (y i) (a i) (b i) = true) = true) ↔
      (K.accepts (x 0) (y 0) (a 0) (b 0) &&
        decide (∀ i : Fin n, K.accepts (x i.succ) (y i.succ) (a i.succ) (b i.succ) = true)) = true
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨hzero, hsucc⟩ i
      exact Fin.cases hzero hsucc i

theorem collisionValue_repetition_succ [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition (n + 1)).collisionValue =
      (K.product (K.repetition n)).collisionValue := by
  rw [repetition_succ, collisionValue_reindex]

theorem collisionValue_repetition_zero_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    (K.repetition 0).collisionValue ≤ 1 :=
  (K.repetition 0).collisionValue_le_one

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

def revealedProductWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) (y : ι → β) : ℝ :=
  ∏ i, weight i (x i) (y i) *
    (if mask i then (if y i = fixedRight i then 1 else 0)
     else (if x i = fixedLeft i then 1 else 0))

def revealedLeftWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) : ℝ :=
  ∏ i, if mask i then weight i (x i) (fixedRight i)
    else (if x i = fixedLeft i then 1 else 0)

def revealedRightWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (y : ι → β) : ℝ :=
  ∏ i, if mask i then (if y i = fixedRight i then 1 else 0)
    else weight i (fixedLeft i) (y i)

theorem revealedProductWeight_factorizes (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) (y : ι → β) :
    revealedProductWeight weight mask fixedLeft fixedRight x y =
      revealedLeftWeight weight mask fixedLeft fixedRight x *
        revealedRightWeight weight mask fixedLeft fixedRight y := by
  unfold revealedProductWeight revealedLeftWeight revealedRightWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hm : mask i = true
  · by_cases hy : y i = fixedRight i <;> simp [hm, hy]
  · by_cases hx : x i = fixedLeft i <;> simp [hm, hx]

theorem revealedProductWeight_local_restrictions
    (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β)
    (leftTest : (ι → α) → ℝ) (rightTest : (ι → β) → ℝ)
    (x : ι → α) (y : ι → β) :
    revealedProductWeight weight mask fixedLeft fixedRight x y * leftTest x * rightTest y =
      (revealedLeftWeight weight mask fixedLeft fixedRight x * leftTest x) *
      (revealedRightWeight weight mask fixedLeft fixedRight y * rightTest y) := by
  rw [revealedProductWeight_factorizes]
  ring

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

theorem normalized_productWeight (left : X → ℝ) (right : Y → ℝ)
    (hleft : 0 < ∑ x, left x) (hright : 0 < ∑ y, right y) (xy : X × Y) :
    normalizedWeight (fun z : X × Y => left z.1 * right z.2) xy =
      normalizedWeight left xy.1 * normalizedWeight right xy.2 := by
  unfold normalizedWeight
  rw [productWeight_mass]
  field_simp

theorem normalized_rectangle_restriction
    (left : X → ℝ) (right : Y → ℝ) (leftTest : X → ℝ) (rightTest : Y → ℝ)
    (hleft : 0 < ∑ x, left x * leftTest x)
    (hright : 0 < ∑ y, right y * rightTest y) (xy : X × Y) :
    normalizedWeight
      (fun z : X × Y => left z.1 * right z.2 * leftTest z.1 * rightTest z.2) xy =
      normalizedWeight (fun x => left x * leftTest x) xy.1 *
      normalizedWeight (fun y => right y * rightTest y) xy.2 := by
  have hfun : (fun z : X × Y => left z.1 * right z.2 * leftTest z.1 * rightTest z.2) =
      (fun z : X × Y => (left z.1 * leftTest z.1) * (right z.2 * rightTest z.2)) := by
    funext z
    ring
  rw [hfun]
  exact normalized_productWeight _ _ hleft hright xy

end

end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) : FiniteDistribution X :=
  if h : 0 < ∑ x, w x then
    { weight := normalizedWeight w
      nonnegative := (normalizedWeight_isProbability w hw h).1
      normalized := (normalizedWeight_isProbability w hw h).2 }
  else fallback

theorem sum_mul_normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) (x : X) :
    (∑ z, w z) * (normalizeOr w hw fallback).weight x = w x := by
  classical
  have hs : 0 ≤ ∑ z, w z := Finset.sum_nonneg (fun z _ => hw z)
  by_cases h : 0 < ∑ z, w z
  · simp only [normalizeOr, dite_eq_left h, normalizedWeight]
    field_simp
  · have hz : ∑ z, w z = 0 := le_antisymm (le_of_not_gt h) hs
    have hx : w x = 0 := by
      apply le_antisymm _ (hw x)
      have hl := Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ x)
      simpa only [hz] using hl
    simp [normalizeOr, hz, hx]

theorem local_completion_recombination
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (x : X) (y : Y) :
    (c * (∑ z, left z) * (∑ z, right z)) *
      ((normalizeOr left hl defaultLeft).weight x *
        (normalizeOr right hr defaultRight).weight y) = c * left x * right y := by
  calc
    _ = c * ((∑ z, left z) * (normalizeOr left hl defaultLeft).weight x) *
        ((∑ z, right z) * (normalizeOr right hr defaultRight).weight y) := by ring
    _ = _ := by rw [sum_mul_normalizeOr, sum_mul_normalizeOr]

theorem factorized_completion_row
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (xy : X × Y) :
    (∑ z : X × Y, c * left z.1 * right z.2) *
      ((normalizeOr left hl defaultLeft).product
        (normalizeOr right hr defaultRight)).weight xy = c * left xy.1 * right xy.2 := by
  have hm : (∑ z : X × Y, c * left z.1 * right z.2) =
      c * (∑ z, left z) * (∑ z, right z) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [productWeight_mass]
  rw [hm]
  exact local_completion_recombination left right hl hr defaultLeft defaultRight c xy.1 xy.2

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def leftQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₁ where
  weight x := ∑ y, G.questions.weight (x, y)
  nonnegative x := Finset.sum_nonneg fun y _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [← Fintype.sum_prod_type]
    exact G.questions.normalized

def rightQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₂ where
  weight y := ∑ x, G.questions.weight (x, y)
  nonnegative y := Finset.sum_nonneg fun x _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact G.questions.normalized

def leftGivenRight (G : Game Q₁ Q₂ A₁ A₂) (y : Q₂) : FiniteDistribution Q₁ :=
  DFVSGames.Foundations.Repetition.normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G)

theorem rightQuestionMarginal_mul_leftGivenRight
    (G : Game Q₁ Q₂ A₁ A₂) (x : Q₁) (y : Q₂) :
    (rightQuestionMarginal G).weight y * (leftGivenRight G y).weight x =
      G.questions.weight (x, y) :=
  DFVSGames.Foundations.Repetition.sum_mul_normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G) x

def kernelOfGame (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    ProjectionKernel Q₁ Q₂ A₁ A₂ where
  outer := rightQuestionMarginal G
  inner := leftGivenRight G
  accepts := G.accepts
  projection := hG

@[simp] theorem kernelOfGame_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (q : Q₁ × Q₂) :
    (kernelOfGame G hG).toGame.questions.weight q = G.questions.weight q :=
  rightQuestionMarginal_mul_leftGivenRight G q.1 q.2

@[simp] theorem toGame_kernelOfGame
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame = G := by
  have hq : (kernelOfGame G hG).toGame.questions = G.questions :=
    FiniteDistribution.eq_of_weight_eq (kernelOfGame_question_weight G hG)
  calc
    _ = { questions := G.questions, accepts := G.accepts } := by
      change Game.mk (kernelOfGame G hG).toGame.questions G.accepts =
        Game.mk G.questions G.accepts
      rw [hq]
    _ = G := by cases G; rfl

@[simp] theorem kernelOfGame_success
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (kernelOfGame G hG).toGame.success strategy = G.success strategy := by
  rw [toGame_kernelOfGame]

@[simp] theorem kernelOfGame_value [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame.value = G.value := by
  rw [toGame_kernelOfGame]

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition

theorem sequence_le_power {r : ℝ} (hr : 0 ≤ r) (c : ℕ → ℝ)
    (hzero : c 0 ≤ 1) (hstep : ∀ n, c (n + 1) ≤ r * c n) :
    ∀ n, c n ≤ r ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        c (n + 1) ≤ r * c n := hstep n
        _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem squared_rate_le_dsRate_sq {gap : ℝ}
    (_hgap₀ : 0 ≤ gap) (_hgap₁ : gap ≤ 1) :
    1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
  dsimp [dsRate]
  nlinarith only [sq_nonneg (gap ^ 2)]

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]


open DFVSGames.Foundations.Games
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
  [Nonempty A₁] [Nonempty A₂] [Nonempty B₁] [Nonempty B₂]

omit [Nonempty B₂] in
theorem collisionValue_product_le_gap_rate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) :
    (K.product H).collisionValue ≤ (1 - gap ^ 2 / 8) * H.collisionValue := by
  apply ((K.product H).collisionValue_le_iff _).2
  intro labels
  rw [← vectorEnergy_tensorSlice]
  apply K.vectorEnergy_le_of_unit_bound (1 - gap ^ 2 / 8) H.collisionValue
    (fun f hf hmass => K.vectorEnergy_le_gap_rate f hf hmass hgap₀ hgap₁ hvalue)
    H.collisionValue_nonneg (H.tensorSlice labels)
    (H.tensorSlice_nonnegative labels) (H.vectorMass_tensorSlice_le labels)

theorem repetition_value_le_dsRate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) (n : ℕ) :
    (K.toGame.repetition n).value ≤ dsRate gap ^ n := by
  have hstep : ∀ m, (K.repetition (m + 1)).collisionValue ≤
      (1 - gap ^ 2 / 8) * (K.repetition m).collisionValue := by
    intro m
    rw [K.collisionValue_repetition_succ]
    exact K.collisionValue_product_le_gap_rate (K.repetition m) hgap₀ hgap₁ hvalue
  have h := rate_of_squared_collision_recurrence hgap₀ hgap₁
    (fun m => (K.repetition m).collisionValue)
    (fun m => (K.repetition m).toGame.value)
    K.collisionValue_repetition_zero_le_one hstep
    (fun m => (K.repetition m).value_sq_le_collisionValue) n
  simpa only [toGame_repetition] using h

end ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem projection_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    {gap : ℝ} (hgap₀ : 0 < gap) (hgap₁ : gap < 1)
    (hvalue : G.value ≤ 1 - gap) :
    (G.repetition n).value ≤ (1 - gap ^ 2 / 16) ^ n := by
  have h := (kernelOfGame G hG).repetition_value_le_dsRate hgap₀.le hgap₁.le
    (by simpa only [kernelOfGame_value] using hvalue) n
  simpa only [toGame_kernelOfGame, dsRate] using h

theorem projection_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    {gap : ℝ} (hgap₀ : 0 < gap) (hgap₁ : gap < 1)
    (hvalue : G.value ≤ 1 - gap)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    (G.repetition n).success strategy ≤ (1 - gap ^ 2 / 16) ^ n :=
  ((G.repetition n).success_le_value strategy).trans
    (projection_repetition_value G hG n hgap₀ hgap₁ hvalue)

theorem clean_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ (14 : ℝ) / 15) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 3600) ^ n := by
  have hv : G.value ≤ 1 - (1 : ℝ) / 15 := by convert hvalue using 1 ; norm_num
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 15) (by norm_num) (by norm_num) hv
  norm_num at h ⊢
  exact h

theorem final_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 10240000) ^ n := by
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 800) (by norm_num) (by norm_num) hvalue
  norm_num at h ⊢
  exact h

end
end DFVSGames.Repetition

end OAI
