import Mathlib
import OAI.Probability.BinarySweep.Processes.PointMassOne

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section IndependentLaw
variable {G Ω Ξ : Type*} [Fintype G] [Group G] [Fintype Ω] [Fintype Ξ]

def independentHistory (f : Ω → G) (n : ℕ) (c : Fin n → Ω) : G :=
  (List.ofFn (fun i => f (c i))).reverse.prod

omit [Fintype G] [Fintype Ω] in
lemma independentHistory_succ (f : Ω → G) (n : ℕ) (a : Ω) (c : Fin n → Ω) :
    independentHistory f (n + 1) (Fin.snoc c a) = f a * independentHistory f n c := by
  unfold independentHistory
  rw [List.ofFn_succ']
  simp

lemma finiteLaw_independentHistory [Nonempty Ω] (f : Ω → G) (n : ℕ) :
    finiteLaw (independentHistory f n) = convolutionPower (finiteLaw f) n := by
  induction n with
  | zero =>
    classical
    funext g
    simp [finiteLaw, independentHistory, convolutionPower, pointMassOne, eq_comm]
  | succ n ih =>
    let e : Ω × (Fin n → Ω) ≃ (Fin (n + 1) → Ω) := Fin.snocEquiv (fun _ => Ω)
    rw [← finiteLaw_reindex e]
    have he : (independentHistory f (n + 1)) ∘ e =
        fun a : Ω × (Fin n → Ω) => f a.1 * independentHistory f n a.2 := by
      funext a
      exact independentHistory_succ f n a.1 a.2
    rw [he, finiteLaw_independent_mul, ih]
    rfl

end IndependentLaw

section Assignments
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [Fintype I]

def Assigns (A B : I ↪ X) (σ : Equiv.Perm X) : Prop := ∀ i, σ (A i) = B i

lemma card_assignment_completions (A B : I ↪ X) :
    Fintype.card {σ : Equiv.Perm X // Assigns A B σ} =
      (Fintype.card X - Fintype.card I).factorial := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  have ha : Fintype.card (Set.range A) = Fintype.card I := Fintype.card_congr eA.symm
  have hb : Fintype.card (Set.range B) = Fintype.card I := Fintype.card_congr eB.symm
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro h x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using h i
      · intro h i
        simpa [e₀, eA, eB] using h (eA i))
  let c : ↥((Set.range A)ᶜ) ≃ ↥((Set.range B)ᶜ) := Fintype.equivOfCardEq (by
    change Fintype.card {x : X // x ∉ Set.range A} = Fintype.card {x : X // x ∉ Set.range B}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ha, hb])
  rw [Fintype.card_congr (e.trans (Equiv.Set.compl e₀)), Fintype.card_equiv c]
  change (Fintype.card {x : X // x ∉ Set.range A}).factorial = _
  rw [Fintype.card_subtype_compl, ha]

lemma uniform_assignment_probability (A B : I ↪ X) :
    (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  classical
  have hn : Fintype.card I ≤ Fintype.card X := Fintype.card_le_of_injective A A.injective
  have hcard : (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) =
      ((Fintype.card X - Fintype.card I).factorial : ℝ) := by
    exact_mod_cast card_assignment_completions A B
  have hsum : (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) *
        (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ := by
    simp [Fintype.card_subtype, Finset.sum_ite]
  rw [hsum, hcard, Fintype.card_perm,
    ← Nat.factorial_mul_descFactorial hn, Nat.cast_mul, mul_inv_rev]
  have hf : (((Fintype.card X - Fintype.card I).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (Fintype.card X - Fintype.card I))
  field_simp

end Assignments

lemma physicalLaw_eq_convolutionPower (d t : ℕ) :
    physicalLaw d t = convolutionPower (finiteLaw (physical d)) t :=
  finiteLaw_independentHistory (physical d) t

def sweepHistory (d t : ℕ) (coins : Fin t → SweepCoins d) : Equiv.Perm (Slot d) :=
  independentHistory (binarySweep d) t coins

lemma sweepLaw_eq_finiteLaw (d t : ℕ) : sweepLaw d t = finiteLaw (sweepHistory d t) :=
  (finiteLaw_independentHistory (binarySweep d) t).symm

def fromInitial {G : Type*} [Group G] (p : G → ℝ) (initial : G) : G → ℝ :=
  fun g => p (g * initial⁻¹)

lemma totalVariation_fromInitial {G : Type*} [Fintype G] [Group G]
    (p : G → ℝ) (initial : G) :
    totalVariation (fromInitial p initial) (uniformLaw G) = totalVariation p (uniformLaw G) := by
  unfold totalVariation fromInitial uniformLaw
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight initial⁻¹)
    (fun g => |p g - (Fintype.card G : ℝ)⁻¹|)

theorem fixed_dimension_sweep_convergence_fromInitial (d : ℕ)
    (initial : Equiv.Perm (Slot d)) :
    Filter.Tendsto (fun t => totalVariation (fromInitial (sweepLaw d t) initial)
      (uniformLaw (Equiv.Perm (Slot d)))) Filter.atTop (nhds 0) := by
  simp only [totalVariation_fromInitial]
  exact fixed_dimension_sweep_convergence d

def ConstantSweepMixingTarget : Prop :=
  ∃ w : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ initial : Equiv.Perm (Slot d),
      totalVariation (fromInitial (sweepLaw d w) initial)
        (uniformLaw (Equiv.Perm (Slot d))) < ε

def fallingCost (m u : ℕ) : ℝ := Real.log ((m : ℝ) ^ u / (m.descFactorial u : ℝ))

lemma fallingCost_sum {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = ∑ j ∈ Finset.range u, Real.log ((m : ℝ) / (m - j : ℕ)) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hdf : (0 : ℝ) < m.descFactorial u := by exact_mod_cast (Nat.descFactorial_pos.mpr hu)
  have hdiff (j : ℕ) (hj : j ∈ Finset.range u) : (m - j : ℕ) ≠ 0 := by
    simp only [Finset.mem_range] at hj
    omega
  have hlog (j : ℕ) (hj : j ∈ Finset.range u) :
      Real.log ((m : ℝ) / (m - j : ℕ)) = Real.log m - Real.log (m - j : ℕ) :=
    Real.log_div hmp.ne' (by exact_mod_cast hdiff j hj)
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp.ne') hdf.ne', Real.log_pow,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod, Real.log_prod (fun j hj => by exact_mod_cast hdiff j hj)]
  rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib]
  simp

lemma fallingCost_nonneg {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : 0 ≤ fallingCost m u := by
  rw [fallingCost_sum hm hu]
  apply Finset.sum_nonneg
  intro j hj
  have hdiff : (0 : ℝ) < (m - j : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt ((Finset.mem_range.mp hj).trans_le hu))
  apply Real.log_nonneg
  exact (le_div_iff₀ hdiff).mpr (by simp)

lemma prefix_sum_le_of_full_sum_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) (f : ℕ → ℝ)
    (hf : ∀ i < u, ∀ j, u ≤ j → j < m → f i ≤ f j)
    (hfull : ∑ j ∈ Finset.range m, f j ≤ m) :
    ∑ j ∈ Finset.range u, f j ≤ u := by
  have hc : ((m : ℝ) - u) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * ∑ j ∈ Finset.Ico u m, f j := by
    calc
      _ = ∑ i ∈ Finset.range u, ∑ _j ∈ Finset.Ico u m, f i := by
        simp [Nat.cast_sub hu, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hf i (Finset.mem_range.mp hi) j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      _ = _ := by simp
  have hsplit := Finset.sum_range_add_sum_Ico f hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : (0 : ℝ) ≤ u := by positivity
  nlinarith

lemma fallingCost_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : fallingCost m u ≤ u := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hfull : fallingCost m m ≤ m := by
    have hst := Stirling.le_log_factorial_stirling hm.ne'
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [fallingCost, Nat.descFactorial_self, Real.log_div (pow_ne_zero _ hmp.ne') (by positivity), Real.log_pow]
    linarith
  rw [fallingCost_sum hm hu]
  apply prefix_sum_le_of_full_sum_le hm hu
  · intro i hi j huj hjm
    apply Real.log_le_log
    · exact div_pos hmp (by exact_mod_cast Nat.sub_pos_of_lt (hi.trans_le hu))
    · apply div_le_div_of_nonneg_left hmp.le
      · exact_mod_cast Nat.sub_pos_of_lt hjm
      · exact_mod_cast Nat.sub_le_sub_left (hi.le.trans huj) m
  · rwa [← fallingCost_sum hm le_rfl]

attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

end BinaryCoordinateSweeps
end

end OAI
