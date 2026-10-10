import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.JointSampledComparison

namespace OAI

/-! # Simultaneous arithmetic replacement for concrete moving-giant slots -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotLine {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) : PolynomialGiantLine σ :=
  movingHistoryLine (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w

theorem movingSlotLine_degree {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (k d : ℕ)
    (hlen : path.length ≤ k) (hd : ∀ s ∈ path, s.lengthLE d) (hc : current.lengthLE d) :
    (movingSlotLine path current).a.totalDegree ≤ (k + 1) * d ∧
      (movingSlotLine path current).b.totalDegree ≤ (k + 1) * d := by
  have h := movingHistoryLine_degree (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w d
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs; exact t.polynomial_degree d (hd t ht))
    (current.polynomial_degree d hc).1 (current.polynomial_degree d hc).2.1
  have hb : ((path.map MovingSlotReversal.polynomial).length + 1) * d ≤ (k + 1) * d := by
    simpa only [List.length_map] using Nat.mul_le_mul_right d (Nat.add_le_add_right hlen 1)
  exact ⟨h.1.trans hb, h.2.trans hb⟩

theorem movingSlotLine_height {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (x : σ → ℝ) (k d : ℕ) (F T : ℝ)
    (hF : 1 ≤ F) (hT : 1 ≤ T) (hlen : path.length ≤ k)
    (hd : ∀ s ∈ path, s.lengthLE d ∧ s.frequencyLE F)
    (hc : current.lengthLE d ∧ current.frequencyLE F) (hx : ∀ i, |x i| ≤ T) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x
    |φ (movingSlotLine path current).a| ≤ (2 * (F * T ^ d)) ^ (k + 1) ∧
      |φ (movingSlotLine path current).b| ≤ (2 * (F * T ^ d)) ^ (k + 1) := by
  have hK : 1 ≤ F * T ^ d := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hT)
  have hh := movingHistoryLine_value (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w _ (F * T ^ d) (by linarith)
    (by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact t.polynomial_height x F T d (hd t ht).2 hT (hd t ht).1 hx)
    (current.polynomial_height x F T d hc.2 hT hc.1 hx).1
    (current.polynomial_height x F T d hc.2 hT hc.1 hx).2.1
  have hb : (2 * (F * T ^ d)) ^ ((path.map MovingSlotReversal.polynomial).length + 1) ≤
      (2 * (F * T ^ d)) ^ (k + 1) := by
    apply pow_le_pow_right₀ (by linarith)
    simpa only [List.length_map] using Nat.add_le_add_right hlen 1
  exact ⟨hh.1.trans hb, hh.2.trans hb⟩

theorem movingSlotLine_vars {σ : Type*} [DecidableEq σ]
    (path : List (MovingSlotReversal σ)) (current : MovingSlotReversal σ) (S : Finset σ)
    (hp : ∀ s ∈ path, (∀ i ∈ s.leftSlots, i ∈ S) ∧ (∀ i ∈ s.rightSlots, i ∈ S) ∧
      (∀ i ∈ s.compensationSlots, i ∈ S))
    (hc : (∀ i ∈ current.leftSlots, i ∈ S) ∧ (∀ i ∈ current.rightSlots, i ∈ S)) :
    (movingSlotLine path current).a.vars ⊆ S ∧ (movingSlotLine path current).b.vars ⊆ S := by
  have hsub (a : ℤ) (slots : List σ) (h : ∀ i ∈ slots, i ∈ S) :
      (movingSlotCoefficient a slots).vars ⊆ S :=
    (movingSlotCoefficient_vars a slots).trans (fun i hi => h i (List.mem_toFinset.mp hi))
  apply movingHistoryLine_vars_subset
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact ⟨hsub _ _ (hp t ht).2.1, hsub _ _ (hp t ht).1, hsub _ _ (hp t ht).2.2⟩
  · exact hsub _ _ hc.2
  · exact hsub _ _ hc.1

/-- All occurrence tests for all representative internal primes are replaced
at once, under the original independent slot priors. The multiplier remains
complex-valued. Independence follows from absence of the tested coordinate in
the actual slot lists, including every ancestor compensation list. -/
theorem moving_slot_joint_symbolic_comparison {A J O : Type*}
    [Fintype A] [Nonempty A] [Fintype J] [Fintype O] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin (n + 1))))
    (current : J → O → MovingSlotReversal (Fin (n + 1)))
    (base : J → O) (coordinate : J → Fin (n + 1))
    (k d : ℕ) (F T : ℝ) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hlen : ∀ j o, (path j o).length ≤ k)
    (hd : ∀ j o, (∀ s ∈ path j o, s.lengthLE d ∧ s.frequencyLE F) ∧
      (current j o).lengthLE d ∧ (current j o).frequencyLE F)
    (habsent : ∀ j o,
      (∀ s ∈ path j o, coordinate j ∉ s.leftSlots ∧ coordinate j ∉ s.rightSlots ∧
        coordinate j ∉ s.compensationSlots) ∧
      coordinate j ∉ (current j o).leftSlots ∧ coordinate j ∉ (current j o).rightSlots)
    (hvalues : ∀ a, |(value a : ℝ)| ≤ T)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coordinate j) a ≤ β)
    (hsize : ∀ j a, μ (coordinate j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (Ψ : (Fin (n + 1) → A) → (J × (Bool ⊕ O) → Bool) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hΨ : ∀ x flags, ‖Ψ x flags‖ ≤ B) :
    let tests := fun t : J × (Bool ⊕ O) =>
      lineTestPolynomials (fun o => movingSlotLine (path t.1 o) (current t.1 o)) (base t.1) t.2
    ‖∑ x, (productPrior μ x : ℂ) *
      (Ψ x (fun t => arithmeticTestFlag
        (prime (x (coordinate t.1)) ∣ (integerTestValue value (tests t) x).natAbs)) -
       Ψ x (fun t => arithmeticTestFlag (tests t = 0)))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card O)) *
        ((2 * ((k + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * T ^ d)) ^ (k + 1)) ^ 2) / V) * β) := by
  let lines := fun j o => movingSlotLine (path j o) (current j o)
  let tests := fun t : J × (Bool ⊕ O) => lineTestPolynomials (lines t.1) (base t.1) t.2
  let H := (2 * (F * T ^ d)) ^ (k + 1)
  have hH : 1 ≤ H := one_le_pow₀ (by
    have := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hT (n := d))
    linarith)
  have hdeg (t : J × (Bool ⊕ O)) : (tests t).totalDegree ≤ 2 * ((k + 1) * d) :=
    lineTestPolynomials_degree_le (lines t.1) (base t.1) _
      (fun o => movingSlotLine_degree _ _ k d (hlen _ _) (fun s hs => (hd _ _).1 s hs |>.1)
        (hd _ _).2.1) t.2
  have hheight (t : J × (Bool ⊕ O)) (x : Fin (n + 1) → A) :
      |(integerTestValue value (tests t) x : ℝ)| ≤ 2 * H ^ 2 := by
    rw [integerTestValue_real_cast]
    apply lineTestPolynomials_value_le (lines t.1) (base t.1) _ H hH
    intro o
    exact movingSlotLine_height _ _ _ k d F T hF hT (hlen _ _) (hd _ _).1 (hd _ _).2
      (fun i => hvalues (x i))
  have hab (t : J × (Bool ⊕ O)) : coordinate t.1 ∉ (tests t).vars := by
    let S : Finset (Fin (n + 1)) := Finset.univ.erase (coordinate t.1)
    have hl (o : O) : (lines t.1 o).a.vars ⊆ S ∧ (lines t.1 o).b.vars ⊆ S := by
      apply movingSlotLine_vars
      · intro s hs
        refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> apply Finset.mem_erase.mpr <;>
          refine ⟨?_, Finset.mem_univ _⟩
        · exact fun h => (habsent t.1 o).1 s hs |>.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).1 s hs |>.2.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).1 s hs |>.2.2 (h ▸ hi)
      · constructor <;> intro i hi <;> apply Finset.mem_erase.mpr <;>
          refine ⟨?_, Finset.mem_univ _⟩
        · exact fun h => (habsent t.1 o).2.1 (h ▸ hi)
        · exact fun h => (habsent t.1 o).2.2 (h ▸ hi)
    exact fun h => Finset.notMem_erase _ _
      (lineTestPolynomials_vars_subset (lines t.1) (base t.1) S hl t.2 h)
  have hh := joint_sampled_polynomial_comparison_le value hinj prime hpInj hprime tests
    (fun t => coordinate t.1) hab μ hμ hmass α β V (2 * H ^ 2) hα hβ hV
    (by nlinarith [sq_nonneg H]) hmax (fun t => hpmax t.1) (fun t => hsize t.1) hheight Ψ B hB hΨ
  apply hh.trans
  have hterm (t : J × (Bool ⊕ O)) :
      ((tests t).totalDegree : ℝ) * α + (Real.log (2 * H ^ 2) / V) * β ≤
        ((2 * ((k + 1) * d) : ℕ) : ℝ) * α + (Real.log (2 * H ^ 2) / V) * β := by
    have hd' : ((tests t).totalDegree : ℝ) ≤ ((2 * ((k + 1) * d) : ℕ) : ℝ) := by
      exact_mod_cast hdeg t
    exact add_le_add (mul_le_mul_of_nonneg_right hd' hα) le_rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hterm t)
  apply (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hB)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, H]
  ring

end Ostmann

end OAI
