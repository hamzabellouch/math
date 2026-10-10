import OAI.InformationTheory.QuantumCircuit.Pruning

namespace OAI

/-! Orthogonal product-basis spectral resolutions. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial

namespace QAC

lemma act_finset_sum {N : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Operator N) (ψ : State N) :
    act (∑ i ∈ s, P i) ψ = ∑ i ∈ s, act (P i) ψ := by
  simp [act, map_sum]

lemma projection_pythagoras {N : ℕ} {ι : Type} (s : Finset ι)
    (P : ι → Operator N) (ψ : State N)
    (hp : ∀ i ∈ s, IsStarProjection (P i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    ‖act (∑ i ∈ s, P i) ψ‖^2 = ∑ i ∈ s, ‖act (P i) ψ‖^2 := by
  classical
  have hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      inner ℂ (act (P i) ψ) (act (P j) ψ) = 0 := by
    intro i hi j hj hij
    calc
      _ = inner ℂ ψ (act (star (P i)) (act (P j) ψ)) := by
        simpa only [star_star] using (inner_act_right (star (P i)) ψ (act (P j) ψ)).symm
      _ = 0 := by rw [← act_mul, (hp i hi).isSelfAdjoint.star_eq, ho i hi j hj hij, act_zero, inner_zero_right]
  rw [act_finset_sum]
  have hh : inner ℂ (∑ i ∈ s, act (P i) ψ) (∑ i ∈ s, act (P i) ψ) =
      ∑ i ∈ s, inner ℂ (act (P i) ψ) (act (P i) ψ) := by
    simp only [inner_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact hc j hj i hi hji
    · exact fun h => (h hi).elim
  have hreal := congrArg Complex.re hh
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using hreal

lemma Count.restrict_operator_mul_pattern {N : ℕ} (M : Count N)
    (J F : Finset (Fin N)) (hF : F ⊆ M.support) :
    (M.restrict J).operator * M.pattern F = ((F ∩ J).card : ℝ) • M.pattern F := by
  classical
  rw [Count.operator, Finset.sum_mul]
  calc
    _ = ∑ i ∈ M.support ∩ J, if i ∈ F then M.pattern F else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact M.generator_mul_pattern i (Finset.mem_inter.mp hi).1 F
    _ = _ := by
      rw [Finset.sum_ite_mem]
      have heq : (M.support ∩ J) ∩ F = F ∩ J := by
        ext i
        simp only [Finset.mem_inter]
        constructor
        · tauto
        · intro hi; exact ⟨⟨hF hi.1, hi.2⟩, hi.1⟩
      rw [heq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]

lemma Count.restrict_operator_pow_mul_pattern {N : ℕ} (M : Count N)
    (J F : Finset (Fin N)) (hF : F ⊆ M.support) (k : ℕ) :
    (M.restrict J).operator^k * M.pattern F =
      (((F ∩ J).card : ℝ)^k) • M.pattern F := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, M.restrict_operator_mul_pattern J F hF, smul_smul]
    congr 1

lemma Count.restrict_polynomial_mul_pattern {N : ℕ} (M : Count N)
    (J F : Finset (Fin N)) (hF : F ⊆ M.support) (p : ℝ[X]) :
    (M.restrict J).polynomial p * M.pattern F =
      p.eval ((F ∩ J).card : ℝ) • M.pattern F := by
  classical
  rw [(M.restrict J).polynomial_eq_sum, Finset.sum_mul, Polynomial.eval_eq_sum, Polynomial.sum]
  simp_rw [smul_mul_assoc, M.restrict_operator_pow_mul_pattern J F hF, smul_smul]
  exact (Finset.sum_smul ..).symm

lemma Count.restrict_operator_expansion {N : ℕ} (M : Count N) (J : Finset (Fin N)) :
    (M.restrict J).operator = ∑ F ∈ M.support.powerset,
      ((F ∩ J).card : ℝ) • M.pattern F := by
  calc
    _ = (M.restrict J).operator * (∑ F ∈ M.support.powerset, M.pattern F) := by
      rw [M.sum_pattern, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      exact M.restrict_operator_mul_pattern J F (Finset.mem_powerset.mp hF)

lemma Count.restrict_high_expansion {N : ℕ} (M : Count N)
    (J : Finset (Fin N)) (r : ℝ) :
    (M.restrict J).high r = ∑ F ∈ M.support.powerset,
      if r ≤ ((F ∩ J).card : ℝ) then M.pattern F else 0 := by
  classical
  let s := Finset.range (N + 1)
  let p : ℝ[X] := Lagrange.interpolate s (fun k : ℕ => (k : ℝ))
    (fun k => if r ≤ (k : ℝ) then 1 else 0)
  have hp : ∀ k : ℕ, k ≤ N → p.eval (k : ℝ) = if r ≤ (k : ℝ) then 1 else 0 := by
    intro k hk
    exact Lagrange.eval_interpolate_at_node _ (by intro i _ j _ hij; exact_mod_cast hij)
      (by simp [s]; omega)
  have heq : (M.restrict J).high r = (M.restrict J).polynomial p := by
    rw [(M.restrict J).high_spectral]
    unfold Count.polynomial Count.spectral
    apply Finset.sum_congr rfl
    intro F hF
    have hk : F.card ≤ N := (Finset.card_le_card (Finset.mem_powerset.mp hF)).trans
      (by simpa using Finset.card_le_univ (M.restrict J).support)
    change (if r ≤ (F.card : ℝ) then (1 : ℝ) else 0) • _ = p.eval (F.card : ℝ) • _
    rw [hp F.card hk]
  rw [heq]
  calc
    _ = (M.restrict J).polynomial p * (∑ F ∈ M.support.powerset, M.pattern F) := by
      rw [M.sum_pattern, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      rw [M.restrict_polynomial_mul_pattern J F (Finset.mem_powerset.mp hF)]
      have hk : (F ∩ J).card ≤ N := (Finset.card_le_card Finset.inter_subset_left).trans
        (by simpa using Finset.card_le_univ F)
      rw [hp _ hk]
      split_ifs <;> simp

lemma expectation_pattern_sum {N : ℕ} (M : Count N) (ψ : State N)
    (c : Finset (Fin N) → ℝ) :
    (inner ℂ ψ (act (∑ F ∈ M.support.powerset, c F • M.pattern F) ψ)).re =
      ∑ F ∈ M.support.powerset, c F * outcomeMass M ψ F := by
  rw [act_finset_sum, inner_sum]
  simp only [act_real_smul]
  simp_rw [show ∀ F, (c F • act (M.pattern F) ψ : State N) =
    (c F : ℂ) • act (M.pattern F) ψ from fun _ => rfl,
    inner_smul_right, projection_inner_self _ (M.pattern_projection _)]
  simp [outcomeMass, -Complex.ofReal_pow]

lemma restriction_moment {N : ℕ} (M : Count N) (J : Finset (Fin N)) (ψ : State N) :
    meanCount (M.restrict J) ψ = ∑ F ∈ M.support.powerset,
      ((F ∩ J).card : ℝ) * outcomeMass M ψ F := by
  have ha : meanCount (M.restrict J) ψ =
      (inner ℂ ψ (act (M.restrict J).operator ψ)).re := by
    rw [(M.restrict J).operator_spectral]
    exact (expectation_pattern_sum (M.restrict J) ψ (fun F => F.card)).symm
  rw [ha, M.restrict_operator_expansion]
  exact expectation_pattern_sum M ψ _

theorem published_product_spectral_resolution : PublishedProductSpectralResolution where
  restriction := Count.restrict_high_expansion
  pythagoras := projection_pythagoras
  restriction_moment := restriction_moment

theorem regular_pruning_unconditional (d : ℕ)
    (m : ℕ → ℕ) (hm : Filter.Tendsto m Filter.atTop Filter.atTop) (hN : ∀ ν, 1 ≤ m ν)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (hs : ∀ ν, NonemptyGateSupports (l ν)) (P : ∀ ν, ProductInput (m ν)) :
    RegularTrajectory m (fun ν => pruneCircuit (l ν) (P ν).state) (fun ν => (P ν).state) ∧
    (∀ ν, (pruneCircuit (l ν) (P ν).state).length = (l ν).length) ∧
    (∀ ν, ‖act (evolution (l ν)) (P ν).state -
      act (evolution (pruneCircuit (l ν) (P ν).state)) (P ν).state‖ ≤
        2 * ((l ν).length : ℝ) * (m ν : ℝ)^(-2 : ℝ)) :=
  regular_pruning published_product_spectral_resolution d m hm hN l hl hs P

end QAC

end

end OAI
