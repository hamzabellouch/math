import OAI.NumberTheory.CubicMoment.Angular.AngularCoprimeLattice
import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeIdentity

namespace OAI

/-! Low-height angular cancellation for the literal squarefree,
coprime primary lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeCoprimeAngularLattice (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u ∧ IsCoprime r u then
    (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0

lemma coprimeAngularLattice_divisor (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (Y : ℝ) {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u ∧ IsCoprime r u then
      theta ℓ u*W (norm u/Y) else 0) =
      if IsCoprime r d then theta ℓ d*primaryCoprimeAngularLattice r ℓ W (Y/norm d)
      else 0 := by
  have he (u : Eisenstein) :
      (if primary u ∧ d ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
      if primary u ∧ d ∣ u then
        (if IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [tsum_primary_dvd_eq_multiples hd]
  by_cases hc : IsCoprime r d
  · rw [ite_eq_left hc,primaryCoprimeAngularLattice,←tsum_mul_left]
    apply tsum_congr
    intro u
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have hs : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    simp only [IsCoprime.mul_right_iff,hc,true_and]
    by_cases hu : primary u <;> by_cases hru : IsCoprime r u <;>
      simp [hu,hru,theta_mul,norm_mul_eq,hs,mul_assoc]
  · rw [ite_eq_right hc]
    simp only [IsCoprime.mul_right_iff,hc,false_and,ite_false]
    simp

private lemma squarefreeAngular_pointwise_inversion (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) (u : Eisenstein) :
    (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) := by
  by_cases hu : primary u
  · by_cases hc : IsCoprime r u
    · by_cases hw : W (norm u/Y) = 0
      · simp [hw]
      · have hn : norm u ≤ S*Y := by
          have hh : norm u/Y ≤ S := le_of_not_gt (fun hh => hw (hcut _ hh))
          exact (div_le_iff₀ hY).mp hh
        have hi : (∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
            if c^2 ∣ u then (idealMoebius c:ℂ) else 0) = (idealMoebius u:ℂ)^2 := by
          exact_mod_cast primary_square_moebius_truncation hu hn
        rw [ite_eq_left ⟨hu,hc⟩,←hi,Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c hc'
        by_cases hd : c^2 ∣ u <;> simp [hu,hc,hd,mul_assoc]
    · simp [hu,hc]
  · simp [hu]

private lemma squarefreeAngular_summable (r c : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y : ℝ} (hY : 0 < Y) :
    Summable (fun u : Eisenstein => (idealMoebius c:ℂ)*
      (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)) := by
  have hs := summable_primary_angular_restricted ℓ W hW hsm hY
    (fun u => c^2 ∣ u ∧ IsCoprime r u)
  apply (hs.mul_left (idealMoebius c:ℂ)).congr
  intro u
  by_cases hu : primary u ∧ c^2 ∣ u ∧ IsCoprime r u
  · simp only [hu]
  · simp only [hu,ite_false]

theorem squarefreeCoprimeAngularLattice_expansion
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W)
    {Y S : ℝ} (hY : 0 < Y)
    (hcut : ∀ x : ℝ, S < x → W x = 0) :
    squarefreeCoprimeAngularLattice r ℓ W Y =
      ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (S*Y)),
        (idealMoebius c:ℂ)*
          (if IsCoprime r (c^2) then theta ℓ (c^2)*
            primaryCoprimeAngularLattice r ℓ W (Y/norm (c^2)) else 0) := by
  let C := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  let T (c u : Eisenstein) : ℂ := (idealMoebius c:ℂ)*
    (if primary u ∧ c^2 ∣ u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0)
  have hsum (c : Eisenstein) : Summable (T c) := squarefreeAngular_summable r c ℓ W hW hsm hY
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0) =
        ∑ c ∈ C,T c u := squarefreeAngular_pointwise_inversion r ℓ W hY hcut u
  unfold squarefreeCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun c _ => hsum c)]
  apply Finset.sum_congr rfl
  intro c hc
  have hprim : primary (c^2) := by
    simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
      (mem_squarefreeDivisorTruncation.mp hc).1
  change (∑' u : Eisenstein,(idealMoebius c:ℂ)*_) = _
  rw [tsum_mul_left,coprimeAngularLattice_divisor r ℓ W Y hprim]

/-- Cancellation in every fixed nonzero mode, for the literal squarefree
primary sum with coprimality to the level. -/
theorem squarefreeCoprimeAngularLattice_bound {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y : ℝ, 1 ≤ Y →
        ‖squarefreeCoprimeAngularLattice r ℓ W Y‖ ≤ K*norm r^ε*Real.sqrt Y := by
  obtain ⟨C,hC,hbound⟩ := primaryCoprimeAngularLattice_bound hℓ W hW hpos hsm hε
  obtain ⟨S₀,hS₀⟩ := hW.isCompact.isBounded.exists_norm_le
  let S := max S₀ 1
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hcut : ∀ x : ℝ, S < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hb := hS₀ x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hb
    have hh : S₀ ≤ S := le_max_left _ _
    linarith [le_abs_self x]
  refine ⟨18*Real.sqrt S*C,by positivity,?_⟩
  intro r hr hsr Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hNr : 0 ≤ norm r^ε := Real.rpow_nonneg (norm_nonneg r) _
  let B := squarefreeDivisorTruncation (Real.sqrt (S*Y))
  have hcard : (B.card:ℝ) ≤ 18*Real.sqrt (S*Y) := by
    have hsub : B ⊆ nonzeroNormBall (Real.sqrt (S*Y)) := by
      intro c hc
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (nonzeroNormBall_card_le (Real.sqrt_nonneg _))
  rw [squarefreeCoprimeAngularLattice_expansion r ℓ W hW hsm hY0 hcut]
  calc
    _ ≤ ∑ c ∈ B,C*norm r^ε := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      have hprim : primary (c^2) := by
        simpa only [pow_two] using primary_mul (mem_squarefreeDivisorTruncation.mp hc).1
          (mem_squarefreeDivisorTruncation.mp hc).1
      by_cases hcop : IsCoprime r (c^2)
      · rw [ite_eq_left hcop,norm_mul,norm_mul,
          norm_theta (primary_ne_zero hprim),one_mul]
        apply (mul_le_of_le_one_left (_root_.norm_nonneg _)
          (norm_idealMoebius_le_one c)).trans
        exact hbound r hr hsr _ (div_pos hY0 (norm_pos_of_ne_zero (primary_ne_zero hprim)))
      · simp only [ite_eq_right hcop,mul_zero,norm_zero]
        exact mul_nonneg hC.le hNr
    _ = (B.card:ℝ)*(C*norm r^ε) := by simp
    _ ≤ (18*Real.sqrt (S*Y))*(C*norm r^ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le hNr)
    _ = _ := by rw [Real.sqrt_mul hS.le]; ring

end CubicFirstMoment

end

end OAI
