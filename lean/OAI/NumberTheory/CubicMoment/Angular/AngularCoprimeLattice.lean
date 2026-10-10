import OAI.NumberTheory.CubicMoment.Angular.AngularPrimaryLattice
import OAI.NumberTheory.CubicGram.LatticeCounts
import OAI.NumberTheory.CubicGram.CubicOperator

namespace OAI

/-! Exact coprimality removal for the angular lattice model. The
primary congruence class and all divisor phases remain literal. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryCoprimeAngularLattice (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0

lemma primaryAngularLattice_eq_indicator (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) :
    primaryAngularLattice ℓ W Y =
      ∑' u : Eisenstein, if primary u then theta ℓ u*W (norm u/Y) else 0 := by
  symm
  change (∑' u : Eisenstein, Set.indicator {u | primary u}
    (fun u => theta ℓ u*W (norm u/Y)) u) = _
  rw [←tsum_subtype]
  rfl

lemma summable_primary_angular_restricted (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y)
    (P : Eisenstein → Prop) :
    Summable (fun u : Eisenstein => if primary u ∧ P u then theta ℓ u*W (norm u/Y) else 0) := by
  apply (schwartz_summable_eisenstein (normProfileSchwartz W hW hsm Y hY)).norm.of_norm_bounded
  intro u
  change ‖ite _ _ _‖ ≤ ‖W (norm u/Y)‖
  split_ifs with hu
  · rw [norm_mul,norm_theta (primary_ne_zero hu.1),one_mul]
  · simp

lemma primaryAngularLattice_divisor (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ)
    {d : Eisenstein} (hd : primary d) :
    (∑' u : Eisenstein, if primary u ∧ d ∣ u then theta ℓ u*W (norm u/Y) else 0) =
      theta ℓ d*primaryAngularLattice ℓ W (Y/norm d) := by
  rw [tsum_primary_dvd_eq_multiples hd,primaryAngularLattice_eq_indicator,←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · simp only [hu,ite_true,theta_mul,norm_mul_eq]
    have hn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
    have he : norm d*norm u/Y = norm u/(Y/norm d) := by field_simp
    rw [he]
    ring
  · simp only [hu,ite_false,mul_zero]

lemma primaryCoprimeAngularLattice_expansion {r : Eisenstein}
    (hr : primary r) (hsr : Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hsm : ContDiff ℝ ∞ W) {Y : ℝ} (hY : 0 < Y) :
    primaryCoprimeAngularLattice r ℓ W Y =
      ∑ s ∈ (primaryPrimeFactors r).powerset,
        (idealMoebius (∏ p ∈ s, p):ℂ)*theta ℓ (∏ p ∈ s, p)*
          primaryAngularLattice ℓ W (Y/norm (∏ p ∈ s, p)) := by
  let P := (primaryPrimeFactors r).powerset
  let f : Finset Eisenstein → Eisenstein → ℂ := fun s u =>
    (idealMoebius (∏ p ∈ s, p):ℂ)*
      (if primary u ∧ (∏ p ∈ s, p) ∣ u then theta ℓ u*W (norm u/Y) else 0)
  have hf (s : Finset Eisenstein) (_hs : s ∈ P) : Summable (f s) :=
    (summable_primary_angular_restricted ℓ W hW hsm hY _).mul_left _
  have he (u : Eisenstein) :
      (if primary u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0) =
        ∑ s ∈ P, f s u := by
    by_cases hu : primary u
    · have hi := congrArg (fun z : ℂ => z*(theta ℓ u*W (norm u/Y)))
        (primary_moebius_coprimality hr hsr u)
      rw [Finset.sum_mul] at hi
      calc
        _ = (if IsCoprime r u then (1:ℂ) else 0)*(theta ℓ u*W (norm u/Y)) := by
          by_cases hc : IsCoprime r u <;> simp [hu,hc]
        _ = _ := hi
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hd : (∏ p ∈ s, p) ∣ u <;> simp [f,hu,hd]
    · simp [f,hu]
  unfold primaryCoprimeAngularLattice
  simp_rw [he]
  rw [Summable.tsum_finsetSum hf]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
    (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
  change (∑' u : Eisenstein, (idealMoebius (∏ p ∈ s, p):ℂ)*_) = _
  rw [tsum_mul_left,primaryAngularLattice_divisor ℓ W Y hd]
  ring

/-- The actual coprime angular sum is bounded by a fixed small power
of the level, uniformly over its length. -/
theorem primaryCoprimeAngularLattice_bound {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y : ℝ, 0 < Y → ‖primaryCoprimeAngularLattice r ℓ W Y‖ ≤ K*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := primaryAngularLattice_bounded hℓ W hW hpos hsm
  obtain ⟨D,hD,hdiv⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro r hr hsr Y hY
  rw [primaryCoprimeAngularLattice_expansion hr hsr ℓ W hW hsm hY]
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors r).powerset, C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      have hd : primary (∏ p ∈ s, p) := primary_finset_prod _ _
        (fun p hp => (primaryPrimeFactor_spec hr (Finset.mem_powerset.mp hs hp)).1.1)
      rw [norm_mul,norm_mul,norm_theta (primary_ne_zero hd),mul_one]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
      exact hbound _ (div_pos hY (norm_pos_of_ne_zero (primary_ne_zero hd)))
    _ = C*(2:ℝ)^(primaryPrimeFactors r).card := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    _ ≤ C*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr hsr) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
