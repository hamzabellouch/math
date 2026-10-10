import OAI.NumberTheory.CubicMoment.Estimates.SparseLateSupport
import OAI.NumberTheory.CubicMoment.Estimates.LateStopDivisor
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedUniform

namespace OAI

/-! The sparse support belongs to the actual late stopped coefficient.
Nonvanishing selects a literal product fibre, and the failed first stage
constructs its large small-prime divisor. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppedBeta_late_mem_sparse
    (R D : Finset Eisenstein) (f : Eisenstein → ℂ) (w : ℝ)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ)
    {X C η Z Q B : ℝ} (hQ : 0 < Q) (hgap : X^η ≤ Z/Q)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (hell : ∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
      0 < ell (bin p) ∧ ell (bin p) ≤ norm p)
    (hsmall : ∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
      h ≤ bin p → norm p ≤ (Real.log X)^C)
    {b : Eisenstein} (hb : primary b) (hsb : Squarefree b) (hbB : norm b ≤ B)
    (hβ : stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest bin ell j k h Z Q false) b ≠ 0) :
    b ∈ sparseLateSupport X C η B := by
  unfold stoppedBeta primaryPairCoefficient at hβ
  obtain ⟨t,ht,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  obtain ⟨hpair,heq⟩ := Finset.mem_filter.mp ht
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp hpair
  have htest : stoppedSideTest bin ell j k h Z Q false t.1 t.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  have hsd : Squarefree t.2 := by
    intro c hc
    apply hsb c
    exact hc.trans (heq ▸ dvd_mul_left t.2 t.1)
  obtain ⟨hc,hsc,hdiv,hlarge,hsmooth⟩ := stopped_late_smooth_divisor bin ell j k h Z Q
    ((Real.log X)^C) (hR _ hr) (hD _ hd) hsd hQ htest (hell _ hd) (hsmall _ hd)
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨hb,hbB⟩,
    lateStopDivisor bin h t.2,hc,hsc,?_,hgap.trans hlarge.le,hsmooth⟩
  exact heq ▸ hdiv

theorem sparse_stopped_beta_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C η ξ : ℝ} (hC : 0 < C) (hη : 0 < η)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B Z Q : ℝ), 0 ≤ B → B ≤ X → 0 < Q → X^η ≤ Z/Q →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D U : Finset Eisenstein) (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d) →
      (∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
        0 < ell (bin p) ∧ ell (bin p) ≤ norm p) →
      (∀ d ∈ D, ∀ p ∈ primaryPrimeFactors d,
        h ≤ bin p → norm p ≤ (Real.log X)^C) →
      (∀ b ∈ U, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ) (stoppedSideTest bin ell j k h Z Q false) b‖^2) ≤
          K*B*X^(-δ) := by
  obtain ⟨δ,hδ,hcount⟩ := sparseLateSupport_card_saving hpnt hC hη
  obtain ⟨M,hM,hbound⟩ := stoppedBeta_distinguished_uniform (ι := ι) (C := 1) hξ hξz
    (by norm_num) (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨δ,18*M^2,hδ,by positivity,?_⟩
  filter_upwards [hcount,hbound] with X hcount hbound
  intro B Z Q hB hBX hQ hgap S W R D U bin ell j k h hS hW hR hD hell hsmall hU
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ) (stoppedSideTest bin ell j k h Z Q false)
  let T := U.filter (fun b => β b ≠ 0)
  have hsub : T ⊆ sparseLateSupport X C η B := by
    intro b hb
    obtain ⟨hb,hβ⟩ := Finset.mem_filter.mp hb
    exact stoppedBeta_late_mem_sparse R D _ _ bin ell j k h hQ hgap hR hD hell hsmall
      (hU b hb).1 (hU b hb).2.1 (hU b hb).2.2 hβ
  have hcard : (T.card:ℝ) ≤ 18*B*X^(-δ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount B hB)
  have heq : (∑ b ∈ U, ‖β b‖^2) = ∑ b ∈ T, ‖β b‖^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hz : β b = 0 <;> simp only [hz,ne_eq,not_true_eq_false,not_false_eq_true,
      ite_true,ite_false,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
  change (∑ b ∈ U, ‖β b‖^2) ≤ _
  rw [heq]
  calc
    _ ≤ ∑ _b ∈ T, M^2 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hb,_⟩ := Finset.mem_filter.mp hb
      apply pow_le_pow_left₀ (_root_.norm_nonneg _)
      exact hbound S W R D _ hS hW hR b (hU b hb).1 (hU b hb).2.1
        (by simpa only [one_mul] using (hU b hb).2.2.trans hBX)
    _ = (T.card:ℝ)*M^2 := by simp
    _ ≤ (18*B*X^(-δ))*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
