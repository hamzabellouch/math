import OAI.NumberTheory.CubicMoment.Decomposition.NoStopCentral

namespace OAI

/-! Exact Type-I collection for a no-stop branch with an additional
predicate on the distinguished and selected factors. In particular the
failed first-stage prefix is preserved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopCoefficient (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ X Z : ℝ) (P : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein) : ℂ :=
  stoppedBeta R D v ψ w (fun r m =>
    norm r*primeSurrogate (primaryPrimeFactors m)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P r m) b

lemma restrictedNoStop_coefficient_collection (S R : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r*∑ u ∈ primaryElementBall X,
      ∑ m ∈ primaryProductSlice S X (r*u) with
        norm r*primeSurrogate (primaryPrimeFactors m)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P r m,
        cutoffMoebius ψ w m*K (r*(m*u))) =
    ∑ b ∈ primaryPairSupport R (primaryElementBall X),
      restrictedNoStopCoefficient R (primaryElementBall X) v ψ w ρ X Z P b *
        ∑ u ∈ primaryElementBall X, if b*u ∈ S then K (b*u) else 0 := by
  unfold restrictedNoStopCoefficient stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _
  simp only [primaryProductSlice,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro m _
  have he : (r*u)*m = (r*m)*u := by ring
  simp only [he]
  split_ifs <;> ring_nf

lemma restrictedNoStop_coefficient_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) {b : Eisenstein} (hb : primary b) :
    ‖restrictedNoStopCoefficient R D v ψ w ρ X Z P b‖ ≤
      M*((metaplecticPrimaryDivisors b).card:ℝ) := by
  have hsub : R.filter (fun r => r ∣ b) ⊆ metaplecticPrimaryDivisors b := by
    intro r hr
    obtain ⟨hrR,hrb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨hR r hrR,norm_le_of_dvd (primary_ne_zero hb) hrb⟩,hrb⟩
  apply (stoppedBeta_divisor_bound R D hR hψ w _ v hM hv b).trans
  calc
    _ ≤ ((metaplecticPrimaryDivisors b).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) hM
    _ = _ := mul_comm _ _

lemma restrictedNoStop_coefficient_nonzero (R D : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w ρ X Z : ℝ)
    (P : Eisenstein → Eisenstein → Prop) {b : Eisenstein}
    (hb : restrictedNoStopCoefficient R D v ψ w ρ X Z P b ≠ 0) :
    ∃ r ∈ R, ∃ m ∈ D, r*m = b ∧ Squarefree m ∧
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z := by
  unfold restrictedNoStopCoefficient stoppedBeta primaryPairCoefficient at hb
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hm⟩ := Finset.mem_product.mp hp
  have hsel : norm p.1*primeSurrogate (primaryPrimeFactors p.2)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P p.1 p.2 := by
    by_contra h
    exact hterm (ite_eq_right h)
  rw [ite_eq_left hsel] at hterm
  exact ⟨p.1,hr,p.2,hm,hprod,
    cutoffMoebius_ne_zero_squarefree (mul_ne_zero_iff.mp hterm).2,hsel.1⟩

end CubicFirstMoment

end

end OAI
