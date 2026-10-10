import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedDyads
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingLabelWeights

namespace OAI

/-! The exact finite stopping sums cost only a fixed power of log X. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_double_sum_le_card_sq {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → κ → ℂ) {M : ℝ} (hf : ∀ i ∈ S, ∀ j ∈ T, ‖f i j‖ ≤ M) :
    ‖∑ i ∈ S, ∑ j ∈ T, f i j‖ ≤ (S.card:ℝ)*(T.card:ℝ)*M := by
  calc
    _ ≤ ∑ i ∈ S, ‖∑ j ∈ T, f i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, (T.card:ℝ)*M := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        Finset.sum_le_sum (s := T) (fun j hj => hf i hi j hj)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem distinguishedScaleStoppedRow_bound {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (M : ℝ), 0 ≤ M →
      (∀ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        ∀ j k : ℕ, ‖distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖distinguishedScaleStoppedRow i ρ ξ Ct H X h early d‖ ≤
        K*(1+Real.log X)^5*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  refine ⟨C*D^2,by positivity,?_⟩
  intro i Ct ξ H X hX h early d M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
    (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := by
    dsimp [I]
    split
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hJ0 : 0 ≤ (J.card:ℝ) := Nat.cast_nonneg _
  have hinner (q) (hq : q ∈ I) :
      ‖∑ j ∈ J, ∑ k ∈ J, distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
    apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece q hq j k)).trans
    have hs := mul_le_mul hJ hJ hJ0 (by positivity : 0 ≤ D*(1+Real.log X))
    calc
      _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
      _ = _ := by ring
  rw [distinguishedScaleStoppedRow_dyads]
  have hh := (hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
    (by positivity) hinner
  apply hh.trans_eq
  ring

theorem distinguishedScaleStopped_bound (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ct : ℕ) (ξ H X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)) →
        ∀ j k : ℕ, ‖distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k‖ ≤ M) →
      ‖distinguishedScaleStopped i ρ ξ Ct H X h early‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨C,hC,hrow⟩ := distinguishedScaleStoppedRow_bound hρ
  obtain ⟨D,hD,hcount⟩ := stopped_norm_partition_subset_count i
  refine ⟨D*C,by positivity,?_⟩
  intro Ct ξ H X hX h early M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let S := (Finset.univ : Finset (Fin i → Fin
    (normPartitionCount (Real.exp primeProductWeights.radius*X))))
  have hb (d) : ‖(if distinguishedScaleLength d < X^(69/200:ℝ) then
      distinguishedScaleStoppedRow i ρ ξ Ct H X h early d else 0)‖ ≤
      C*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow i Ct ξ H X hX h early d M hM (hpiece d)
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, C*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*(C*(1+Real.log X)^5*M) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (D*(1+Real.log X)^i)*(C*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hcount X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CubicFirstMoment

end

end OAI
