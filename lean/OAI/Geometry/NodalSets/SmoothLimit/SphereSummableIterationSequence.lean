import OAI.Geometry.NodalSets.Coefficients.SphereFiniteCoefficientConstraints
import OAI.Geometry.NodalSets.Persistence.FiniteHistorySelection
import OAI.Geometry.NodalSets.SmoothLimit.SphereIterationInterface

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal
noncomputable section

theorem sphere_summable_iteration_sequence (P₀ : Finset Base) (budget : ℝ) (hbudget : 0 < budget) :
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧
      ∃ s : (k : ℕ) → SphereNodalStage r delta k,
        sphereCoefficientDistance P₀ 0 roundSphereEnergyData.tensor roundSphereEnergyData.density
          (s 0).energy.tensor (s 0).energy.density < budget/4 ∧
        (∀ k, k+1 ≤ (s k).frequency) ∧
        (∀ k, 2*(s k).frequency+1 ≤ (s (k+1)).frequency) ∧
        (∀ k, (s k).support ⊆ (s (k+1)).support) ∧
        (∀ k, sphereCoefficientDistance P₀ (k+1) (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < (1/2:ℝ)^(k+1)) ∧
        (∀ k, sphereCoefficientDistance P₀ 0 (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < budget*(1/2:ℝ)^(k+3)) ∧
        (∀ k i, i ≤ k → sphereCoefficientDistance (s i).charts 8 (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < (s i).radius*(1/2:ℝ)^(k-i+2)) := by
  classical
  obtain ⟨r,delta,hr,hdelta,⟨d₀,hd₀,hsupp₀⟩,H⟩ := sphere_iteration_interface
  obtain ⟨s₀,hs₀,hsupp,hfirst⟩ := H d₀ 0 P₀ 0 (budget/4) (by positivity) 1
  let R : (k : ℕ) → ((i : Fin (k+1)) → SphereNodalStage r delta i.val) →
      SphereNodalStage r delta (k+1) → Prop := fun k v w ↦
    let d := v (Fin.last k)
    2*d.frequency+1 ≤ w.frequency ∧ d.support ⊆ w.support ∧
    sphereCoefficientDistance P₀ (k+1) d.energy.tensor d.energy.density w.energy.tensor w.energy.density < (1/2:ℝ)^(k+1) ∧
    sphereCoefficientDistance P₀ 0 d.energy.tensor d.energy.density w.energy.tensor w.energy.density < budget*(1/2:ℝ)^(k+3) ∧
    ∀ i : Fin (k+1), sphereCoefficientDistance (v i).charts 8 d.energy.tensor d.energy.density w.energy.tensor w.energy.density <
      (v i).radius*(1/2:ℝ)^(k-i.val+2)
  have Hnext : ∀ k v, ∃ w, R k v w := by
    intro k v
    let d := v (Fin.last k)
    obtain ⟨Q,m,eta,heta,Hsmall⟩ := sphere_finite_coefficient_constraints
      (Finset.univ : Finset (Fin (k+1))) (fun i ↦ (v i).charts) (fun _ ↦ 8)
      (fun i ↦ (v i).radius*(1/2:ℝ)^(k-i.val+2))
      (fun i _ ↦ mul_pos (v i).radius_pos (by positivity))
    let eps : ℝ := min eta (min ((1/2:ℝ)^(k+1)) (budget*(1/2:ℝ)^(k+3)))
    have heps : 0 < eps := by dsimp [eps]; positivity
    obtain ⟨w,hfreq,hsupport,hdist⟩ := H d.toSphereComparisonPair (k+1) (P₀ ∪ Q) (max (k+1) m)
      eps heps (2*d.frequency+1)
    have hdistP := (sphereCoefficientDistance_mono_atlas P₀ (P₀ ∪ Q) Finset.subset_union_left
      d.energy w.energy d.density_smooth w.density_smooth (max (k+1) m)).trans_lt hdist
    have hdistOrder := (sphereCoefficientDistance_mono_order P₀ d.energy w.energy d.density_smooth w.density_smooth
      (k+1) (max (k+1) m) (le_max_left _ _)).trans_lt hdistP
    refine ⟨w,hfreq,hsupport,?_,?_,?_⟩
    · exact hdistOrder.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    · exact ((sphereCoefficientDistance_mono_order P₀ d.energy w.energy d.density_smooth w.density_smooth
        0 (k+1) (Nat.zero_le _)).trans_lt hdistOrder).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    · intro i
      apply Hsmall d.energy w.energy d.density_smooth w.density_smooth ?_ i (Finset.mem_univ i)
      exact (sphereCoefficientDistance_mono_order Q d.energy w.energy d.density_smooth w.density_smooth
        m (max (k+1) m) (le_max_right _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas Q (P₀ ∪ Q) Finset.subset_union_right
          d.energy w.energy d.density_smooth w.density_smooth _).trans_lt (hdist.trans_le (min_le_left _ _)))
  obtain ⟨s,hs0,hs⟩ := Yau.exists_sequence_of_finite_history s₀ R Hnext
  have hprops (k : ℕ) := hs k
  change ∀ k, R k (fun i ↦ s i.val) (s (k+1)) at hs
  have hfreq (k : ℕ) : 2*(s k).frequency+1 ≤ (s (k+1)).frequency := (hs k).1
  refine ⟨r,delta,hr,hdelta,s,?_,?_,hfreq,fun k ↦ (hs k).2.1,
    fun k ↦ (hs k).2.2.1,fun k ↦ (hs k).2.2.2.1,?_⟩
  · rw [hs0,← hd₀]
    exact hfirst
  · intro k
    induction k with
    | zero => simpa only [hs0] using hs₀
    | succ k ih => have h := hfreq k; omega
  · intro k i hi
    exact (hs k).2.2.2.2 ⟨i,Nat.lt_succ_of_le hi⟩

end
end Yau.Target

end OAI
