import OAI.Geometry.NodalSets.SmoothLimit.IterationGeometricTails
import OAI.Geometry.NodalSets.SmoothLimit.SphereCoefficientSummablePositiveLimit
import OAI.Geometry.NodalSets.SmoothLimit.SphereIterationSummability
import OAI.Geometry.NodalSets.SmoothLimit.SphereSummableIterationSequence

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_iteration_positive_limit :
    ∃ (r delta : ℝ) (s : (k : ℕ) → SphereNodalStage r delta k),
      (∀ k, k+1 ≤ (s k).frequency) ∧
      ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        ∀ k, sphereCoefficientDistance (s k).charts 8
          (s k).energy.tensor (s k).energy.density b.tensor b.density < (s k).radius := by
  obtain ⟨P,hP⟩ := finite_sphere_coefficient_atlas
  obtain ⟨eta,heta,Hlimit⟩ := sphere_coefficient_summable_positive_limit P hP
    roundSphereEnergyData roundSphereEnergyData_density_smooth
  obtain ⟨r,delta,hr,hdelta,s,hfirst,hfreq,hgap,hsupp,hdiag,hzero,hpast⟩ :=
    sphere_summable_iteration_sequence P eta heta
  let d : ℕ → SphereEnergyData := fun n ↦ Nat.casesOn n roundSphereEnergyData (fun k ↦ (s k).energy)
  have hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density := by
    rintro (_|n)
    · exact roundSphereEnergyData_density_smooth
    · exact (s n).density_smooth
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  let D (Q : Finset Base) (J n : ℕ) : ℝ := sphereCoefficientDistance Q J
    (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density
  have hnonneg (Q : Finset Base) (J n : ℕ) : 0 ≤ D Q J n :=
    sphereCoefficientDistance_nonneg Q J (d n).tensor (d (n+1)).tensor
      (d n).density (d (n+1)).density (fun p _ ↦ hds n p) (fun p _ ↦ hds (n+1) p)
  have hsum (J : ℕ) : Summable (D P J) := by
    apply (summable_nat_add_iff 1).mp
    exact sphere_coefficient_diagonal_summable P (fun k ↦ (s k).energy)
      (fun k ↦ (s k).density_smooth) hdiag J
  have hzero_le (n : ℕ) : D P 0 (n+1) ≤ eta*(1/2:ℝ)^(n+3) := (hzero n).le
  have htotal : (∑' n, D P 0 n) < eta := by
    have ht : (∑' n, D P 0 (n+1)) ≤ eta/4 := by
      rw [← tsum_scaled_geometric_three eta]
      exact ((summable_nat_add_iff 1).mpr (hsum 0)).tsum_le_tsum hzero_le
        (hasSum_scaled_geometric_shift eta 3).summable
    rw [(hsum 0).tsum_eq_zero_add]
    have hf : D P 0 0 < eta/4 := hfirst
    linarith
  obtain ⟨b,hb,Htail⟩ := Hlimit d hd rfl hsum htotal
  refine ⟨r,delta,s,hfreq,b,hb,?_⟩
  intro i
  have hpast_le (j : ℕ) : D (s i).charts 8 (j+(i+1)) ≤ (s i).radius*(1/2:ℝ)^(j+2) := by
    have h := hpast (i+j) i (Nat.le_add_right i j)
    simpa only [D,d,show j+(i+1) = (i+j)+1 by omega,Nat.casesOn,
      Nat.add_sub_cancel_left] using h.le
  have hsumtail : Summable (fun j ↦ D (s i).charts 8 (j+(i+1))) :=
    Summable.of_nonneg_of_le (fun j ↦ hnonneg _ _ _) hpast_le
      (hasSum_scaled_geometric_shift (s i).radius 2).summable
  have hsumall : Summable (D (s i).charts 8) := (summable_nat_add_iff (i+1)).mp hsumtail
  have ht := (Htail (s i).charts 8 hsumall).2 (i+1)
  have htsum : (∑' j, D (s i).charts 8 ((i+1)+j)) ≤ (s i).radius/2 := by
    rw [← tsum_scaled_geometric_two (s i).radius]
    have hs' : Summable (fun j ↦ D (s i).charts 8 ((i+1)+j)) := by
      simpa only [Nat.add_comm] using hsumtail
    exact hs'.tsum_le_tsum
      (fun j ↦ by simpa only [Nat.add_comm] using hpast_le j)
      (hasSum_scaled_geometric_shift (s i).radius 2).summable
  exact ht.trans_lt (htsum.trans_lt (half_lt_self (s i).radius_pos))

end
end Yau.Target

end OAI
