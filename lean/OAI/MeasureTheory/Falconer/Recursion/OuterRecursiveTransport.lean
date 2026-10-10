import OAI.MeasureTheory.Falconer.Recursion.TwoProfileRecursion
import OAI.MeasureTheory.Falconer.Estimates.RootSupremum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem outerDescriptorList_remaining (m : ℝ → ℝ) (N q c : ℕ) :
    (outerDescriptorList m N q c).filter (fun b => c < descriptorAnchor b) =
      remainingPolicyDescriptors (fun n => m n-(n:ℝ)/N) N q c N c := by
  classical
  ext b
  simp only [outerDescriptorList,remainingPolicyDescriptors,Finset.mem_filter,Finset.mem_insert]
  constructor
  · rintro ⟨hb | hb,hc⟩
    · subst b
      exact (Nat.lt_irrefl c hc).elim
    · exact ⟨hb,hc⟩
  · rintro ⟨hb,hc⟩
    exact ⟨Or.inr hb,hc⟩

theorem outer_remaining_budget (m : ℝ → ℝ) (N q c K : ℕ) (k : PolicyDescriptor → ℕ)
    (hk : ∑ b ∈ outerDescriptorList m N q c, k b ≤ K) :
    ∑ b ∈ remainingPolicyDescriptors (fun n => m n-(n:ℝ)/N) N q c N c, k b ≤ K := by
  rw [← outerDescriptorList_remaining]
  exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hk

theorem outer_remaining_energy (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane)
    (mass : Fin 2 → ℝ → ℝ) (N q c J : ℕ) (lam sig : ℝ)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ)
    (row : CellPath × CellPath) (hX : row.1.length = c) (hY : row.2.length = c) :
    remainingAngularEnergy (fun l => outerDescriptorList (mass l) N q c) (fun _ => id) k
      Q ρ mass N lam sig J 0 h (((2:ℝ)^N)^(-mass 0 c)) (((2:ℝ)^N)^(-mass 1 c)) c N Ψ row =
    sourceAngularH c N Ψ
      ((⟨Q 0,ρ 0,mass 0,N,q,J,lam,sig⟩ : RecursiveEnvironment).endpointTransform c row.1 (k 0) (h 0))
      ((⟨Q 1,ρ 1,mass 1,N,q,J,lam,sig⟩ : RecursiveEnvironment).endpointTransform c row.2 (k 1) (h 1)) := by
  simp only [remainingAngularEnergy,hX,hY,id_eq,outerDescriptorList_remaining]
  rfl

theorem RootShellData.inverseShellSupremum_le (d : RootShellData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ M) : d.inverseShellSupremum n v Ψ ≤ M := by
  apply csSup_le (show (d.inverseShellEnergies n v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro E hE
  rcases hE with rfl | ⟨j,hj,b,hb,ξ,rfl⟩
  · exact hM
  · exact h j hj b hb ξ

end PlanarFalconer

end OAI
