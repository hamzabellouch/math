import Mathlib
import OAI.Analysis.Commutator.KaplanskyFull

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (hnT : ‖T‖≤1)

include hS hT hnT

lemma net_approx_exists (j : Finset H × ℕ) : ∃ a : H →L[ℂ] H,
    a∈S ∧ ‖a‖≤1 ∧ ∀ x∈j.1,‖a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,ha,hna,he⟩ := contraction_finite_approx j.1 S hS hT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,ha,hna,fun x hx => he ⟨x,hx⟩⟩

def approximationNet (j : Finset H × ℕ) : H →L[ℂ] H :=
  (net_approx_exists S hS T hT hnT j).choose

lemma approximationNet_spec (j : Finset H × ℕ) :
    approximationNet S hS T hT hnT j∈S ∧ ‖approximationNet S hS T hT hnT j‖≤1 ∧
      ∀ x∈j.1,‖approximationNet S hS T hT hnT j x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (net_approx_exists S hS T hT hnT j).choose_spec

lemma approximationNet_tendsto (x : H) :
    Tendsto (fun j => approximationNet S hS T hT hnT j x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  have hxj : x∈j.1 := hj.1 (Finset.mem_singleton_self x)
  apply (approximationNet_spec S hS T hT hnT j).2.2 x hxj |>.trans_le
  have hnj : (N+1:ℝ)≤j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hnj).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
