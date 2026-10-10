import Mathlib
import OAI.Analysis.Commutator.KaplanskyRange

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ)))
  (hsT : IsSelfAdjoint T) (hnT : ‖T‖ ≤ 1)

include hT hsT hnT in
lemma starHom_net_approx_exists (j : Finset H × ℕ) : ∃ a : A,
    ‖a‖ ≤ 1 ∧ ∀ x∈j.1,‖φ a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,_,hna,he⟩ := range_selfAdjoint_contraction_finite_approx j.1 φ hT hsT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,hna,fun x hx => he ⟨x,hx⟩⟩

def starHomNet (j : Finset H × ℕ) : A :=
  (starHom_net_approx_exists φ T hT hsT hnT j).choose

lemma starHomNet_spec (j : Finset H × ℕ) :
    ‖starHomNet φ T hT hsT hnT j‖ ≤ 1 ∧
      ∀ x∈j.1,‖φ (starHomNet φ T hT hsT hnT j) x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (starHom_net_approx_exists φ T hT hsT hnT j).choose_spec

lemma starHomNet_tendsto (x : H) :
    Tendsto (fun j => φ (starHomNet φ T hT hsT hnT j) x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  have hxj : x∈j.1 := hj.1 (Finset.mem_singleton_self x)
  apply (starHomNet_spec φ T hT hsT hnT j).2 x hxj |>.trans_le
  have hnj : (N+1:ℝ) ≤ j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hnj).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
