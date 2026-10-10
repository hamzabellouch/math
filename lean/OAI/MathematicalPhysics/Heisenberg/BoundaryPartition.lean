import OAI.MathematicalPhysics.Heisenberg.BoundaryWitness

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pin_weight_surface (π : Equiv.Perm V) (B : Set V) :
    (2:ℝ)^missingCount π B=(2:ℝ)^missingCount π ∅ *
      Real.exp (-(Real.log 2)*((hitClasses π B).card:ℝ)) := by
  have hpow : Real.exp (Real.log 2*((hitClasses π B).card:ℝ))=(2:ℝ)^(hitClasses π B).card := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [neg_mul,Real.exp_neg,hpow,←missing_add_hit π B,pow_add]
  field_simp

lemma partition_surface_identity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (B : Set V) :
    pinPartition μ π B/pinPartition μ π ∅=
      ∑ ω,pinDensity μ π ∅ ω*Real.exp (-(Real.log 2)*((hitClasses (π ω) B).card:ℝ)) := by
  unfold pinPartition
  simp_rw [pin_weight_surface (B:=B)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  unfold pinDensity pinPartition
  ring

theorem partition_surface_lower (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (B : Set V)
    (C : ℝ) (hC : (∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) B).card:ℝ))≤C) :
    Real.exp (-(Real.log 2)*C) ≤ pinPartition μ π B/pinPartition μ π ∅ := by
  have hj:=convexOn_exp.map_sum_le (t:=Finset.univ)
    (p:=fun ω=>-(Real.log 2)*((hitClasses (π ω) B).card:ℝ))
    (fun ω _=>pinDensity_nonneg μ π hμ hpos ∅ ω)
    (pinDensity_sum μ π hμ hpos ∅) (fun _ _=>Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have he : (∑ ω,pinDensity μ π ∅ ω*(-(Real.log 2)*((hitClasses (π ω) B).card:ℝ)))=
      -(Real.log 2)*(∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) B).card:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [he,←partition_surface_identity μ π B] at hj
  apply (Real.exp_le_exp.mpr ?_).trans hj
  exact mul_le_mul_of_nonpos_left hC (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))

end Heisenberg.Surface
end
end

end OAI
