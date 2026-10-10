import Mathlib

namespace OAI

section
section

section
noncomputable section
namespace ResolventTaylor
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
open scoped BigOperators

def second (L : E →ₗ[ℝ] E) (t : ℝ) (a : E) : E :=
  a-(3*t) • L a+(6*t^2) • ((L^2) a)

lemma cube_second (L : E →ₗ[ℝ] E) (t : ℝ) (a : E) :
    (((LinearMap.id : E →ₗ[ℝ] E)+t • L)^3) (second L t a) =
      a+(10*t^3) • ((L^3) a)+(15*t^4) • ((L^4) a)+(6*t^5) • ((L^5) a) := by
  simp only [second,pow_succ,Module.End.mul_apply,LinearMap.add_apply,
    LinearMap.id_apply,LinearMap.smul_apply,map_add,map_sub,map_smul,pow_zero,
    Module.End.one_apply]
  module
end ResolventTaylor

end
end

section
noncomputable section
namespace ResolventTaylor
open Filter Set
open scoped Topology RealInnerProductSpace
variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma scaled_inner_tendsto (U : ℝ → H) (K : ℝ)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖U r‖ ≤ K*(r⁻¹)^3)
    (b : H) (n : ℕ) :
    Tendsto (fun r : ℝ => r^(n+4)*⟪U r,b⟫) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => K*‖b‖*r^(n+1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow (n+1)).const_mul (K*‖b‖)
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hr1
  have hp : 0 < r := hr
  calc
    ‖r^(n+4)*⟪U r,b⟫‖ = r^(n+4)*|⟪U r,b⟫| := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (pow_pos hp _)]
    _ ≤ r^(n+4)*(‖U r‖*‖b‖) := mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm _ _) (pow_nonneg hp.le _)
    _ ≤ r^(n+4)*((K*(r⁻¹)^3)*‖b‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hb r hp hr1.le) (norm_nonneg _)) (pow_nonneg hp.le _)
    _ = K*‖b‖*r^(n+1) := by
      simp only [pow_add]
      field_simp

lemma cube_distribution_tendsto (L : E →ₗ[ℝ] E) (i : E →ₗ[ℝ] H)
    (F : E →ₗ[ℝ] ℝ) (U : ℝ → H) (K : ℝ)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖U r‖ ≤ K*(r⁻¹)^3)
    (he : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ a : E,
      ⟪U r,i ((((LinearMap.id : E →ₗ[ℝ] E)+r^2 • L)^3) a)⟫ = F a)
    (a : E) : Tendsto (fun r : ℝ => ⟪U r,i a⟫) (𝓝[>] 0) (𝓝 (F a)) := by
  have h3 := (scaled_inner_tendsto U K hb (i ((L^3) a)) 2).const_mul 10
  have h4 := (scaled_inner_tendsto U K hb (i ((L^4) a)) 4).const_mul 15
  have h5 := (scaled_inner_tendsto U K hb (i ((L^5) a)) 6).const_mul 6
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := (ht.pow 2).const_mul (3*F (L a))
  have h2 := (ht.pow 4).const_mul (6*F ((L^2) a))
  have hlim := ((((tendsto_const_nhds (x:=F a)).sub h1).add h2).sub h3).sub h4 |>.sub h5
  simp only [zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    mul_zero,sub_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hr1
  have hx := he r hr hr1.le (second L (r^2) a)
  rw [cube_second] at hx
  simp only [second,map_add,map_sub,map_smul,inner_add_right,real_inner_smul_right] at hx
  norm_num only [← pow_mul,smul_eq_mul] at hx
  norm_num only
  nlinarith [hx]
end ResolventTaylor

end
end

end
end

end OAI
