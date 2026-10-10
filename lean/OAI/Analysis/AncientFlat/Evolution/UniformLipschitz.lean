import OAI.Analysis.AncientFlat.Profile.RadialRealSemigroup

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ContDiff ZeroAtInfty BoundedContinuousFunction NNReal
namespace FlatCompactness
variable {V : Type} [NormedAddCommGroup V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def eval0 (x : V) : C₀(V,ℂ) →L[ℂ] ℂ :=
  ({ toFun := fun f => f x, map_add' := by intros; rfl,
     map_smul' := by intros; rfl } : C₀(V,ℂ) →ₗ[ℂ] ℂ).mkContinuous 1
    (fun f => by
      change ‖f x‖ ≤ 1*‖f‖
      simpa only [one_mul,ZeroAtInftyContinuousMap.toBCF_apply,ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using f.toBCF.norm_coe_le_norm x)
lemma uniform_lipschitz (P : E →L[ℂ] C₀(V,ℂ))
    (h : ∀ d : E, ∃ C : ℝ≥0, LipschitzWith C (P d : V → ℂ)) :
    ∃ K : ℝ, 0≤K ∧ ∀ d : E, ∀ x y : V,
      ‖P d x-P d y‖≤K*‖d‖*‖x-y‖ := by
  let L : V × V → E →L[ℂ] ℂ := fun p =>
    (‖p.1-p.2‖ : ℂ)⁻¹ • ((eval0 p.1-eval0 p.2).comp P)
  have hl : ∀ d : E, ∃ C : ℝ, ∀ p, ‖L p d‖≤C := by
    intro d
    obtain ⟨C,hC⟩ := h d
    refine ⟨C,fun p => ?_⟩
    change ‖(‖p.1-p.2‖ : ℂ)⁻¹*(P d p.1-P d p.2)‖≤C
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖p.1-p.2‖⁻¹*((C:ℝ)*‖p.1-p.2‖) :=
        mul_le_mul_of_nonneg_left (hC.norm_sub_le _ _) (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ C := by
        by_cases hz : ‖p.1-p.2‖=0
        · simp [hz]
        · simp [hz,mul_left_comm]
  obtain ⟨K,hK⟩ := banach_steinhaus hl
  refine ⟨max K 0,le_max_right _ _,fun d x y => ?_⟩
  by_cases hz : x=y
  · simp [hz]
  have hn : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hh := ((L (x,y)).le_opNorm d).trans
    (mul_le_mul_of_nonneg_right ((hK (x,y)).trans (le_max_left K 0)) (norm_nonneg d))
  change ‖(‖x-y‖ : ℂ)⁻¹*(P d x-P d y)‖≤ max K 0*‖d‖ at hh
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn,←div_eq_inv_mul] at hh
  exact (div_le_iff₀ hn).mp hh
end FlatCompactness

end

end OAI
