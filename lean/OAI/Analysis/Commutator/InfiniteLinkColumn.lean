import Mathlib
import OAI.Analysis.Commutator.BiprodLinkColumn

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal NNReal

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

variable (hspan : (familySpace N right left S).starProjection=left)

lemma finite_sum_norm_sq (s : Finset S) (x : H) :
    ∑ v∈s,‖component N v.val x‖^2=(inner ℂ x (compression N S s x)).re := by
  have he := congrArg (fun T : H →L[ℂ] H => inner ℂ x (T x)) (column_square N S s)
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right] at he
  rw [←he]
  change _ = RCLike.re (inner ℂ (finiteColumn N S s x) (finiteColumn N S s x))
  rw [←norm_sq_eq_re_inner (𝕜:=ℂ)]
  rw [PiLp.norm_sq_eq_of_L2]
  exact (Finset.sum_attach s (fun v => ‖component N v.val x‖^2)).symm

include hS hspan

lemma column_hasSum (x : H) :
    HasSum (fun v : S => ‖component N v.val x‖^2) (‖x‖^2) := by
  have hc : Continuous (fun y : H => (inner ℂ x y).re) :=
    Complex.continuous_re.comp (continuous_const.inner continuous_id)
  have ht := (hc.tendsto x).comp (compression_tendsto N S hS hspan x)
  have hn : (inner ℂ x x).re=‖x‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) x).symm
  change Tendsto (fun s : Finset S => ∑ v∈s,‖component N v.val x‖^2) atTop (𝓝 (‖x‖^2))
  convert ht using 1
  · ext s
    exact finite_sum_norm_sq N S s x
  · rw [hn]

lemma column_memℓp (x : H) : Memℓp (fun v : S => component N v.val x) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (column_hasSum N S hS hspan x).summable

def infiniteColumn : H →ₗᵢ[ℂ] lp (fun _ : S => G) 2 where
  toFun x := ⟨fun v => component N v.val x,column_memℓp N S hS hspan x⟩
  map_add' x y := by ext v; exact map_add _ _ _
  map_smul' c x := by ext v; exact map_smul _ _ _
  norm_map' x := by
    let v : lp (fun _ : S => G) 2 := ⟨fun v => component N v.val x,column_memℓp N S hS hspan x⟩
    have hn : ‖v‖^2=‖x‖^2 := by
      have he := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) v
      simp only [ENNReal.toReal_ofNat,Real.rpow_two] at he
      exact he.trans (column_hasSum N S hS hspan x).tsum_eq
    exact (sq_eq_sq₀ (norm_nonneg v) (norm_nonneg x)).mp hn

@[simp] lemma infiniteColumn_apply (x : H) (v : S) :
    infiniteColumn N S hS hspan x v=component N v.val x := rfl

end Kadison.BiprodLinkColumn

end

end
end

end OAI
