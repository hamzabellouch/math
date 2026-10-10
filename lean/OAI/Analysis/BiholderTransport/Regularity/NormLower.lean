import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.QuantitativeDividedAction
import OAI.Analysis.BiholderTransport.Coordinates.JoiningCoordinates
import OAI.Analysis.BiholderTransport.Coordinates.FixedJoinSmooth
import OAI.Analysis.BiholderTransport.Coordinates.FixedJoinDifference

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

lemma exists_norm_sq_lower_of_injective (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ c>0, ∀ v:E, c*‖v‖^2 ≤ ‖L v‖^2 := by
  obtain ⟨K,hK,HK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hKr),?_⟩
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz L HK v
  have H2 := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg K.coe_nonneg (norm_nonneg (L v)))).mpr H
  rw [mul_pow] at H2
  have HH : ‖v‖^2/(K:ℝ)^2 ≤ ‖L v‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hKr)).mpr (by simpa only [mul_comm] using H2)
  simpa only [div_eq_mul_inv,mul_comm] using HH

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_fixedJoinMiddle_lower_crossing {x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh : 0<h) (hh1 : h<1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ c>0, ∀ᶠ T in 𝓝 (1:ℝ), h<T → T<1 →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(1-T)*‖k‖^2 ≤ fixedJoinMiddle x h T p k k-fixedJoinMiddle x h 1 p k k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ V := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let z := (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
  let q : TangentSpace 𝓘(ℝ,Model n) z :=
    (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2
  have Hcoords := exists_smooth_joining_coordinates hh.ne' hleft
  dsimp only at Hcoords
  rw [riemannianExp_smul] at Hcoords
  obtain ⟨g,hg,hg0,hgi,hginj⟩ := Hcoords
  obtain ⟨a,ha,Ha⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ g p) hginj
  obtain ⟨c,hc,Hc⟩ := exists_uniform_divided_hessian_gap (n := n) (M := M) ‖q‖
  have hden : 0<1-h := sub_pos.mpr hh1
  let t : ℝ → ℝ := fun T => (T-h)/(1-h)
  have htcont : ContinuousAt t 1 := by fun_prop
  have ht1 : t 1=1 := div_self hden.ne'
  have htend : Tendsto t (𝓝 1) (𝓝 1) := by simpa only [ht1] using htcont.tendsto
  refine ⟨c*a/(1-h)^2,div_pos (mul_pos hc ha) (sq_pos_of_pos hden),?_⟩
  filter_upwards [htend.eventually Hc] with T hCT
  intro hT hT1 k
  have ht0 : 0<t T := div_pos (sub_pos.mpr hT) hden
  have htt1 : t T<1 := (div_lt_one hden).mpr (by linarith)
  have htq : t T • q∈injectivityDomain z :=
    contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors z hright) ht0 htt1
  have heT : t T • q=(T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 := by
    dsimp [t,q]
    rw [smul_smul,div_mul_cancel₀ _ hden.ne']
  have hBT := (fixedJoinAction_contDiffAt hT.ne' hleft (heT ▸ htq)).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB1 := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HD := fixedJoinMiddle_difference_normal ht0.ne'
    (by dsimp [t]; field_simp)
    hright htq (shifted_exp_endpoint x p h)
    (by rw [heT]; exact shifted_exp_time x p h T)
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hg0 hgi hBT hB1 k
  rw [HD]
  have HH := hCT z q (fderiv ℝ g p k) le_rfl ht0 htt1 hright
  have H : c*(1-t T)*‖fderiv ℝ g p k‖^2 ≤
      hessianValue z (t T • q) (fderiv ℝ g p k)/(t T)-hessianValue z q (fderiv ℝ g p k) := by
    linarith only [HH]
  have HA := mul_le_mul_of_nonneg_left (Ha k) (mul_nonneg hc.le (sub_pos.mpr htt1).le)
  have HL := (div_le_div_iff_of_pos_right hden).mpr (HA.trans H)
  convert! HL using 1
  dsimp [t]
  field_simp
  ring

end WeakMTWTransport

end

end OAI
