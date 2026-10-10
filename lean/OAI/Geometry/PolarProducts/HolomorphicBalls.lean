import OAI.Geometry.PolarProducts.RadialMap

namespace OAI

universe u41 u42 u43 u44 u45 u46 u47 u48 u49

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff

open Set
namespace SingularComparison
noncomputable section

theorem exists_inner_radius {μ α R : ℝ} (hμ : 0 ≤ μ) (hμα : μ < α)
    (hR : 0 < R) (M C : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ (t δ H : ℝ), 0 < t → t ≤ r^2 → 0 < δ →
      H ≤ α * Real.log t + C → H + 2 ≤ μ * Real.log (t + δ) - M := by
  let L := (-M - C - 2) / (α - μ)
  obtain ⟨r, hr, hrsmall⟩ := exists_between (show (0 : ℝ) < min R (Real.sqrt (Real.exp L)) by
    exact lt_min hR (Real.sqrt_pos.mpr (Real.exp_pos L)))
  refine ⟨r, hr, hrsmall.trans_le (min_le_left _ _), ?_⟩
  intro t δ H ht htr hδ hH
  have hre : r < Real.sqrt (Real.exp L) := hrsmall.trans_le (min_le_right _ _)
  have hr2 : r^2 ≤ Real.exp L := by
    have hs := Real.sq_sqrt (Real.exp_pos L).le
    nlinarith [Real.sqrt_nonneg (Real.exp L)]
  have htL : Real.log t ≤ L := by
    calc
      Real.log t ≤ Real.log (Real.exp L) := Real.log_le_log ht (htr.trans hr2)
      _ = L := Real.log_exp L
  have hlog : Real.log t ≤ Real.log (t + δ) := Real.log_le_log ht (by linarith)
  have hcoef : (α - μ) * Real.log t ≤ -M - C - 2 := by
    calc
      _ ≤ (α - μ) * L := mul_le_mul_of_nonneg_left htL (sub_nonneg.mpr hμα.le)
      _ = -M - C - 2 := by dsimp [L]; field_simp [sub_ne_zero.mpr hμα.ne']
  have hmono := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem outer_comparison {μ R δ H L M : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hH : L ≤ H)
    (hM : μ * Real.log (R^2 + 1) - L + 2 < M) :
    μ * Real.log (R^2 + δ) - M + 2 < H := by
  have hp : 0 < R^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg R) hδ
  have hlog := Real.log_le_log hp (show R^2 + δ ≤ R^2 + 1 by linarith)
  have hh := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem radius_bound {a μ r δ : ℝ} (ha : 0 < a) (_ham : a < μ) (hr : 0 < r)
    (hδ : 0 < δ) (hδb : δ < r^2 * (μ / a - 1)) :
    a < r^2 * (1 + μ / (r^2 + δ)) := by
  have hd : 0 < r^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg r) hδ
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hδa : δ * a < r^2 * (μ - a) := by
    calc
      δ * a < (r^2 * (μ / a - 1)) * a := mul_lt_mul_of_pos_right hδb ha
      _ = r^2 * (μ - a) := by field_simp
  have hfrac : a < r^2 * μ / (r^2 + δ) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  calc
    a < r^2 * μ / (r^2 + δ) := hfrac
    _ < r^2 * (1 + μ / (r^2 + δ)) := by
      rw [mul_add, mul_one, mul_div_assoc]
      linarith

end
end SingularComparison

namespace ComplexPotential

open Set Filter RadialSymplectic
open scoped ContDiff Topology

noncomputable section

variable {E : Type u41} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_ball_from_logarithmic_pole (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {U : Set E} (hU : IsOpen U) (hU0 : (0 : E) ∈ U)
    {τ H : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hτ0 : τ 0 = 0)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ U ∧ τ x ≤ s})
    {s₀ α C ρ : ℝ} (hs₀ : s₀ < 1) (hρ : 0 < ρ)
    (htail : ∀ x ∈ U, s₀ ≤ τ x → H x = τ x)
    (hpole : ∀ x ∈ U, x ≠ 0 → ‖x‖ ≤ ρ → H x ≤ α * Real.log (‖x‖^2) + C)
    {a : ℝ} (ha : 0 < a) (haα : a < α) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → F x ∈ U) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x v)
          (fderiv ℝ (F : E → E) x w) = standardTensor J v w := by
  obtain ⟨μ, haμ, hμα⟩ := exists_between haα
  have hμ : 0 < μ := ha.trans haμ
  have hn : {x : E | x ∈ U ∧ τ x < 1/2} ∈ 𝓝 (0 : E) := by
    exact inter_mem (hU.mem_nhds hU0)
      ((hτ 0 hU0).1.continuousAt.eventually_lt continuousAt_const (by norm_num [hτ0]))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hn
  let R := ε / 2
  have hR : 0 < R := half_pos hε
  have hRball (x : E) (hx : ‖x‖ ≤ R) : x ∈ U ∧ τ x < 1/2 := by
    apply hεball
    rw [Metric.mem_ball, dist_zero_right]
    exact hx.trans_lt (half_lt_self hε)
  have hsp : IsCompact {x : E | ‖x‖ = R} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) R
  have hcont : ContinuousOn H {x : E | ‖x‖ = R} := by
    intro x hx
    apply ((hH x (hRball x hx.le).1 ?_).1.continuousAt).continuousWithinAt
    intro hz
    have : R = 0 := by simpa [hz] using hx.symm
    exact hR.ne' this
  obtain ⟨L, hL⟩ := hsp.bddBelow_image hcont
  let M := μ * Real.log (R^2 + 1) - L + 3
  obtain ⟨r, hr, hrlt, hrdom⟩ := SingularComparison.exists_inner_radius hμ.le hμα
    (lt_min hR hρ) M C
  have hrR : r < R := hrlt.trans_le (min_le_left _ _)
  have hrρ : r < ρ := hrlt.trans_le (min_le_right _ _)
  have hδmax : 0 < min (1 : ℝ) (r^2 * (μ / a - 1)) := by
    apply lt_min zero_lt_one
    exact mul_pos (sq_pos_of_pos hr) (sub_pos.mpr ((one_lt_div ha).mpr haμ))
  obtain ⟨δ, hδ, hδlt⟩ := exists_between hδmax
  have hδ1 : δ ≤ 1 := (hδlt.trans_le (min_le_left _ _)).le
  have hδb : δ < r^2 * (μ / a - 1) := hδlt.trans_le (min_le_right _ _)
  let P : E → ℝ := fun x => μ * logNormSq δ x - M
  have hP (x : E) : IsPSHAt J P x :=
    ((isPSHAt_logNormSq J hsk hJ hJJ hδ.le
      (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ)).const_smul hμ.le).sub_const M
  have hinner (x : E) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ r) : H x + 1 ≤ P x := by
    have hxu := (hRball x (hx.trans hrR.le)).1
    have hh := hrdom (‖x‖^2) δ (H x) (sq_pos_of_pos (norm_pos_iff.mpr hx0))
      ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr hx) hδ
      (hpole x hxu hx0 (hx.trans hrρ.le))
    change H x + 1 ≤ μ * Real.log (‖x‖^2 + δ) - M
    linarith
  have houter (x : E) (_hx : x ∈ U) (hnorm : ‖x‖ = R) : P x + 1 < H x := by
    have hh := SingularComparison.outer_comparison hμ.le hδ hδ1
      (hL ⟨x, hnorm, rfl⟩) (show μ * Real.log (R^2 + 1) - L + 2 < M by dsimp [M]; linarith)
    change μ * Real.log (‖x‖^2 + δ) - M + 1 < H x
    rw [hnorm]
    linarith
  let T := gluedPotential R H P
  have hT (x : E) (hx : x ∈ U) : IsPSHAt J T x :=
    isPSHAt_gluedPotential J hJJ hr hrR H P hH (fun x _ => hP x) hinner houter hx
  obtain ⟨σ, hσmin, hσ1⟩ := exists_between (show max s₀ (1/2 : ℝ) < 1 from
    max_lt hs₀ (by norm_num))
  have hσ0 : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2)
    ((le_max_right _ _).trans_lt hσmin)
  let K : Set E := {x | x ∈ U ∧ τ x ≤ σ}
  have hK : IsCompact K := hcompact σ hσ0 hσ1
  have heq (x : E) (hx : x ∈ U) (hxK : x ∉ K) : T x = τ x := by
    have hστ : σ < τ x := lt_of_not_ge (fun h => hxK ⟨hx, h⟩)
    have hnorm : R ≤ ‖x‖ := by
      by_contra hh
      have hhalf := (hRball x (not_le.mp hh).le).2
      linarith [(le_max_right s₀ (1/2 : ℝ)).trans_lt hσmin]
    exact (gluedPotential_outer R H P hnorm).trans (htail x hx
      (((le_max_left _ _).trans_lt hσmin).le.trans hστ.le))
  obtain ⟨Q, hQ, hQi, _hout, hQmap, hQpull⟩ := exists_potential_transport J hsk hJ
    hU hK (fun _ hx => hx.1) hτ hT heq
  let F := (radialHomeomorph (E := E) hμ hδ).symm.trans Q
  have hF : ContDiff ℝ ∞ (F : E → E) := hQ.comp (contDiff_radialContraction hμ hδ)
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := (contDiff_radialExpansion hμ hδ).comp hQi
  have hmap (x : E) (hx : ‖x‖^2 < a) : ‖radialContraction μ δ x‖ < r := by
    apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
    apply radialContraction_mapsTo hμ hδ _ hx
    calc
      a ≤ r^2 * (1 + μ / (r^2 + δ)) := (SingularComparison.radius_bound ha haμ hr hδ hδb).le
      _ = radiusSq μ δ (r^2) := by unfold radiusSq; ring
  have hUmap (x : E) (hx : ‖x‖^2 < a) : radialContraction μ δ x ∈ U :=
    (hRball _ ((hmap x hx).trans hrR).le).1
  refine ⟨F, hF, hFi, fun x hx => (hQmap _).mpr (hUmap x hx), ?_⟩
  intro x hx v w
  change ddc J (fun y => ‖y‖^2 + τ y) (Q (radialContraction μ δ x))
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x v)
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x w) = _
  rw [fderiv_comp x (hQ.differentiable (by simp) _) ((contDiff_radialContraction hμ hδ).differentiable
    (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQpull _ (hUmap x hx)]
  have heT : (fun z : E => ‖z‖^2 + T z) =ᶠ[𝓝 (radialContraction μ δ x)]
      fun z => modelPotential μ δ z - M := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const (hmap x hx)] with z hz
    dsimp only [T]
    rw [gluedPotential_inner hrR H P hinner hz.le]
    dsimp [P, logNormSq, modelPotential]
    ring
  rw [ddc_congr J heT, ddc_sub_const J (contDiff_modelPotential μ hδ).contDiffAt,
    radialContraction_pullback J hsk hμ hδ]

end
end ComplexPotential

namespace TensorCalculus

open Set Filter
open scoped Topology ContDiff

variable {E : Type u42} {F : Type u43} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

local instance pullbackOneTensorGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance pullbackOneTensorSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

def pullbackOneForm (f : E → F) (γ : F → F →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℝ :=
  (γ (f x)).comp (fderiv ℝ f x)

@[simp] theorem pullbackOneForm_apply (f : E → F) (γ : F → F →L[ℝ] ℝ) (x a : E) :
    pullbackOneForm f γ x a = γ (f x) (fderiv ℝ f x a) := rfl

theorem fderiv_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hd : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    fderiv ℝ (pullbackOneForm f γ) x a b =
      fderiv ℝ γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) +
        γ (f x) (fderiv ℝ (fderiv ℝ f) x a b) := by
  unfold pullbackOneForm
  rw [fderiv_clm_comp (c := fun y => γ (f y)) (hγ.comp x hf) hd]
  rw [show fderiv ℝ (fun y => γ (f y)) x = (fderiv ℝ γ (f x)).comp (fderiv ℝ f x) by
    exact fderiv_comp x hγ hf]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  ring

theorem exteriorD_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    exteriorD (pullbackOneForm f γ) x a b =
      exteriorD γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hf' := hf.differentiableAt (by simp)
  have hs := hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [exteriorD_apply, fderiv_pullbackOneForm hf' hd hγ]
  rw [hs.eq a b]
  ring

end
end TensorCalculus

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u44} {F : Type u45} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

theorem dc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x))
    (hCR : ∀ a, fderiv ℝ f x (J a) = K (fderiv ℝ f x a)) :
    dc J (φ ∘ f) x = pullbackOneForm f (dc K φ) x := by
  ext a
  rw [dc_apply, fderiv_comp x hφ hf, ContinuousLinearMap.comp_apply, hCR,
    pullbackOneForm_apply, dc_apply]

theorem ddc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hφ : ContDiffAt ℝ ∞ φ (f x))
    (hCR : ∀ᶠ y in 𝓝 x, ∀ a, fderiv ℝ f y (J a) = K (fderiv ℝ f y a)) (a b : E) :
    ddc J (φ ∘ f) x a b = ddc K φ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (φ ∘ f) =ᶠ[𝓝 x] pullbackOneForm f (dc K φ) := by
    filter_upwards [(hf.of_le h1).eventually (by simp),
      hf.continuousAt ((hφ.of_le h1).eventually (by simp)), hCR] with y hy hz hc
    exact dc_comp J K (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) φ (f y) from hz).differentiableAt one_ne_zero) hc
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  exact exteriorD_pullbackOneForm hf ((contDiffAt_dc K hφ).differentiableAt (by simp)) a b

end
end ComplexPotential

namespace ComplexPotential

open Set Filter TensorCalculus
open scoped ContDiff Topology

noncomputable section

variable {E : Type u46} {F : Type u47} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexStructure (E : Type u48) [NormedAddCommGroup E] [NormedSpace ℂ E] : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] theorem complexStructure_apply (a : E) : complexStructure E a = Complex.I • a := rfl

theorem complexStructure_sq (a : E) : complexStructure E (complexStructure E a) = -a := by
  simp [complexStructure_apply, smul_smul]

theorem complexStructure_norm (a : E) : ‖complexStructure E a‖ = ‖a‖ := by
  simp [complexStructure_apply, norm_smul]

theorem fderiv_commutes_complexStructure {f : E → F} {x : E}
    (hf : DifferentiableAt ℂ f x) (a : E) :
    fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) := by
  rw [hf.fderiv_restrictScalars ℝ]
  simp [complexStructure_apply]

theorem complexStructure_skew {G : Type u49} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (a b : G) :
    let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) a (complexStructure G b) = -inner (𝕜 := ℝ) (complexStructure G a) b := by
  let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner ℂ, inner_smul_right, inner_smul_left]

theorem IsPSHAt.holomorphic_comp {f : E → F} {φ : F → ℝ} {x : E}
    (hφ : IsPSHAt (complexStructure F) φ (f x))
    (hf : ContDiffAt ℝ ∞ f x) (hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y) :
    IsPSHAt (complexStructure E) (φ ∘ f) x := by
  refine ⟨hφ.1.comp x hf, fun a => ?_⟩
  rw [ddc_comp (complexStructure E) (complexStructure F) hf hφ.1
    (hhol.mono (fun y hy => fderiv_commutes_complexStructure hy)),
    fderiv_commutes_complexStructure hhol.self_of_nhds]
  exact hφ.2 _

end
end ComplexPotential

end LowerBoundInline

end OAI
