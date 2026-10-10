import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVOneDimensionalHat

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_paired_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : Cover) {d : ℝ} (hd : 0 < d)
    (hc : Metric.closedBall c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ) (U : Ultrafilter ℕ),
      MeasurableSet A ∧ 0 ≤ θ ∧ StrictMono φ ∧ (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E c (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ c (r (φ i)) 2) U (𝓝 ν) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
          ∫ x in A, divergence F x) ∧
      (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
        ⟪(z.2 : Cover),z.1⟫ = 0) := by
  obtain ⟨S,B,hS,hB,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨θ,hθ,hdens⟩ := exists_density_of_cmc_monotone hd
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH c hc)
  have hsmall : 0 < min (d/2) (S/2) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsbound (i) : s i < min (d/2) (S/2) := hk _ (by omega)
  have hslim : Tendsto s atTop (𝓝 0) := hrlim.comp (tendsto_add_atTop_nat k)
  obtain ⟨A,hA,ψ,hψ,hconv,_⟩ := isMinimizerAt_blowup_limit hV hE hmin c hd
    (Metric.ball_subset_closedBall.trans hc) s hs hslim (by norm_num : (0 : ℝ) < 2)
  have hchart (i) : Metric.closedBall c (s (ψ i)*2) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.closedBall_subset_closedBall _).trans hc
    have hh := (hsbound (ψ i)).trans_le (min_le_left _ _)
    linarith
  have hmass (i) : cellBallMass μ c (s (ψ i)*2) ≤ (B*4)*(s (ψ i))^2 := by
    rw [cellBallMass_eq_spatialNormalMeasure μ c _ (Metric.ball_subset_closedBall.trans (hchart i))]
    have hh := harea μ hμ (quotientMap c) (s (ψ i)*2) (mul_pos (hs _) (by norm_num)) (by
      have hh := (hsbound (ψ i)).trans_le (min_le_right _ _)
      linarith)
    convert hh using 1
    ring
  obtain ⟨ν,_,_,hcl⟩ := blowupNormalMeasure_cluster c (fun i ↦ s (ψ i))
    (fun i ↦ hs _) (by positivity : 0 ≤ B*4) hmass
  obtain ⟨U,hU,hν⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hrl : Tendsto (fun i ↦ s (ψ i)) (U : Filter ℕ) (𝓝 0) :=
    (hslim.comp hψ.tendsto_atTop).mono_left hU
  have hcm (i) : Metric.closedBall c (s (ψ i)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.closedBall_subset_closedBall (by have hh := hs (ψ i); linarith)).trans (hchart i)
  have hm (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 2) :=
    blowup_limit_ball_mass c (fun i ↦ s (ψ i)) (fun i ↦ hs _) hrl hdens hν hρ hρ2
  have hstat (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hFs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    weakCMC_blowup_limit_stationary hμ hH c (fun i ↦ s (ψ i)) (fun i ↦ hs _)
      (by norm_num : (1 : ℝ) < 2) hcm hrl hν hF hFs
  refine ⟨A,ν,θ,fun i ↦ ψ i+k,U,hA,hθ,fun i j hij ↦ Nat.add_lt_add_right (hψ hij) k,
    hU,hconv,hν,hm,?_,stationary_quadraticMass_radial_tangent hθ (fun ρ hρ hρ1 ↦ hm ρ hρ (by linarith)) hstat⟩
  intro F hF hFs
  exact ⟨hstat F hF hFs,blowup_limit_flux hE hμ c (fun i ↦ s (ψ i)) (fun i ↦ hs _)
    (by norm_num : (1 : ℝ) < 2) hcm hν hA (hconv.mono_left hU) hF hFs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_radial_smul {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ) (x : Cover) :
    divergence (fun y ↦ ψ y • y) x = 3*ψ x+fderiv ℝ ψ x x := by
  change divergence (fun y ↦ ψ y • id y) x = _
  rw [divergence_smul_function (hψ x) differentiableAt_id,inner_gradient_left]
  simp only [id_eq]
  have hd : divergence (id : Cover → Cover) x = 3 := by
    unfold divergence
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
    norm_num [Fin.sum_univ_three]
  rw [hd]
  ring

theorem limit_set_radial_flux {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    (hrad : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
      ⟪(z.2 : Cover),z.1⟫ = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ψ x • x) := hψ.smul contDiff_id
  have hFs : tsupport (fun x ↦ ψ x • x) ⊆ Metric.closedBall (0 : Cover) 1 :=
    (tsupport_smul_subset_left ψ (fun x : Cover ↦ x)).trans (hs.trans Metric.ball_subset_closedBall)
  have he := hflux _ hF hFs
  have hz : (∫ z : BlowupNormalBundle, ⟪(z.2 : Cover),ψ z.1 • z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hrad] with z hz
    change ⟪(z.2 : Cover),ψ z.1 • z.1⟫ = 0
    by_cases hx : z.1 ∈ Metric.ball (0 : Cover) 1
    · rw [inner_smul_right,hz hx,mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh)),zero_smul,inner_zero_right]
  rw [hz] at he
  simpa only [divergence_radial_smul (hψ.differentiable (by simp))] using he.symm

lemma hasDerivAt_setIntegral_dilation {A : Set Cover} (hA : MeasurableSet A)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (s • x))
      (∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (t • x) x) t := by
  let η : Measure Cover := volume.restrict (A ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hψ.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  have hm (s : ℝ) : AEStronglyMeasurable (fun x ↦ ψ (s • x)) η := by
    have hc : Continuous (fun x : Cover ↦ s • x) := by fun_prop
    exact (hψ.continuous.comp hc).aestronglyMeasurable
  have hi : Integrable (fun x ↦ ψ (t • x)) η :=
    Integrable.of_bound (hm t) M (ae_of_all _ (fun x ↦ hM _))
  have hm' : AEStronglyMeasurable (fun x ↦ fderiv ℝ ψ (t • x) x) η := by
    have hc : Continuous (fun x : Cover ↦ t • x) := by fun_prop
    exact (((hψ.continuous_fderiv (by simp)).comp hc).clm_apply
      continuous_id).aestronglyMeasurable
  have hb : ∀ᵐ x ∂η, ∀ s ∈ (univ : Set ℝ), ‖fderiv ℝ ψ (s • x) x‖ ≤ |K| := by
    filter_upwards [ae_restrict_mem (hA.inter Metric.isClosed_closedBall.measurableSet)] with x hx s _
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.2
    calc
      _ ≤ ‖fderiv ℝ ψ (s • x)‖*‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ (s • x)‖*1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ |K| := by simpa only [mul_one] using (hK (s • x)).trans (le_abs_self K)
  have hd (x : Cover) (s : ℝ) : HasDerivAt (fun u : ℝ ↦ ψ (u • x)) (fderiv ℝ ψ (s • x) x) s := by
    convert! ((hψ.differentiable (by simp) (s • x)).hasFDerivAt).comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x) using 1
    simp only [one_smul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (univ_mem : univ ∈ 𝓝 t)
    (Eventually.of_forall hm) hi hm' hb (integrable_const (|K|))
    (ae_of_all _ fun x s _ ↦ hd x s)).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma dilation_tsupport_subset {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    tsupport (fun x : Cover ↦ ψ (t • x)) ⊆ Metric.ball (0 : Cover) 1 := by
  have hc : Continuous (fun x : Cover ↦ t • x) := by fun_prop
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ hc hx)
  have htx : t*‖x‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one ht)] using hh
  have hnx := mul_le_mul_of_nonneg_right ht (norm_nonneg x)
  simpa only [Metric.mem_ball,dist_zero_right] using (by nlinarith : ‖x‖ < 1)

lemma fderiv_dilation_apply {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ) (t : ℝ) (x : Cover) :
    fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x = t*fderiv ℝ ψ (t • x) x := by
  have hd := ((hψ (t • x)).hasFDerivAt).comp x ((hasFDerivAt_id x).const_smul t)
  have he := hd.fderiv
  change fderiv ℝ (ψ ∘ fun y : Cover ↦ t • id y) x = _ at he
  rw [show (fun y : Cover ↦ ψ (t • y)) = (ψ ∘ fun y : Cover ↦ t • id y) from rfl, he]
  simp

lemma dilation_radial_euler {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) +
      t*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (t • x) x) = 0 := by
  let η : Measure Cover := volume.restrict (A ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (t • x)) :=
    hψ.comp (contDiff_id.const_smul t)
  have hcs := dilation_tsupport_subset hs ht
  have hψs : HasCompactSupport ψ := (isCompact_closedBall (0 : Cover) 1).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  have hi : Integrable (fun x : Cover ↦ ψ (t • x)) η := by
    obtain ⟨M,hM⟩ := hψs.exists_bound_of_continuous hψ.continuous
    exact Integrable.of_bound hcomp.continuous.aestronglyMeasurable M (ae_of_all _ fun x ↦ hM _)
  have hdi : Integrable (fun x : Cover ↦ fderiv ℝ ψ (t • x) x) η := by
    obtain ⟨K,hK⟩ := (hψs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
    have hd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
    have hc : Continuous (fun x : Cover ↦ fderiv ℝ ψ (t • x) x) :=
      (hd.comp (by fun_prop : Continuous (fun x : Cover ↦ t • x))).clm_apply continuous_id
    apply Integrable.of_bound hc.aestronglyMeasurable |K|
    filter_upwards [ae_restrict_mem (hA.inter Metric.isClosed_closedBall.measurableSet)] with x hx
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.2
    calc
      _ ≤ ‖fderiv ℝ ψ (t • x)‖*‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ ψ (t • x)‖*1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ |K| := by simpa only [mul_one] using (hK (t • x)).trans (le_abs_self K)
  have he := hrad _ hcomp hcs
  have hz (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) 1) :
      3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x = 0 := by
    have hn : x ∉ tsupport (fun y : Cover ↦ ψ (t • y)) :=
      fun hh ↦ hx (Metric.ball_subset_closedBall (hcs hh))
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn]
    simp
  have heq : (∫ x in A, 3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1,
        3*ψ (t • x)+fderiv ℝ (fun y : Cover ↦ ψ (t • y)) x x := by
    rw [inter_comm A, ← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hz
  rw [heq] at he
  simp_rw [fderiv_dilation_apply (hψ.differentiable (by simp))] at he
  rw [integral_add (hi.const_mul 3) (hdi.const_mul t),integral_const_mul,integral_const_mul] at he
  exact he

theorem radial_flux_dilation_pairing {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    t^3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ x := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall (0 : Cover) 1).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun s ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (s • x)
  let J : ℝ → ℝ := fun s ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (s • x) x
  have hd (s : ℝ) (hs' : s ∈ Ici (1 : ℝ)) : HasDerivAt (fun s ↦ s^3*I s) 0 s := by
    have heg : 3*I s+s*J s = 0 := dilation_radial_euler hA hrad hψ hs hs'
    have hdiff : HasDerivAt I (J s) s := hasDerivAt_setIntegral_dilation hA hψ hψs s
    convert! (((hasDerivAt_id s).pow 3).mul hdiff).congr_deriv (show
      (3*(s^(3-1))*1)*I s+s^3*J s = 0 from by
        calc
          _ = s^2*(3*I s+s*J s) := by ring
          _ = 0 := by rw [heg,mul_zero]) using 1
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs' ↦ (hd s hs').hasDerivWithinAt) (fun _ _ ↦ by simp : ∀ x ∈ Ici (1 : ℝ), ‖(0 : ℝ)‖ ≤ 0)
    (convex_Ici (1 : ℝ)) (show (1 : ℝ) ∈ Ici (1 : ℝ) by simp) (show t ∈ Ici (1 : ℝ) from ht)
  have he : t^3*I t = (1 : ℝ)^3*I 1 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))
  simpa only [I,one_pow,one_mul,one_smul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_indicator_dilation_local {A : Set Cover} (hA : MeasurableSet A)
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    {t : ℝ} (ht : 1 ≤ t) :
    (∫ x, ψ (t • x)*A.indicator (fun _ ↦ (1 : ℝ)) x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x) := by
  have hs' := dilation_tsupport_subset hs ht
  have hind : (fun x : Cover ↦ ψ (t • x)*A.indicator (fun _ ↦ (1 : ℝ)) x) =
      A.indicator (fun x ↦ ψ (t • x)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hind,integral_indicator hA]
  rw [inter_comm A,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun y : Cover ↦ ψ (t • y))
    (fun hh ↦ hx (Metric.ball_subset_closedBall (hs' hh)))

lemma radial_flux_cone_test {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) {t : ℝ} (ht : 1 ≤ t) :
    (∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) =
      ∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) x := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have he := integral_cover_affine_scaling
    (fun x : Cover ↦ ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) 0 ht0
  simp only [add_zero,smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at he
  rw [he,integral_indicator_dilation_local hA hs ht]
  have hh := radial_flux_dilation_pairing hA hrad hψ hs ht
  rw [hh]
  have he1 := integral_indicator_dilation_local hA hs (t := 1) le_rfl
  simpa only [one_smul] using he1.symm

theorem radial_flux_cone_ae {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {t : ℝ} (ht : 1 ≤ t) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A) := by
  let f : Cover → ℝ := A.indicator (fun _ ↦ 1)
  have hm : Measurable f := measurable_const.indicator hA
  have hm' : Measurable (fun x : Cover ↦ f (t⁻¹ • x)) := hm.comp (by fun_prop)
  have hb (x : Cover) : ‖f x‖ ≤ 1 := cover_indicator_bound A x
  have hli : LocallyIntegrable f (volume : Measure Cover) :=
    (memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).locallyIntegrable le_top
  have hli' : LocallyIntegrable (fun x : Cover ↦ f (t⁻¹ • x)) (volume : Measure Cover) :=
    (memLp_top_of_bound hm'.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ hb _)).locallyIntegrable le_top
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hli'.sub hli).locallyIntegrableOn (Metric.ball (0 : Cover) 1)) (fun ψ hψ hψs hs ↦ ?_)
  · filter_upwards [hz] with x hx hxin
    have he : f (t⁻¹ • x) = f x := sub_eq_zero.mp (hx hxin)
    by_cases h1 : t⁻¹ • x ∈ A <;> by_cases h2 : x ∈ A <;> simp [f,h1,h2] at he ⊢
  · have hi : Integrable ψ (volume : Measure Cover) := hψ.continuous.integrable_of_hasCompactSupport hψs
    have hi1 : Integrable (fun x : Cover ↦ ψ x*f (t⁻¹ • x)) :=
      hi.mul_bdd hm'.aestronglyMeasurable (ae_of_all _ fun x ↦ hb _)
    have hi2 : Integrable (fun x : Cover ↦ ψ x*f x) :=
      hi.mul_bdd hm.aestronglyMeasurable (ae_of_all _ hb)
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub,integral_sub hi1 hi2]
    exact sub_eq_zero.mpr (radial_flux_cone_test hA hrad hψ hs ht)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

def affineScalarTest (p : Cover) (r : ℝ) (ψ : Cover → ℝ) (x : Cover) : ℝ :=
  ψ (r⁻¹ • (x-p))

lemma affineScalarTest_contDiff {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (p : Cover) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (affineScalarTest p r ψ) :=
  hψ.comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma affineScalarTest_tsupport {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1)
    (p : Cover) {r : ℝ} (hr : 0 < r) :
    tsupport (affineScalarTest p r ψ) ⊆ Metric.closedBall p r := by
  have hc : Continuous (fun x : Cover ↦ r⁻¹ • (x-p)) := by fun_prop
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ hc hx)
  have hh' : ‖x-p‖ / r ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hh
  simpa only [Metric.mem_closedBall,dist_eq_norm] using (div_le_iff₀ hr).mp hh' |>.trans_eq (one_mul r)

lemma fderiv_affineScalarTest {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ)
    (p : Cover) {r : ℝ} (hr : r ≠ 0) (x v : Cover) :
    fderiv ℝ (affineScalarTest p r ψ) (r • x+p) v = r⁻¹ * fderiv ℝ ψ x v := by
  have hd := (hψ (r⁻¹ • ((r • x+p)-p))).hasFDerivAt.comp (r • x+p)
    (((hasFDerivAt_id (r • x+p)).sub_const p).const_smul (r⁻¹))
  change HasFDerivAt (affineScalarTest p r ψ) _ (r • x+p) at hd
  rw [hd.fderiv]
  simp [hr]

lemma affineScalarTest_radial {ψ : Cover → ℝ} (hψ : Differentiable ℝ ψ)
    (p : Cover) {r : ℝ} (hr : r ≠ 0) (x : Cover) :
    3*affineScalarTest p r ψ (r • x+p) +
      fderiv ℝ (affineScalarTest p r ψ) (r • x+p) (r • x+p) =
      r⁻¹ * (fderiv ℝ ψ x p + r*(3*ψ x+fderiv ℝ ψ x x)) := by
  rw [fderiv_affineScalarTest hψ p hr]
  simp only [affineScalarTest,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hr,one_smul,
    map_add,map_smul,smul_eq_mul]
  field_simp
  ring

lemma radial_flux_affine_identity {A : Set Cover} (hA : MeasurableSet A)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1)
    (p : Cover) {r : ℝ} (hr : 0 < r)
    (hpr : Metric.closedBall p r ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p) *
      (fderiv ℝ ψ x p+r*(3*ψ x+fderiv ℝ ψ x x))) = 0 := by
  have he := hrad _ (affineScalarTest_contDiff hψ p r)
    ((affineScalarTest_tsupport hs p hr).trans hpr)
  rw [← integral_indicator hA] at he
  have hid : A.indicator (fun x ↦ 3*affineScalarTest p r ψ x+
      fderiv ℝ (affineScalarTest p r ψ) x x) =
      fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) x *
        (3*affineScalarTest p r ψ x+fderiv ℝ (affineScalarTest p r ψ) x x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hid,integral_cover_affine_scaling _ p hr] at he
  simp_rw [affineScalarTest_radial (hψ.differentiable (by simp)) p hr.ne',
    show ∀ a b : ℝ, a*(r⁻¹*b)=r⁻¹*(a*b) by intros; ring] at he
  rw [integral_const_mul] at he
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hr.ne'))).resolve_left (inv_ne_zero hr.ne')

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma local_indicator_pairing_tendsto {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (p : Cover) (r : ℕ → ℝ) {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {f : Cover → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ Metric.closedBall (0 : Cover) 1) :
    Tendsto (fun i ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*f x)
      l (𝓝 (∫ x in B, f x)) := by
  have hfs : HasCompactSupport f := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  let k : Cover →ᵇ ℝ := ofCompactSupport f hf hfs
  have hm (i) : Measurable (fun x : Cover ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)) :=
    (measurable_const.indicator hA).comp (by fun_prop)
  have hb (C : Set Cover) (x : Cover) : |C.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ C <;> simp [hx]
  have hh := localL1_weighted_integral_tendsto _ hm (fun i x ↦ hb A _)
    (measurable_const.indicator hB) (hb B) hconv k
  have hzero (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) 1) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have he (g : Cover → ℝ) : (∫ x in Metric.closedBall (0 : Cover) 1, g x*k x) = ∫ x, g x*f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      change g x*f x = 0
      rw [hzero x hx,mul_zero])
  simp_rw [he] at hh
  convert hh using 1
  simp only [← indicator_mul_left,one_mul,integral_indicator hB]

lemma fderiv_apply_tsupport_subset {ψ : Cover → ℝ} (p : Cover) :
    tsupport (fun x ↦ fderiv ℝ ψ x p) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by change fderiv ℝ ψ x p = 0; rw [fderiv_of_notMem_tsupport ℝ h]; rfl)

lemma radial_euler_tsupport_subset {ψ : Cover → ℝ} :
    tsupport (fun x ↦ 3*ψ x+fderiv ℝ ψ x x) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by change 3*ψ x+fderiv ℝ ψ x x = 0; rw [image_eq_zero_of_notMem_tsupport h,fderiv_of_notMem_tsupport ℝ h]; simp)

lemma indicator_pairing_integrable {A : Set Cover} (hA : MeasurableSet A)
    {f : Cover → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    (p : Cover) (r : ℝ) :
    Integrable (fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)*f x) := by
  have hm : AEStronglyMeasurable (fun x : Cover ↦ A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)) volume :=
    ((measurable_const.indicator hA).comp (by fun_prop)).aestronglyMeasurable
  have hi := (hf.integrable_of_hasCompactSupport hs).mul_bdd hm (ae_of_all _ fun x ↦ cover_indicator_bound A _)
  simpa only [mul_comm] using hi

theorem radial_cone_secondary_derivative_zero {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ x in B, fderiv ℝ ψ x p) = 0 := by
  have hc0 : Continuous (fun x ↦ fderiv ℝ ψ x p) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc1 : Continuous (fun x ↦ 3*ψ x+fderiv ℝ ψ x x) :=
    (hψ.continuous.const_mul 3).add ((hψ.continuous_fderiv (by simp)).clm_apply continuous_id)
  have hs0 := (fderiv_apply_tsupport_subset (ψ:=ψ) p).trans hs
  have hs1 := (radial_euler_tsupport_subset (ψ:=ψ)).trans hs
  have hl0 := local_indicator_pairing_tendsto hA hB p r hconv hc0 hs0
  have hl1 := local_indicator_pairing_tendsto hA hB p r hconv hc1 hs1
  have hl := hl0.add (hrlim.mul hl1)
  simp only [zero_mul,add_zero] at hl
  have he : (fun i ↦ (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*fderiv ℝ ψ x p) +
      r i*(∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*(3*ψ x+fderiv ℝ ψ x x))) =ᶠ[l] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    have hball : Metric.closedBall p (r i) ⊆ Metric.ball (0 : Cover) 1 := by
      intro x hx
      have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
      have hn := norm_add_le (x-p) p
      rw [sub_add_cancel] at hn
      simpa only [Metric.mem_ball,dist_zero_right] using (by linarith : ‖x‖ < 1)
    have hid := radial_flux_affine_identity hA hrad hψ hs p (hr i) hball
    have hi0 := indicator_pairing_integrable hA hc0 ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs0) p (r i)
    have hi1 := indicator_pairing_integrable hA hc1 ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs1) p (r i)
    have hmul (x : Cover) : A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p) *
        (fderiv ℝ ψ x p+r i*(3*ψ x+fderiv ℝ ψ x x)) =
        A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*fderiv ℝ ψ x p+
          r i*(A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*(3*ψ x+fderiv ℝ ψ x x)) := by ring
    simp_rw [hmul] at hid
    rwa [integral_add hi0 (hi1.const_mul _),integral_const_mul] at hid
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' he.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma hasDerivAt_setIntegral_translation {B : Set Cover} (hB : MeasurableSet B)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ)
    (v : Cover) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+s • v))
      (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ (x+t • v) v) t := by
  let η : Measure Cover := volume.restrict (B ∩ Metric.closedBall (0 : Cover) 1)
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    ((measure_mono inter_subset_right).trans_lt Metric.isBounded_closedBall.measure_lt_top).ne
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hψ.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  have hm (s : ℝ) : AEStronglyMeasurable (fun x ↦ ψ (x+s • v)) η :=
    (hψ.continuous.comp (by fun_prop)).continuousOn.aestronglyMeasurable
      (hB.inter Metric.isClosed_closedBall.measurableSet)
  have hi : Integrable (fun x ↦ ψ (x+t • v)) η :=
    Integrable.of_bound (hm t) M (ae_of_all _ fun x ↦ hM _)
  have hm' : AEStronglyMeasurable (fun x ↦ fderiv ℝ ψ (x+t • v) v) η :=
    (((hψ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable
  have hb : ∀ᵐ x ∂η, ∀ s ∈ (univ : Set ℝ), ‖fderiv ℝ ψ (x+s • v) v‖ ≤ |K| * ‖v‖ :=
    ae_of_all _ fun x s _ ↦ (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((hK _).trans (le_abs_self K)) (norm_nonneg _))
  have hd (x : Cover) (s : ℝ) : HasDerivAt (fun u : ℝ ↦ ψ (x+u • v)) (fderiv ℝ ψ (x+s • v) v) s := by
    convert! (hψ.differentiable (by simp) (x+s • v)).hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const v).const_add x) using 1
    simp only [one_smul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (univ_mem : univ ∈ 𝓝 t)
    (Eventually.of_forall hm) hi hm' hb (integrable_const (|K| * ‖v‖))
    (ae_of_all _ fun x s _ ↦ hd x s)).2

lemma translation_test_tsupport {ψ : Cover → ℝ}
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) (1/4)) {v : Cover} (hv : ‖v‖ ≤ 1/4)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tsupport (fun x ↦ ψ (x+t • v)) ⊆ Metric.ball (0 : Cover) (1/2) := by
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun x : Cover ↦ x+t • v)) hx)
  have hx' : ‖x+t • v‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have htv : ‖t • v‖ ≤ 1/4 := by
    rw [norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans (by simpa only [one_mul] using hv)
  have hh := norm_sub_le (x+t • v) (t • v)
  rw [add_sub_cancel_right] at hh
  simpa only [Metric.mem_ball,dist_zero_right] using (by linarith : ‖x‖ < 1/2)

lemma derivative_zero_translation_pairing {B : Set Cover} (hB : MeasurableSet B) (v : Cover)
    (hv : ‖v‖ ≤ 1/4)
    (hzero : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1 → (∫ x in B, fderiv ℝ ψ x v) = 0)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) (1/4)) :
    (∫ x, ψ x*B.indicator (fun _ ↦ (1 : ℝ)) (x-v)) =
      ∫ x, ψ x*B.indicator (fun _ ↦ (1 : ℝ)) x := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun t ↦ ∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+t • v)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt I 0 t := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ ψ (x+t • v)) :=
      hψ.comp (contDiff_id.add contDiff_const)
    have hts := (translation_test_tsupport hs hv ht).trans
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1/2 : ℝ) ≤ 1)))
    have hef (x : Cover) : fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v = fderiv ℝ ψ (x+t • v) v := by
      have hh := (hψ.differentiable (by simp) (x+t • v)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const (t • v))
      change HasFDerivAt (fun y : Cover ↦ ψ (y+t • v)) _ x at hh
      simp only [hh.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
    have hz := hzero _ hcomp hts
    have heq : (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v) =
        ∫ x in B, fderiv ℝ (fun y : Cover ↦ ψ (y+t • v)) x v := by
      rw [inter_comm B,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hx (hts hh))]
      rfl
    rw [← heq] at hz
    simp_rw [hef] at hz
    exact (hasDerivAt_setIntegral_translation hB hψ hψs v t).congr_deriv hz
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (hd t ht).hasDerivWithinAt)
    (fun _ _ ↦ by simp : ∀ t ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ)‖ ≤ 0) (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have heI : I 1=I 0 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : I t = ∫ x, ψ (x+t • v)*B.indicator (fun _ ↦ (1 : ℝ)) x := by
    change (∫ x in B ∩ Metric.closedBall (0 : Cover) 1, ψ (x+t • v)) = _
    rw [inter_comm B,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1) (translation_test_tsupport hs hv ht hh)))))]
    rw [← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [he 1 (by norm_num),he 0 (by norm_num)] at heI
  simp only [one_smul,zero_smul,add_zero] at heI
  have htrans := integral_add_right_eq_self (μ := (volume : Measure Cover)) (fun x : Cover ↦ ψ x*B.indicator (fun _ ↦ (1 : ℝ)) (x-v)) v
  simp only [add_sub_cancel_right] at htrans
  exact htrans.symm.trans heI

theorem derivative_zero_translation_ae {B : Set Cover} (hB : MeasurableSet B) (v : Cover)
    (hv : ‖v‖ ≤ 1/4)
    (hzero : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1 → (∫ x in B, fderiv ℝ ψ x v) = 0) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x-v ∈ B ↔ x ∈ B) := by
  let f : Cover → ℝ := B.indicator (fun _ ↦ 1)
  have hm : Measurable f := measurable_const.indicator hB
  have hm' : Measurable (fun x : Cover ↦ f (x-v)) := hm.comp (by fun_prop)
  have hb (x : Cover) : ‖f x‖ ≤ 1 := cover_indicator_bound B x
  have hli : LocallyIntegrable f (volume : Measure Cover) :=
    (memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).locallyIntegrable le_top
  have hli' : LocallyIntegrable (fun x : Cover ↦ f (x-v)) (volume : Measure Cover) :=
    (memLp_top_of_bound hm'.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ hb _)).locallyIntegrable le_top
  have hz := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hli'.sub hli).locallyIntegrableOn (Metric.ball (0 : Cover) (1/4))) (fun ψ hψ hψs hs ↦ ?_)
  · filter_upwards [hz] with x hx hxin
    have he : f (x-v)=f x := sub_eq_zero.mp (hx hxin)
    by_cases h1 : x-v ∈ B <;> by_cases h2 : x ∈ B <;> simp [f,h1,h2] at he ⊢
  · have hi : Integrable ψ (volume : Measure Cover) := hψ.continuous.integrable_of_hasCompactSupport hψs
    have hi1 := hi.mul_bdd hm'.aestronglyMeasurable (ae_of_all _ fun x ↦ hb (x-v))
    have hi2 := hi.mul_bdd hm.aestronglyMeasurable (ae_of_all _ hb)
    simp only [smul_eq_mul,Pi.sub_apply,mul_sub,integral_sub hi1 hi2]
    exact sub_eq_zero.mpr (derivative_zero_translation_pairing hB v hv hzero hψ hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem radial_cone_secondary_line_invariance {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hrad : ∀ ψ : Cover → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Metric.ball (0 : Cover) 1 →
      (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    (t : ℝ) (ht : |t| * ‖p‖ ≤ 1/4) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x+t • p ∈ B ↔ x ∈ B) := by
  have hz (ψ : Cover → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1) :
      (∫ x in B, fderiv ℝ ψ x (-(t • p))) = 0 := by
    simp only [map_neg,map_smul,smul_eq_mul,integral_neg,integral_const_mul]
    rw [radial_cone_secondary_derivative_zero hA hB hrad p hp r hr hrlim hconv hψ hs,mul_zero,neg_zero]
  have hv : ‖-(t • p)‖ ≤ 1/4 := by simpa only [norm_neg,norm_smul,Real.norm_eq_abs] using ht
  simpa only [sub_neg_eq_add] using derivative_zero_translation_ae hB (-(t • p)) hv hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cone_dilation_pairing {A : Set Cover} (hA : MeasurableSet A)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1)
    {t : ℝ} (ht : 1 ≤ t) :
    t^3*(∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ x := by
  have he : (∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) =
      ∫ x, ψ x*A.indicator (fun _ ↦ (1 : ℝ)) x := by
    apply integral_congr_ae
    filter_upwards [hcone t ht] with x hx
    by_cases hb : x ∈ Metric.ball (0 : Cover) 1
    · by_cases ha : x ∈ A
      · simp only [indicator_of_mem ha,indicator_of_mem ((hx hb).mpr ha)]
      · simp only [indicator_of_notMem ha,indicator_of_notMem (mt (hx hb).mp ha)]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hb (hs hh)),zero_mul,zero_mul]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hscale := integral_cover_affine_scaling
    (fun x : Cover ↦ ψ x*A.indicator (fun _ ↦ (1 : ℝ)) (t⁻¹ • x)) 0 ht0
  simp only [add_zero,smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hscale
  rw [hscale,integral_indicator_dilation_local hA hs ht] at he
  have he1 := integral_indicator_dilation_local hA hs (t := 1) le_rfl
  simp only [one_smul] at he1
  exact he.trans he1

theorem cone_radial_euler {A : Set Cover} (hA : MeasurableSet A)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) :
    (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) = 0 := by
  have hψs : HasCompactSupport ψ := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  let I : ℝ → ℝ := fun t ↦ ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, ψ (t • x)
  let J : ℝ := ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, fderiv ℝ ψ x x
  have hdI : HasDerivAt I J 1 := by
    simpa only [I,J,one_smul] using hasDerivAt_setIntegral_dilation hA hψ hψs 1
  have hdP : HasDerivAt (fun t : ℝ ↦ t^3*I t) (3*I 1+J) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).pow 3).mul hdI).congr_deriv (show
      (3 : ℝ)*1^(3-1)*1*I 1+1^3*J = 3*I 1+J by norm_num) using 1
  have hc : HasDerivWithinAt (fun t : ℝ ↦ t^3*I t) 0 (Ici 1) 1 :=
    (hasDerivWithinAt_const 1 (Ici (1 : ℝ)) (I 1)).congr
      (fun t ht ↦ by
        have hh := cone_dilation_pairing hA hcone hs ht
        simpa only [I,one_smul] using hh)
      (by norm_num)
  have he : 3*I 1+J=0 :=
    (hdP.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 1)).symm.trans
      (hc.derivWithin (uniqueDiffWithinAt_Ici 1))
  have hi : IntegrableOn ψ (A ∩ Metric.closedBall (0 : Cover) 1) :=
    (hψ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set inter_subset_right
  have hdi : IntegrableOn (fun x ↦ fderiv ℝ ψ x x) (A ∩ Metric.closedBall (0 : Cover) 1) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_id).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set inter_subset_right
  have heq : (∫ x in A, 3*ψ x+fderiv ℝ ψ x x) =
      ∫ x in A ∩ Metric.closedBall (0 : Cover) 1, 3*ψ x+fderiv ℝ ψ x x := by
    rw [inter_comm A,← Measure.restrict_restrict Metric.isClosed_closedBall.measurableSet]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport ψ := fun hh ↦ hx (Metric.ball_subset_closedBall (hs hh))
    rw [image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn]
    simp
  rw [heq,integral_add (hi.const_mul 3) hdi,integral_const_mul]
  simpa only [I,J,one_smul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localL1_triangle {η : Measure Cover} [IsFiniteMeasure η]
    {f g h : Cover → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) (hhb : ∀ x, |h x| ≤ 1) :
    (∫ x, |f x-h x| ∂η) ≤ (∫ x, |f x-g x| ∂η)+(∫ x, |g x-h x| ∂η) := by
  have hi := integrable_bounded_one hf hfb (η := η)
  have hj := integrable_bounded_one hg hgb (η := η)
  have hk := integrable_bounded_one hh hhb (η := η)
  rw [← integral_add (f := fun x ↦ |f x-g x|) (g := fun x ↦ |g x-h x|)
    (hi.sub hj).abs (hj.sub hk).abs]
  exact integral_mono (hi.sub hk).abs ((hi.sub hj).abs.add (hj.sub hk).abs)
    (fun x ↦ abs_sub_le (f x) (g x) (h x))

theorem actual_tangent_secondary_representation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∃ (c : ℕ → Cover) (q : ℕ → ℝ), (∀ i, ‖c i-cubeCenter‖ ≤ 1/8) ∧
        (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun i ↦ ((i : ℝ)+1)⁻¹
  have hepos (i) : 0 < e i := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hnex (i : ℕ) : ∃ n : ℕ, i ≤ n ∧ r n < 1/(8*(‖p‖+1)) ∧
      (∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r n) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) <
          (s i)^3*e i := by
    have hp0 : 0 < (1 : ℝ)/(8*(‖p‖+1)) := by positivity
    exact ((eventually_ge_atTop i).and ((hrlim.eventually (Iio_mem_nhds hp0)).and
      (hconv.eventually (Iio_mem_nhds (mul_pos (pow_pos (hs i) 3) (hepos i)))))).exists
  choose n hn hnr hne using hnex
  have hnlim : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop b).mono (fun i hi ↦ hi.trans (hn i))
  let c : ℕ → Cover := fun i ↦ cubeCenter+r (n i) • p
  let q : ℕ → ℝ := fun i ↦ r (n i)*s i
  have hq (i) : 0 < q i := mul_pos (hr _) (hs _)
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,mul_zero,Function.comp_apply] using (hrlim.comp hnlim).mul hslim
  have hcp (i) : ‖c i-cubeCenter‖ ≤ 1/8 := by
    simp only [c,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := (lt_div_iff₀ (by positivity : 0 < 8*(‖p‖+1))).mp (hnr i)
    nlinarith [hr (n i),norm_nonneg p]
  have hc (i) : Metric.ball (c i) (1/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply Set.Subset.trans _ (cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ)<1/2))
    intro x hx
    have hxp : ‖x-c i‖ < 1/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hh := norm_add_le (x-c i) (c i-cubeCenter)
    rw [sub_add_sub_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_eq_norm] using (by linarith [hcp i] : ‖x-cubeCenter‖ ≤ 1/4)
  obtain ⟨B,hB,φ,hφ,hBconv,_⟩ := isMinimizerAt_moving_blowup_limit hV hE hmin c
    (by norm_num : (0 : ℝ)<1/8) hc q hq hqlim (by norm_num : (0 : ℝ)<1)
  have herror (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-blowupCharacteristic E (c i) (q i) x|) ≤ e i := by
    have hsub : Metric.closedBall p (s i*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
      intro x hx
      have hh : ‖x-p‖ ≤ s i := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
      have hnn := norm_add_le (x-p) p
      rw [sub_add_cancel] at hnn
      simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith [hs1 i] : ‖x‖ ≤ 2)
    have hi : IntegrableOn (fun x ↦ |blowupCharacteristic E cubeCenter (r (n i)) x-
        A.indicator (fun _ ↦ (1 : ℝ)) x|) (Metric.closedBall (0 : Cover) 2) :=
      ((integrable_bounded_one (measurable_blowupCharacteristic hE _ _) (blowupCharacteristic_bound E _ _)).sub
        (integrable_bounded_one (measurable_const.indicator hA) (cover_indicator_bound A))).abs
    have hb := (local_affine_integral_le p (hs i) hi (fun _ ↦ abs_nonneg _) hsub).trans
      (mul_le_mul_of_nonneg_left (hne i).le (pow_nonneg (inv_nonneg.mpr (hs i).le) 3))
    have heq : (s i)⁻¹^3*((s i)^3*e i)=e i := by field_simp [(hs i).ne']
    rw [heq] at hb
    simpa only [blowupCharacteristic_affine,c,q,abs_sub_comm] using hb
  refine ⟨B,hB,φ,hφ,?_, (fun i ↦ c (φ i)), (fun i ↦ q (φ i)),
    (fun i ↦ hcp (φ i)), (fun i ↦ hq (φ i)), hqlim.comp hφ.tendsto_atTop, hBconv⟩
  have hbound (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) ≤
      e (φ i)+(∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E (c (φ i)) (q (φ i)) x-B.indicator (fun _ ↦ (1 : ℝ)) x|) := by
    exact (localL1_triangle ((measurable_const.indicator hA).comp (by fun_prop))
      (measurable_blowupCharacteristic hE (c (φ i)) (q (φ i))) (measurable_const.indicator hB)
      (fun _ ↦ cover_indicator_bound A _) (blowupCharacteristic_bound E (c (φ i)) (q (φ i))) (cover_indicator_bound B)).trans
      (add_le_add (herror (φ i)) le_rfl)
  exact squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) hbound
    (by simpa using (helim.comp hφ.tendsto_atTop).add hBconv)

theorem actual_tangent_secondary_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) := by
  obtain ⟨B,hB,φ,hφ,hconv',_⟩ := actual_tangent_secondary_representation hV hE hmin
    r hr hrlim hA hconv p hp s hs hs1 hslim
  exact ⟨B,hB,φ,hφ,hconv'⟩

end CubicTorus

end
end

end

end OAI
