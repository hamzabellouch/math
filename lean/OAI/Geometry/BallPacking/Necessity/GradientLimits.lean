import Mathlib
import OAI.Geometry.BallPacking.Necessity.FreezeJ
import OAI.Geometry.BallPacking.Necessity.SchauderBounds

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

theorem exists_nested_complex_cutoffs :
    ∃ (χ θ : ℂ → ℝ) (D : ℝ), 0 ≤ D ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport χ ⊆ Metric.closedBall (0:ℂ) 2 ∧
      tsupport θ ⊆ Metric.closedBall (0:ℂ) 3 ∧
      χ =ᶠ[𝓝 0] (fun _ => (1:ℝ)) ∧
      (∀ z ∈ tsupport χ, θ z=1) ∧
      (∀ z, |χ z| ≤ 1 ∧ |θ z| ≤ 1) ∧
      (∀ z, ‖fderiv ℝ χ z‖ ≤ D ∧ ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D ∧
        ‖fderiv ℝ θ z‖ ≤ D) := by
  let χ : ContDiffBump (0:ℂ) := ⟨1,2,by norm_num,by norm_num⟩
  let θ : ContDiffBump (0:ℂ) := ⟨2,3,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : ℂ → ℝ) := χ.contDiff
  have hθ : ContDiff ℝ ∞ (θ : ℂ → ℝ) := θ.contDiff
  have hχD : ContDiff ℝ ∞ (fderiv ℝ (χ : ℂ → ℝ)) := hχ.fderiv_right (by simp)
  obtain ⟨D₁,hD₁,hB₁⟩ := ((χ.hasCompactSupport.fderiv ℝ).isCompact_range
    (hχ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hbD2 : Bornology.IsBounded (range (fderiv ℝ (fderiv ℝ (χ : ℂ → ℝ)))) :=
    (((χ.hasCompactSupport.fderiv ℝ).fderiv ℝ).isCompact_range
      (hχD.continuous_fderiv (by simp))).isBounded
  obtain ⟨D₂,hD₂,hB₂⟩ := hbD2.exists_pos_norm_le
  obtain ⟨D₃,hD₃,hB₃⟩ := ((θ.hasCompactSupport.fderiv ℝ).isCompact_range
    (hθ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨χ,θ,D₁+D₂+D₃,by positivity,hχ,χ.hasCompactSupport,hθ,θ.hasCompactSupport,?_,?_,?_,?_,?_,?_⟩
  · rw [χ.tsupport_eq]
  · rw [θ.tsupport_eq]
  · exact χ.eventuallyEq_one
  · intro z hz
    rw [χ.tsupport_eq] at hz
    exact θ.one_of_mem_closedBall hz
  · intro z
    constructor
    · rw [abs_of_nonneg χ.nonneg]
      exact χ.le_one
    · rw [abs_of_nonneg θ.nonneg]
      exact θ.le_one
  · intro z
    have h1 := hB₁ _ (mem_range_self z)
    have h2 := hB₂ _ (mem_range_self z)
    have h3 := hB₃ _ (mem_range_self z)
    exact ⟨by linarith,by linarith,by linarith⟩


 

 

 

open scoped Topology ContDiff
open Set Filter Function
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_bound_of_holder_and_values (f : E → F)
    (hf : Differentiable ℝ f) {M C r α : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hr : 0 < r) (hα : 0 ≤ α)
    (hv : ∀ z ∈ Metric.closedBall (0:E) r, ‖f z‖ ≤ M)
    (hD : ∀ z ∈ Metric.closedBall (0:E) r,
      ‖fderiv ℝ f z-fderiv ℝ f 0‖ ≤ C*‖z‖^α) :
    ‖fderiv ℝ f 0‖ ≤ 2*M/r+C*r^α := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hvn
  have hrv : r • v ∈ Metric.closedBall (0:E) r := by
    simp [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hvn]
  have h0 : (0:E) ∈ Metric.closedBall (0:E) r := Metric.mem_closedBall_self hr.le
  have herr := (convex_closedBall (0:E) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) (φ := fderiv ℝ f 0) (C := C*r^α)
    (fun z hz => (hD z hz).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa using hz) hα) hC)) h0 hrv
  simp only [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hvn,mul_one] at herr
  have hval : ‖f (r • v)-f 0‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hv (r • v) hrv,hv 0 h0])
  have hsum := norm_sub_le (f (r • v)-f 0)
    (f (r • v)-f 0-(fderiv ℝ f 0) (r • v))
  rw [sub_sub_cancel] at hsum
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hsum
  rw [map_smul] at herr
  have hbound : r*‖(fderiv ℝ f 0) v‖ ≤ 2*M+(C*r^α)*r := by linarith
  have hh : ‖(fderiv ℝ f 0) v‖ ≤ (2*M+(C*r^α)*r)/r :=
    (le_div_iff₀ hr).mpr (by nlinarith)
  convert hh using 1
  field_simp

theorem norm_fderiv_tendsto_zero_of_holder {f : ℕ → E → F}
    (hf : ∀ j, Differentiable ℝ (f j)) {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hD : ∀ᶠ j in atTop, ∀ x y, ‖fderiv ℝ (f j) x-fderiv ℝ (f j) y‖ ≤ C*‖x-y‖^α)
    (hv : TendstoUniformlyOn f (fun _ => (0:F)) atTop (Metric.closedBall (0:E) 1)) :
    Tendsto (fun j => ‖fderiv ℝ (f j) 0‖) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (norm_nonneg _))
  intro ε hε
  have hpow : Tendsto (fun r : ℝ => C*r^α) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hα)] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => C) (𝓝[>] 0) (𝓝 C)).mul
        ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.mono_left nhdsWithin_le_nhds))
  have hs := hpow.eventually (gt_mem_nhds (show 0 < ε/2 by linarith))
  have hs' : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hr1,hsmall⟩ := (hpos.and (hs'.and hs)).exists
  have hδ : 0 < ε*r/8 := by positivity
  have hev := (Metric.tendstoUniformlyOn_iff.mp hv) (ε*r/8) hδ
  filter_upwards [hev,hD] with j hj hjD
  have hb := derivative_bound_of_holder_and_values (f j) (hf j) (M := ε*r/8)
    (C := C) hδ.le hC hr hα.le
    (fun z hz => le_of_lt (by
      have hh := hj z (Metric.closedBall_subset_closedBall hr1.le hz)
      simpa [dist_eq_norm] using hh))
    (fun z _ => by simpa using hjD z 0)
  have hid : 2*(ε*r/8)/r=ε/4 := by field_simp; ring
  rw [hid] at hb
  linarith

end

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gradientLimitsC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance gradientLimitsC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance gradientLimitsCompactNormedAddCommGroup (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance gradientLimitsCompactNormedSpace (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

private theorem exists_small_principal_const (B K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      B*max δ ((2*δ)^((2:ℝ)/3)*K^((1:ℝ)/3)) ≤ 1/2 := by
  let g : ℝ → ℝ := fun r => B*max r ((2*r)^((2:ℝ)/3)*K^((1:ℝ)/3))
  have hg : Continuous g := by
    exact continuous_const.mul (continuous_id.max
      (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 2/3)).comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (show (2:ℝ)/3 ≠ 0 by norm_num)]
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, g r < 1/2 := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds (show g 0 < (1:ℝ)/2 by rw [hg0]; norm_num))
  have hr1 : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,h0,h1,hg⟩ := (hr0.and (hr1.and hev)).exists
  exact ⟨r,h0,h1.le,hg.le⟩

theorem smallCR_sequence_derivative_zero
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (A : ℕ → ℂ → E →L[ℝ] E) (hA : ∀ j, ContDiff ℝ ∞ (A j))
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hAD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (A j) z‖ ≤ K)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I-Complex.I • fderiv ℝ (u j) z 1=
        A j z (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 3))
    (hA0 : TendstoUniformlyOn A (fun _ => (0:E →L[ℝ] E)) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  obtain ⟨χ,θ,D,hD,hχ,hχc,hθ,hθc,hχ2,hθ3,hχ1,hθ1,hχθ,hd⟩ := exists_nested_complex_cutoffs
  have hχ3 : tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 :=
    hχ2.trans (Metric.closedBall_subset_closedBall (by norm_num))
  let B := 2*‖compactCRInverse (E := E) 3‖*‖c1HolderDx (E := E)‖
  obtain ⟨δ,hδ,hδ1,hsmall⟩ := exists_small_principal_const B (K+D)
  have hu1 : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖u j z‖ ≤ 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu0 1 (by norm_num)] with j hj
    intro z hz
    exact le_of_lt (by simpa [dist_eq_norm] using hj z hz)
  have hAδ : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖A j z‖ ≤ δ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hA0 δ hδ] with j hj
    intro z hz
    exact le_of_lt (by simpa [dist_eq_norm] using hj z hz)
  let v : ℕ → ℂ → E := fun j z => χ z • u j z
  have hv : ∀ j, ContDiff ℝ ∞ (v j) := fun j => hχ.smul (hu j)
  have hv0 : TendstoUniformlyOn v (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu0 ε hε] with j hj
    intro z hz
    simp only [dist_zero_left,v,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hχθ z).1 (norm_nonneg _)).trans_lt (by
      simpa only [one_mul,dist_zero_left] using hj z
        (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3) hz))
  have hvD : ∀ᶠ j in atTop, ∀ x y,
      ‖fderiv ℝ (v j) x-fderiv ℝ (v j) y‖ ≤
        localSchauderBound E 3 D L (K+D)*‖x-y‖^((1:ℝ)/3) := by
    filter_upwards [huD,hAD,hCR,hu1,hAδ] with j hjD hjAD hjCR hj1 hjAδ
    let AA : ℂ → E →L[ℝ] E := fun z => θ z • A j z
    have hAA : ContDiff ℝ ∞ AA := hθ.smul (hA j)
    have hAAc : HasCompactSupport AA := hθc.smul_right
    have hAAs : tsupport AA ⊆ Metric.closedBall (0:ℂ) 3 :=
      (tsupport_smul_subset_left θ (A j)).trans hθ3
    have hb := cutoff_smul_bounds hθ (hA j) hθ3 (C := 1) (D := D) (M := δ) (L := K)
      (by norm_num) hD hδ.le hK (fun z => (hχθ z).2) (fun z => (hd z).2.2) hjAδ hjAD
    have hAAv : ∀ z, ‖AA z‖ ≤ δ := by simpa only [one_mul] using hb.1
    have hAAD : ∀ z, ‖fderiv ℝ AA z‖ ≤ K+D := by
      intro z
      exact (hb.2 z).trans (by nlinarith)
    apply cutoff_smallCR_schauder 3 χ hχ hχc hχ3 AA hAA hAAc hAAs (u j) (hu j)
      hD hL (add_nonneg hK hD) hδ.le hδ1 (fun z => (hd z).1)
      (fun z => (hd z).2.1) (fun z hz => hj1 z (hχ3 hz)) (fun z hz => hjD z (hχ3 hz))
      hAAv hAAD
    · intro z hz
      rw [show AA z=A j z by simp only [AA,hθ1 z hz,one_smul]]
      exact hjCR z (hχ3 hz)
    · dsimp [B] at hsmall
      nlinarith only [hsmall]
  have hC : 0 ≤ localSchauderBound E 3 D L (K+D) := by
    dsimp [localSchauderBound]
    positivity
  have hlim := norm_fderiv_tendsto_zero_of_holder (fun j => (hv j).differentiable (by simp))
    hC (by norm_num : (0:ℝ) < 1/3) hvD hv0
  convert hlim using 1
  funext j
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hχ1] with z hz
  simp only [v,hz,one_smul]

end

 

 

 

open scoped Topology
open Set Filter Function
section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem locally_uniform_comp_uniform_constant
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℕ → E → F} {v : E → F}
    (hv : TendstoLocallyUniformly f v atTop) {x : E} (hvc : ContinuousAt v x)
    {g : ℕ → G → E} {K : Set G}
    (hg : TendstoUniformlyOn g (fun _ => x) atTop K) :
    TendstoUniformlyOn (fun j z => f j (g j z)) (fun _ => v x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := show {p : F × F | dist p.1 p.2 < ε/2} ∈ uniformity F from
    Metric.dist_mem_uniformity (by linarith)
  obtain ⟨U,hU,hUf⟩ := hv _ he x
  obtain ⟨V,hV,hVc⟩ := Metric.continuousAt_iff.mp hvc (ε/2) (by linarith)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hmin : 0 < min δ V := lt_min hδ hV
  filter_upwards [hUf,Metric.tendstoUniformlyOn_iff.mp hg (min δ V) hmin] with j hj hjg
  intro z hz
  have hgdist : dist (g j z) x < min δ V := by simpa [dist_comm] using hjg z hz
  have hmem : g j z ∈ U := hδU (hgdist.trans_le (min_le_left _ _))
  have h1 := hj (g j z) hmem
  have h2 := hVc (lt_of_lt_of_le hgdist (min_le_right _ _))
  have ht := dist_triangle (v x) (v (g j z)) (f j (g j z))
  rw [dist_comm (v x) (v (g j z))] at ht
  linarith

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem continuousAt_comp_uniform_constant
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → F} {x : E}
    (hg : ContinuousAt g x) {u : ℕ → G → E} {K : Set G}
    (hu : TendstoUniformlyOn u (fun _ => x) atTop K) :
    TendstoUniformlyOn (fun j z => g (u j z)) (fun _ => g x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with j hj
  intro z hz
  rw [dist_comm]
  exact hb (by simpa [dist_comm] using hj z hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem uniform_constant_prod
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {x : ℕ → E} {p : E} (hx : Tendsto x atTop (𝓝 p))
    {u : ℕ → G → F} {q : F} {K : Set G}
    (hu : TendstoUniformlyOn u (fun _ => q) atTop K) :
    TendstoUniformlyOn (fun j z => (x j,u j z)) (fun _ => (p,q)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hx ε hε,Metric.tendstoUniformlyOn_iff.mp hu ε hε] with j hj hju
  intro z hz
  rw [Prod.dist_eq]
  exact max_lt (by simpa [dist_comm] using hj) (hju z hz)

theorem affine_rescale_uniform_constant {x : ℕ → E} {c : E}
    (hx : Tendsto x atTop (𝓝 c)) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    {K : Set E} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun j z => x j+r j • z) (fun _ => c) atTop K := by
  obtain ⟨M,hM,hMb⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ j in atTop, dist (x j) c+|r j| * M < ε := by
    have ht : Tendsto (fun j => dist (x j) c+|r j| * M) atTop (𝓝 0) := by
      simpa using (hx.dist (tendsto_const_nhds (x := c))).add (hr.abs.mul_const M)
    exact ht.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with j hj
  intro z hz
  rw [dist_comm,dist_eq_norm]
  have he : x j+r j • z-c=(x j-c)+r j • z := by abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul,Real.norm_eq_abs]
  apply lt_of_le_of_lt _ hj
  rw [dist_eq_norm]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb z hz) (abs_nonneg _))

theorem rescaled_maps_uniform_constant {f : ℕ → E → F} {v : E → F}
    (hv : TendstoLocallyUniformly f v atTop) {x : ℕ → E} {c : E}
    (hvc : ContinuousAt v c) (hx : Tendsto x atTop (𝓝 c))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {K : Set E} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun j z => f j (x j+r j • z)) (fun _ => v c) atTop K :=
  locally_uniform_comp_uniform_constant hv hvc (affine_rescale_uniform_constant hx hr hK)

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity

def frameConjugation {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) : End n →L[ℝ] End n :=
  (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n) S.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)).flip S.symm.toContinuousLinearMap)

@[simp] theorem frameConjugation_apply {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (B : End n) :
    frameConjugation S B=S.toContinuousLinearMap.comp (B.comp S.symm.toContinuousLinearMap) := rfl

theorem frozenCoefficient_fderiv {n : ℕ} (S : Phase n ≃L[ℝ] Phase n) (J : End n)
    {B : ℂ → End n} (hB : Differentiable ℝ B) (z : ℂ) :
    fderiv ℝ (frozenCoefficient S J B) z=(frameConjugation S).comp (fderiv ℝ B z) :=
  ((frameConjugation S).hasFDerivAt.comp z ((hB z).hasFDerivAt.sub_const J)).fderiv

theorem frozen_CR_no_gradient_loss {n : ℕ}
    (u : ℕ → ℂ → Phase n) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (B : ℕ → ℂ → End n) (hB : ∀ j, ContDiff ℝ ∞ (B j))
    (p : Phase n) (J : End n) (hJ : Compatible J)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (B j) z‖ ≤ K)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=B j z (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3))
    (hB0 : TendstoUniformlyOn B (fun _ => J) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  obtain ⟨S,hS⟩ := compatible_standard_frame hJ
  let U : ℕ → ℂ → Phase n := fun j => centeredFrame S p (u j)
  let A : ℕ → ℂ → End n := fun j => frozenCoefficient S J (B j)
  have hU : ∀ j, ContDiff ℝ ∞ (U j) := fun j => centeredFrame_smooth S p (hu j)
  have hA : ∀ j, ContDiff ℝ ∞ (A j) := fun j => frozenCoefficient_smooth S J (hB j)
  have hUD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (U j) z‖ ≤ ‖S.toContinuousLinearMap‖*L := by
    filter_upwards [huD] with j hj
    intro z hz
    rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (u j) z) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) z]
    exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hAD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (A j) z‖ ≤ ‖frameConjugation S‖*K := by
    filter_upwards [hBD] with j hj
    intro z hz
    rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
      frozenCoefficient_fderiv S J ((hB j).differentiable (by simp)) z]
    exact ((frameConjugation S).opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hACR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hCR] with j hj
    intro z hz
    exact frozen_CR_equation S J hS p ((hu j).differentiable (by simp)) (B j) (hj z hz)
  have hU0 : TendstoUniformlyOn U (fun _ => (0:Phase n)) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : Phase n => S (x-p)) p :=
      S.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hu0 using 1
    all_goals try simp only [U,sub_self,map_zero]
    all_goals rfl
  have hA0 : TendstoUniformlyOn A (fun _ => (0:End n)) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : End n => frameConjugation S (x-J)) J :=
      (frameConjugation S).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hB0 using 1
    all_goals try simp only [A,frameConjugation_apply,sub_self,map_zero]
    all_goals rfl
  have hlim := smallCR_sequence_derivative_zero U hU A hA
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) hK) hUD hAD hACR hU0 hA0
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => show ‖fderiv ℝ (u j) 0‖ ≤ ‖S.symm.toContinuousLinearMap‖*‖fderiv ℝ (U j) 0‖ from ?_)
    (by simpa using hlim.const_mul ‖S.symm.toContinuousLinearMap‖)
  have he : fderiv ℝ (u j) 0=S.symm.toContinuousLinearMap.comp (fderiv ℝ (U j) 0) := by
    rw [show fderiv ℝ (U j) 0=S.toContinuousLinearMap.comp (fderiv ℝ (u j) 0) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) 0]
    apply ContinuousLinearMap.ext
    intro z
    change (fderiv ℝ (u j) 0) z=S.symm (S ((fderiv ℝ (u j) 0) z))
    simp
  rw [he]
  exact S.symm.toContinuousLinearMap.opNorm_comp_le _

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity

theorem lineHomotopy_contDiffAt {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    {y : ℝ × Phase n} (hy : y.1 ∈ Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) y :=
  contDiffAt_interpolateJ (hJs.contDiffAt.comp y contDiffAt_snd)
    contDiffAt_fst (hJ y.2) hy

theorem homotopy_CR_no_gradient_loss {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → Phase n) (hu : ∀ j, ContDiff ℝ ∞ (u j)) (p : Phase n)
    {L : ℝ} (hL : 0 ≤ L)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=lineHomotopy J (t j) (u j z) (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  let H : ℝ × Phase n → End n := fun y => lineHomotopy J y.1 y.2
  let B : ℕ → ℂ → End n := fun j z => H (t j,u j z)
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hH (y : ℝ × Phase n) (hy : y.1 ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ H y :=
    lineHomotopy_contDiffAt hJs hJ hy
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,u j z)) z
      (hH (t j,u j z) (ht j)) (contDiffAt_const.prodMk (hu j).contDiffAt)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall p 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  have hB0 : TendstoUniformlyOn B (fun _ => H (s,p)) atTop (Metric.closedBall (0:ℂ) 3) := by
    convert continuousAt_comp_uniform_constant (hH (s,p) hs).continuousAt
      (uniform_constant_prod hts hu0) using 1
  have hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (B j) z‖ ≤ K*L := by
    filter_upwards [huD,Metric.tendstoUniformlyOn_iff.mp hu0 1 (by norm_num)] with j hj hju
    intro z hz
    have hmem : (t j,u j z) ∈ Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1 :=
      ⟨ht j,by simpa [Metric.mem_closedBall,dist_comm] using (hju z hz).le⟩
    have hd : HasFDerivAt (fun z => (t j,u j z))
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) z :=
      (hasFDerivAt_const (t j) z).prodMk ((hu j).differentiable (by simp) z).hasFDerivAt
    have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,u j z)).comp
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) :=
      (HasFDerivAt.comp (g := H) (f := fun z => (t j,u j z)) z
        ((hH (t j,u j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
    rw [he]
    apply ((fderiv ℝ H (t j,u j z)).opNorm_comp_le _).trans
    have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)‖=‖fderiv ℝ (u j) z‖ := by
      rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    rw [hnorm]
    exact mul_le_mul (hKb _ ⟨(t j,u j z),hmem,rfl⟩) (hj z hz) (norm_nonneg _) hK.le
  exact frozen_CR_no_gradient_loss u hu B hB p (H (s,p))
    (lineHomotopy_compatible hJ hs p) hL (mul_nonneg hK.le hL) huD hBD hCR hu0 hB0

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescaleMap (u : ℂ → F) (x : ℂ) (r : ℝ) : ℂ → F := fun z => u (x+r • z)

theorem rescaleMap_smooth {u : ℂ → F} (hu : ContDiff ℝ ∞ u) (x : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (rescaleMap u x r) := by
  exact ContDiff.comp (g := u) (f := fun z : ℂ => x+r • z) hu
    (contDiff_const.add (contDiff_id.const_smul r))

theorem rescaleMap_fderiv {u : ℂ → F} (hu : Differentiable ℝ u) (x : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaleMap u x r) z=r • fderiv ℝ u (x+r • z) := by
  have hd : HasFDerivAt (fun z : ℂ => x+r • z) (r • ContinuousLinearMap.id ℝ ℂ) z :=
    by
      have hh := (hasFDerivAt_const (𝕜 := ℝ) x z).add ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul r)
      simp only [zero_add] at hh
      convert hh using 1
      rfl
  have he := (HasFDerivAt.comp (g := u) (f := fun z : ℂ => x+r • z) z
    (hu (x+r • z)).hasFDerivAt hd).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id] at he
  convert he using 1
  rfl

theorem rescaleMap_norm_fderiv {u : ℂ → F} (hu : Differentiable ℝ u)
    (x : ℂ) (r : ℝ) (z : ℂ) :
    ‖fderiv ℝ (rescaleMap u x r) z‖=|r| * ‖fderiv ℝ u (x+r • z)‖ := by
  rw [rescaleMap_fderiv hu,norm_smul,Real.norm_eq_abs]

theorem weighted_rescale_bounds {u : ℂ → F} (hu : Differentiable ℝ u)
    {x c : ℂ} {R : ℝ} (hg : 0 < ‖fderiv ℝ u x‖)
    (hm : 6 ≤ (R-dist x c)*‖fderiv ℝ u x‖)
    (hb : ∀ y ∈ Metric.closedBall x ((R-dist x c)/2),
      ‖fderiv ℝ u y‖ ≤ 2*‖fderiv ℝ u x‖) :
    ‖fderiv ℝ (rescaleMap u x ‖fderiv ℝ u x‖⁻¹) 0‖=1 ∧
      ∀ z ∈ Metric.closedBall (0:ℂ) 3,
        ‖fderiv ℝ (rescaleMap u x ‖fderiv ℝ u x‖⁻¹) z‖ ≤ 2 := by
  have hr : 0 ≤ ‖fderiv ℝ u x‖⁻¹ := inv_nonneg.mpr hg.le
  constructor
  · rw [rescaleMap_norm_fderiv hu,abs_of_nonneg hr,smul_zero,add_zero,inv_mul_cancel₀ hg.ne']
  · intro z hz
    have hhalf : ‖fderiv ℝ u x‖⁻¹*3 ≤ (R-dist x c)/2 := by
      have hh := mul_le_mul_of_nonneg_right hm hr
      rw [mul_assoc,mul_inv_cancel₀ hg.ne',mul_one] at hh
      linarith
    have hmem : x+‖fderiv ℝ u x‖⁻¹ • z ∈ Metric.closedBall x ((R-dist x c)/2) := by
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hr]
      exact (mul_le_mul_of_nonneg_left (by simpa using hz : ‖z‖ ≤ 3) hr).trans hhalf
    rw [rescaleMap_norm_fderiv hu,abs_of_nonneg hr]
    calc
      _ ≤ ‖fderiv ℝ u x‖⁻¹*(2*‖fderiv ℝ u x‖) := mul_le_mul_of_nonneg_left (hb _ hmem) hr
      _ = 2 := by rw [mul_left_comm,inv_mul_cancel₀ hg.ne',mul_one]

theorem rescaleMap_CR {n : ℕ} {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : Differentiable ℝ u) (hCR : ∀ z, PseudoHolomorphicAt J u z)
    (x : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaleMap u x r) z Complex.I=
      J (rescaleMap u x r z) (fderiv ℝ (rescaleMap u x r) z 1) := by
  rw [rescaleMap_fderiv hu]
  simpa only [smul_apply,map_smul,mul_one,rescaleMap] using
    congrArg (fun v : Phase n => r • v) ((hCR (x+r • z)).2 1)

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weighted_gradient_maximum (f : ℂ → F) (hf : ContDiff ℝ ∞ f)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (hgrad : 0 < ‖fderiv ℝ f c‖) :
    ∃ x ∈ Metric.ball c R,
      R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ ∧
      ‖fderiv ℝ f c‖ ≤ ‖fderiv ℝ f x‖ ∧
      ∀ y ∈ Metric.closedBall x ((R-dist x c)/2),
        ‖fderiv ℝ f y‖ ≤ 2*‖fderiv ℝ f x‖ := by
  let g : ℂ → ℝ := fun z => (R-dist z c)*‖fderiv ℝ f z‖
  have hg : Continuous g :=
    (continuous_const.sub (continuous_id.dist continuous_const)).mul
      ((hf.continuous_fderiv (by simp)).norm)
  obtain ⟨x,hx,hxm⟩ := (isCompact_closedBall c R).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hR.le) hg.continuousOn
  have hcm : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hR.le
  have hcx : R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ := by
    simpa only [Set.mem_ofPred_eq,g,dist_self,sub_zero] using hxm hcm
  have hxp : 0 < R-dist x c := by
    have hm : 0 < (R-dist x c)*‖fderiv ℝ f x‖ := (mul_pos hR hgrad).trans_le hcx
    exact pos_of_mul_pos_left hm (norm_nonneg _)
  have hxmem : x ∈ Metric.ball c R := by
    rw [Metric.mem_ball]
    linarith
  have hgx : ‖fderiv ℝ f c‖ ≤ ‖fderiv ℝ f x‖ := by
    apply le_of_mul_le_mul_left (a := R)
    · calc
        R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ := hcx
        _ ≤ R*‖fderiv ℝ f x‖ := mul_le_mul_of_nonneg_right (by linarith [dist_nonneg (x := x) (y := c)]) (norm_nonneg _)
    · exact hR
  refine ⟨x,hxmem,hcx,hgx,?_⟩
  intro y hy
  have hyx : dist y x ≤ (R-dist x c)/2 := Metric.mem_closedBall.mp hy
  have hyc : dist y c ≤ (R+dist x c)/2 := by
    have hh := dist_triangle y x c
    linarith
  have hymem : y ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall]
    linarith
  have hxy := hxm hymem
  change (R-dist y c)*‖fderiv ℝ f y‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ at hxy
  have hb : ((R-dist x c)/2)*‖fderiv ℝ f y‖ ≤
      (R-dist y c)*‖fderiv ℝ f y‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hh := hb.trans hxy
  nlinarith

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

theorem locally_uniform_reindex {E F : Type*} [TopologicalSpace E] [UniformSpace F]
    {u : ℕ → E → F} {v : E → F} (hv : TendstoLocallyUniformly u v atTop)
    {a : ℕ → ℕ} (ha : Tendsto a atTop atTop) :
    TendstoLocallyUniformly (fun j => u (a j)) v atTop := by
  intro V hV x
  obtain ⟨U,hU,hUV⟩ := hv V hV x
  exact ⟨U,hU,ha.eventually hUV⟩

theorem homotopy_C0_gradient_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → Phase n) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, PseudoHolomorphicAt (lineHomotopy J (t j)) (u j) z)
    (v : ℂ → Phase n) (hv : TendstoLocallyUniformly u v atTop)
    (c : ℂ) {R : ℝ} (_hR : 0 ≤ R) :
    ∃ L ≥ 0, ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall c R, ‖fderiv ℝ (u j) z‖ ≤ L := by
  by_contra hn
  have hbad (j : ℕ) : ∃ i ≥ j, ∃ z ∈ Metric.closedBall c R,
      (j:ℝ)+1 < ‖fderiv ℝ (u i) z‖ := by
    have hnot : ¬ ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall c R,
        ‖fderiv ℝ (u i) z‖ ≤ (j:ℝ)+1 := by
      intro hh
      exact hn ⟨(j:ℝ)+1,by positivity,hh⟩
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    obtain ⟨i,hi,z,hz,hbig⟩ := hnot j
    exact ⟨i,hi,z,hz,hbig⟩
  choose a ha z hz hbig using hbad
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  have hpos (j : ℕ) : 0 < ‖fderiv ℝ (u (a j)) (z j)‖ := lt_trans (by positivity) (hbig j)
  choose x hx hweight hlarger hlocal using
    (fun j => weighted_gradient_maximum (u (a j)) (hu (a j)) (z j) (by norm_num : (0:ℝ)<1) (hpos j))
  have hxmem (j : ℕ) : x j ∈ Metric.closedBall c (R+1) := by
    have h1 : dist (x j) (z j) < 1 := hx j
    have h2 : dist (z j) c ≤ R := hz j
    rw [Metric.mem_closedBall]
    linarith [dist_triangle (x j) (z j) c]
  obtain ⟨d,hd,φ,hφ,hφx⟩ := (isCompact_closedBall c (R+1)).tendsto_subseq hxmem
  let b : ℕ → ℕ := fun j => a (φ j)
  have hbt : Tendsto b atTop atTop := hat.comp hφ.tendsto_atTop
  let g : ℕ → ℝ := fun j => ‖fderiv ℝ (u (b j)) (x (φ j))‖
  have hgp (j : ℕ) : 0 < g j := (hpos (φ j)).trans_le (hlarger (φ j))
  have hgb (j : ℕ) : (φ j:ℝ)+1 < g j := (hbig (φ j)).trans_le (hlarger (φ j))
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (fun j => (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (hgb j).le)
    exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  let r : ℕ → ℝ := fun j => (g j)⁻¹
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hgt
  let U : ℕ → ℂ → Phase n := fun j => rescaleMap (u (b j)) (x (φ j)) (r j)
  have hUs (j : ℕ) : ContDiff ℝ ∞ (U j) := rescaleMap_smooth (hu (b j)) _ _
  have hlim : TendstoUniformlyOn U (fun _ => v d) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hv' := locally_uniform_reindex hv hbt
    have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
    convert rescaled_maps_uniform_constant hv' hvc.continuousAt hφx hrt
      (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 3)) using 1
    rfl
  have hUb : ∀ᶠ j in atTop, ‖fderiv ℝ (U j) 0‖=1 ∧
      ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (U j) z‖ ≤ 2 := by
    filter_upwards [eventually_ge_atTop (6:ℕ)] with j hj
    apply weighted_rescale_bounds ((hu (b j)).differentiable (by simp)) (hgp j)
    · have hφj : j ≤ φ j := hφ.id_le j
      have h6 : (6:ℝ) ≤ φ j := by exact_mod_cast le_trans hj hφj
      have hw := hweight (φ j)
      dsimp [g,b] at hgb
      nlinarith [hbig (φ j)]
    · exact hlocal (φ j)
  have hUCR : ∀ j z, fderiv ℝ (U j) z Complex.I=
      lineHomotopy J (t (b j)) (U j z) (fderiv ℝ (U j) z 1) := by
    intro j z
    exact rescaleMap_CR ((hu (b j)).differentiable (by simp)) (hCR (b j)) _ _ _
  have hzero := homotopy_CR_no_gradient_loss hJs hJ (fun j => t (b j))
    (fun j => ht (b j)) (hts.comp hbt) U hUs (v d) (by norm_num : (0:ℝ) ≤ 2)
    (hUb.mono (fun j hj => hj.2)) (Eventually.of_forall (fun j z _ => hUCR j z)) hlim
  have hone : Tendsto (fun j => ‖fderiv ℝ (U j) 0‖) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (hUb.mono (fun j hj => hj.1.symm))
  have he : (0:ℝ)=1 := tendsto_nhds_unique hzero hone
  norm_num at he

end HigherDimensionalBallPacking.Rigidity

end

end OAI
