import Mathlib
import OAI.Geometry.SmoothYau.Estimates.EventuallyProductScalarFactorRaw
import OAI.Geometry.SmoothYau.Estimates.ExistsSphericalScalarProducer
import OAI.Geometry.SmoothYau.SphereMetric.ThreeExceptional

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeLiftNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeLiftContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul

def threeWaveLift (u : NormalWaveSpace → ℝ) : ThreeManifold → ℝ :=
  manifoldChartPush threeProfileCenter (u ∘ threeNormalEquiv.symm)
lemma threeWaveLift_apply (u : NormalWaveSpace → ℝ) (y : NormalWaveSpace) :
    threeWaveLift u (threeNormalInv y)=u y := by
  dsimp [threeWaveLift,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
lemma threeWaveLift_smooth {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeWaveLift u) :=
  contMDiff_manifoldChartPush _ (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
lemma threeWaveLift_tsupport {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {K : Set NormalWaveSpace} (hs : tsupport u⊆K) :
    tsupport (threeWaveLift u)⊆threeNormalInv '' K := by
  have he : threeWaveLift u=(fun p => threeNormalGlue 0 u p-0) := by
    funext p; simp [threeWaveLift,threeNormalGlue]
  rw [he]
  exact threeNormalGlue_tsupport 0 (by simpa using hc) (by simpa using hs)
lemma threeWaveLift_laplacian (g : SmoothMetric ThreeModel ThreeManifold)
    {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (y : NormalWaveSpace) :
    laplaceBeltrami g (threeWaveLift u) (threeNormalInv y)=laplaceBeltrami (threeNormalMetricOf g) u y := by
  have he : (u ∘ threeNormalEquiv.symm) ∘ threeNormalEquiv=u := by funext z; simp
  have ht := linearPullbackMetric_laplace (threeChartMetric g threeProfileCenter) threeNormalEquiv
    (hu.comp threeNormalEquiv.symm.contDiff) y
  rw [he] at ht
  change _ = laplaceBeltrami (linearPullbackMetric (threeChartMetric g threeProfileCenter) threeNormalEquiv) u y
  rw [ht]
  apply laplaceBeltrami_manifoldChartPush g (threeChartMetric g threeProfileCenter) threeProfileCenter
    (by rw [three_chart_target]; trivial) (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
  filter_upwards [] with z v w
  rw [←selfMetricFlat_apply,threeChartMetric_selfFlat,chartMetricForm_pairing]
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
lemma threeNormalInv_image_source (K : Set NormalWaveSpace) :
    threeNormalInv '' K⊆(chartAt ThreeModel threeProfileCenter).source := by
  rintro p ⟨y,hy,rfl⟩
  exact (chartAt ThreeModel threeProfileCenter).map_target (by rw [three_chart_target]; trivial)

lemma linearEquiv_comp_jets_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F ≃L[ℝ] E) (m : ℕ) :
    ∃ C>0, ∀ (u : E → ℝ), ContDiff ℝ ∞ u → ∀ x : F, ∀ j  ≤  m, ∀ B : ℝ,
      0 ≤ B → ‖iteratedFDeriv ℝ j u (L x)‖ ≤ B → ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ C*B := by
  let c := max 1 ‖L.toContinuousLinearMap‖
  refine ⟨c^m, pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _,?_⟩
  intro u hu x j hj B hB hb
  change ‖iteratedFDeriv ℝ j (u ∘ L.toContinuousLinearMap) x‖ ≤ _
  rw [L.toContinuousLinearMap.iteratedFDeriv_comp_right hu x (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))]
  have hn := (iteratedFDeriv ℝ j u (L x)).norm_compContinuousLinearMap_le (fun _ : Fin j => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  have hp : ‖L.toContinuousLinearMap‖^j ≤ c^m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact hn.trans ((mul_le_mul hb hp (by positivity) hB).trans_eq (mul_comm _ _))

theorem three_wave_lift_jets (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (r : ℝ) (m : ℕ) :
    ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆closedBall 0 r →
      ∀ (B : ℕ → ThreeManifold → ℝ), (∀ j q, 0 ≤ B j q) →
      ∀ (R : ThreeManifold → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
      (∀ x : NormalWaveSpace, ∀ j  ≤  m, ∀ i  ≤  j,
        ‖iteratedFDeriv ℝ i u x‖ ≤ B j (threeNormalInv x)) →
      (∀ x : NormalWaveSpace, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+Λ*u y) x‖ ≤ R (threeNormalInv x)) →
      ∀ y∈K, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (threeWaveLift u ∘ (chartAt ThreeModel p).symm) y‖ ≤ C*B j ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤ C*R ((chartAt ThreeModel p).symm y) := by
  let L : Set ThreeManifold := threeNormalInv '' closedBall 0 r
  have hL : IsCompact L := (isCompact_closedBall _ _).image threeNormalInv_continuous
  have hLs : L⊆(chartAt ThreeModel threeProfileCenter).source := threeNormalInv_image_source _
  obtain ⟨C,hC,htransfer⟩ := compact_chart_weighted_jet_transfer threeProfileCenter p hL hLs hK
    (by rw [three_chart_target]; exact subset_univ _) m
  obtain ⟨D,hD,hlin⟩ := linearEquiv_comp_jets_bound threeNormalEquiv.symm m
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro u hu hc hs B hB R hR Λ hj hres y hy j hjm
  have hUs : tsupport (threeWaveLift u)⊆L := threeWaveLift_tsupport hc hs
  have he (z : ThreeModel) : threeNormalInv (threeNormalEquiv.symm z)=(chartAt ThreeModel threeProfileCenter).symm z := by
    simp [threeNormalInv]
  have hUe (z : ThreeModel) : threeWaveLift u ((chartAt ThreeModel threeProfileCenter).symm z)=(u ∘ threeNormalEquiv.symm) z := by
    rw [←he,threeWaveLift_apply]; rfl
  have hUj (q : ThreeManifold) (hq : q∈L) (j : ℕ) (hjm : j ≤ m) (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i (u ∘ threeNormalEquiv.symm) (chartAt ThreeModel threeProfileCenter q)‖  ≤  D*B j q := by
    apply hlin u hu _ i (hij.trans hjm) _ (hB _ _)
    have hh := hj (threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter q)) j hjm i hij
    simpa only [he,(chartAt ThreeModel threeProfileCenter).left_inv (hLs hq)] using hh
  have hRf : ContDiff ℝ ∞ (fun x => laplaceBeltrami (threeNormalMetricOf g) u x+Λ*u x) := by
    rw [←contMDiff_iff_contDiff]
    exact (contMDiff_laplaceBeltrami (contMDiff_iff_contDiff.mpr hu) _).add
      (contMDiff_const.mul (contMDiff_iff_contDiff.mpr hu))
  constructor
  · simpa only [mul_assoc] using htransfer _ _ (hu.comp threeNormalEquiv.symm.contDiff) hUs
      (fun z _ => hUe z) (fun j q => D*B j q) (fun j q => mul_nonneg hD.le (hB j q)) hUj y hy j hjm
  · have hRs : tsupport (fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q)⊆L :=
      (laplaceResidual_tsupport g _ Λ).trans hUs
    have hh := htransfer (fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q)
      ((fun x => laplaceBeltrami (threeNormalMetricOf g) u x+Λ*u x) ∘ threeNormalEquiv.symm)
      (hRf.comp threeNormalEquiv.symm.contDiff) hRs (fun z _ => by
        rw [←he z,threeWaveLift_laplacian g hu hc,threeWaveLift_apply]; rfl)
      (fun _ q => D*R q) (fun _ q => mul_nonneg hD.le (hR q))
      (fun q hq j hjm i hij => by
        apply hlin _ hRf _ i (hij.trans hjm) _ (hR q)
        have hh := hres (threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter q)) i (hij.trans hjm)
        simpa only [he,(chartAt ThreeModel threeProfileCenter).left_inv (hLs hq)] using hh) y hy j hjm
    simpa only [mul_assoc] using hh
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeGlobalResidualNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeGlobalResidualContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_pullback_smooth {f : ThreeManifold → ℝ}
    (hf : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ f) (p : ThreeManifold) :
    ContDiff ℝ ∞ (f ∘ (chartAt ThreeModel p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hf p (by rw [three_chart_target]; trivial)
lemma threeCoupled_residual_tsupport (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} (hF : IsClosed F)
    (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w)
    (k : ℕ) (hk : 2 ≤ k) :
    tsupport (fun p => laplaceBeltrami g (threeCoupled threeCouplingRadius k) p+
      productFrequency k*threeCoupled threeCouplingRadius k p)⊆F := by
  apply closure_minimal _ hF
  intro p hp
  by_contra hnot
  have hagree : ∀ᶠ z in 𝓝 p, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) z,
      g.inner z v w=threeBackgroundMetric.inner z v w := by
    filter_upwards [hF.isOpen_compl.mem_nhds hnot] with z hz
    exact hext z hz
  have hl := laplaceBeltrami_metric_congr_nhds g threeBackgroundMetric
    (threeCoupled threeCouplingRadius k) hagree
  have he := threeCoupled_eigen threeCouplingRadius k hk p
  exact hp (by dsimp only; linarith)

theorem threeCoupled_global_residual_rapid_decay
    (g : SmoothMetric ThreeModel ThreeManifold) {F : Set ThreeManifold} (hF : IsClosed F)
    (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w)
    {φ : ThreeManifold → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ p∈F, threeGlobalLog p+δ ≤ φ p)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k≥N, ∀ y∈K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
        productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) y‖ ≤
          ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm y)) := by
  let J := K ∩ (chartAt ThreeModel p).symm ⁻¹' F
  have hc := three_chart_symm_continuous p
  have hJ : IsCompact J := hK.inter_right (hF.preimage hc)
  obtain ⟨N,hN,hr⟩ := threeCoupled_dominated_residual_rapid_decay g hφ p hJ h P hδ
    (fun y hy => hgap _ hy.2)
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro k hk y hy j hj
  by_cases hyF : (chartAt ThreeModel p).symm y∈F
  · exact hr k ((le_max_left _ _).trans hk) y ⟨hy,hyF⟩ j hj
  · let R : ThreeManifold → ℝ := fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
      productFrequency k*threeCoupled threeCouplingRadius k z
    have hs : tsupport R⊆F := threeCoupled_residual_tsupport g hF hext k ((le_max_right _ _).trans hk)
    have hz : R ∘ (chartAt ThreeModel p).symm =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(hc.tendsto y).eventually (hF.isOpen_compl.mem_nhds hyF)] with z hz
      by_contra hm
      exact hz (hs (subset_closure hm))
    have hj0 := (hz.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j (R ∘ (chartAt ThreeModel p).symm) y‖ ≤ _
    rw [hj0]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero]; positivity
    | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity
lemma threeWeight_ge_exp (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) :
    Real.exp (productWaveFrequency k*φ p) ≤ threeWeight φ k p :=
  le_add_of_nonneg_right (pow_nonneg (threeGlobalRadius_pos p).le _)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeAssemblyNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeAssemblyContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul

theorem three_wave_background_chart_bounds
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set (ThreeManifold)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    {φ : ThreeManifold → ℝ} (hφ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ φ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ q∈F, threeGlobalLog q+δ ≤ φ q)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K)
    (r : ℝ) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
          productFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*threeWeight φ n ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
          productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*threeWeight φ n ((chartAt ThreeModel p).symm y) := by
  obtain ⟨C₁,hC₁,hback⟩ := threeCoupled_weighted_chart_jets hφ.continuous p hK m
  obtain ⟨N,hN,hres⟩ := threeCoupled_global_residual_rapid_decay g hF hext hφ.continuous hδ hgap p hK m D
  obtain ⟨T,hT,htransfer⟩ := three_wave_lift_jets g p hK r m
  let C := C₁+1+T*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast ((le_max_right N 1).trans hn)
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hnD : 0 < (n:ℝ)^D := pow_pos hn0 _
  have hn4 : (1:ℝ)≤(n:ℝ)^4 := one_le_pow₀ hn1
  intro u hu hc hs hj y hy j hjm
  let W := threeWeight φ n ((chartAt ThreeModel p).symm y)
  have hW : 0 < W := threeWeight_pos φ n _
  have hE := threeWeight_ge_exp φ n ((chartAt ThreeModel p).symm y)
  let B := fun j q => C₀*(n:ℝ)^(j+4)*Real.exp (productWaveFrequency n*φ q)
  let R := fun q => C₀*((n:ℝ)^(D+1))⁻¹*Real.exp (productWaveFrequency n*φ q)
  have hlift := htransfer u hu hc hs B (fun j q => by dsimp [B]; positivity)
    R (fun q => by dsimp [R]; positivity) (productFrequency n)
    (fun x j hjm i hij => (hj x i (hij.trans hjm)).1.trans (by
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega : i+4≤j+4)) hC₀.le)
        (Real.exp_pos _).le))
    (fun x j hjm => (hj x j hjm).2) y hy j hjm
  have hback' := hback n (by exact_mod_cast hn1) y hy j hjm
  have hres' := hres n ((le_max_left _ _).trans hn) y hy j hjm
  have hsmooth := threeWaveLift_smooth hu hc
  have hsum : ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
      (chartAt ThreeModel p).symm)=
      (threeCoupled threeCouplingRadius n ∘ (chartAt ThreeModel p).symm)+
      (threeWaveLift u ∘ (chartAt ThreeModel p).symm) := rfl
  have hroundsm := threeCoupled_smooth threeCouplingRadius n
  constructor
  · rw [hsum]
    apply (real_smooth_add_jet_bound (three_chart_pullback_smooth hroundsm p)
      (three_chart_pullback_smooth hsmooth p) j y).trans
    apply (add_le_add hback' hlift.1).trans
    have hnj : (n:ℝ)^j ≤ (n:ℝ)^(j+4) := pow_le_pow_right₀ hn1 (by omega)
    calc
      _ ≤ C₁*(n:ℝ)^(j+4)*W+T*(C₀*(n:ℝ)^(j+4)*W) :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnj hC₁.le) hW.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hT.le)
      _ ≤ C*(n:ℝ)^(j+4)*W := by dsimp [C]; nlinarith [mul_nonneg (pow_nonneg hn0.le (j+4)) hW.le]
  · let R₁ := fun q => laplaceBeltrami g (threeCoupled threeCouplingRadius n) q+
      productFrequency n*threeCoupled threeCouplingRadius n q
    let R₂ := fun q => laplaceBeltrami g (threeWaveLift u) q+
      productFrequency n*threeWaveLift u q
    have hR₁ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ R₁ :=
      (contMDiff_laplaceBeltrami hroundsm g).add (contMDiff_const.mul hroundsm)
    have hR₂ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ R₂ :=
      (contMDiff_laplaceBeltrami hsmooth g).add (contMDiff_const.mul hsmooth)
    have he : ((fun q => laplaceBeltrami g
        (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
        productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
        (chartAt ThreeModel p).symm)=
        (R₁ ∘ (chartAt ThreeModel p).symm)+(R₂ ∘ (chartAt ThreeModel p).symm) := by
      funext x
      have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
        le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
      have hadd := laplaceBeltrami_add (hroundsm.of_le h2) (hsmooth.of_le h2) g
        ((chartAt ThreeModel p).symm x)
      dsimp only [Function.comp_apply,Pi.add_apply,R₁,R₂]
      change laplaceBeltrami g (fun y => threeCoupled threeCouplingRadius n y+threeWaveLift u y)
        ((chartAt ThreeModel p).symm x) + _ = _
      rw [hadd]
      ring
    rw [he]
    apply (real_smooth_add_jet_bound (three_chart_pullback_smooth hR₁ p)
      (three_chart_pullback_smooth hR₂ p) j y).trans
    apply (add_le_add hres' hlift.2).trans
    have hinv : ((n:ℝ)^(D+1))⁻¹ ≤ ((n:ℝ)^D)⁻¹ :=
      inv_anti₀ hnD (pow_le_pow_right₀ hn1 (by omega))
    calc
      _ ≤ ((n:ℝ)^D)⁻¹*W+T*(C₀*((n:ℝ)^D)⁻¹*W) :=
        add_le_add (mul_le_mul_of_nonneg_left hE (by positivity))
          (mul_le_mul_of_nonneg_left (mul_le_mul
            (mul_le_mul_of_nonneg_left hinv hC₀.le) hE
            (Real.exp_pos _).le (by positivity)) hT.le)
      _ = (1+T*C₀)/(n:ℝ)^D*W := by rw [div_eq_mul_inv]; ring
      _ ≤ C*(n:ℝ)^4/(n:ℝ)^D*W := by
        apply mul_le_mul_of_nonneg_right _ hW.le
        apply div_le_div_of_nonneg_right _ hnD.le
        calc
          1+T*C₀ ≤ C := by dsimp [C]; linarith
          _ ≤ C*(n:ℝ)^4 := le_mul_of_one_le_right (by dsimp [C]; positivity) hn4

end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeCenteredWaveNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeCenteredWaveContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_centered_gradient_norm (p : ThreeManifold) (U : ThreeManifold → ℝ) :
    Real.sqrt (coordinateGradientPair threeBackgroundMetric U U p)=
      ‖fderiv ℝ (U ∘ (chartAt ThreeModel p).symm) 0‖ := by
  rw [coordinateGradientPair,three_chart_center,three_metricCoefficients_zero,
    inverse_gram_differential_norm,Real.sqrt_sq (norm_nonneg _)]
lemma three_centered_gradient_norm_of_agree (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) (U : ThreeManifold → ℝ)
    (hg : ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w) :
    Real.sqrt (coordinateGradientPair g U U p)=
      ‖fderiv ℝ (U ∘ (chartAt ThreeModel p).symm) 0‖ := by
  have he : coordinateGradientPair g U U p=coordinateGradientPair threeBackgroundMetric U U p := by
    have hm : metricCoefficients g p (chartAt ThreeModel p p)=
        metricCoefficients threeBackgroundMetric p (chartAt ThreeModel p p) := by
      ext i j
      dsimp [metricCoefficients]
      rw [(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)]
      exact hg _ _
    simp only [coordinateGradientPair,hm]
  rw [he,three_centered_gradient_norm]

lemma three_wave_centered_first_jet (r : ℝ) (C₀ : ℝ) (hC₀ : 0<C₀) :
    ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆closedBall 0 r → ∀ (φ : ThreeManifold → ℝ) (k : ℕ), 1 ≤ k →
      (∀ y : NormalWaveSpace, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
          Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
      ∀ p : ThreeManifold, |threeWaveLift u p|+
        ‖fderiv ℝ (threeWaveLift u ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) ≤
          C*(k:ℝ)^4*Real.exp (productWaveFrequency k*φ p) := by
  let K := threeNormalEquiv '' closedBall 0 r
  have hK : IsCompact K := (isCompact_closedBall _ _).image threeNormalEquiv.continuous
  obtain ⟨C₁,hC₁,hgrad⟩ := compact_chart_intrinsic_gradient_bound threeBackgroundMetric threeProfileCenter hK
    (by rw [three_chart_target]; exact subset_univ _)
  obtain ⟨D,hD,hlin⟩ := linearEquiv_comp_jets_bound threeNormalEquiv.symm 1
  refine ⟨C₀+C₁*D*C₀,by positivity,?_⟩
  intro u hu hc hs φ k hk hj p
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hUsm := threeWaveLift_smooth hu hc
  by_cases hp : p∈threeNormalInv '' closedBall 0 r
  · obtain ⟨y,hy,rfl⟩ := hp
    have he : threeWaveLift u ∘ (chartAt ThreeModel threeProfileCenter).symm=u ∘ threeNormalEquiv.symm := by
      funext z
      have h := threeWaveLift_apply u (threeNormalEquiv.symm z)
      simpa only [threeNormalInv,Function.comp_apply,threeNormalEquiv.apply_symm_apply] using h
    have hgrad' := hgrad (threeWaveLift u) hUsm (threeNormalEquiv y) ⟨y,hy,rfl⟩
    change Real.sqrt (coordinateGradientPair threeBackgroundMetric _ _ (threeNormalInv y)) ≤ _ at hgrad'
    rw [three_centered_gradient_norm,he] at hgrad'
    have hder := hlin u hu (threeNormalEquiv y) 1 le_rfl
      (C₀*(k:ℝ)^5*Real.exp (productWaveFrequency k*φ (threeNormalInv y))) (by positivity)
      (by simpa only [threeNormalEquiv.symm_apply_apply] using hj y 1 le_rfl)
    rw [norm_iteratedFDeriv_one] at hder
    have hval := hj y 0 (by omega)
    simp only [norm_iteratedFDeriv_zero,Nat.zero_add,Real.norm_eq_abs] at hval
    rw [threeWaveLift_apply]
    calc
      _ ≤ C₀*(k:ℝ)^4*Real.exp (productWaveFrequency k*φ (threeNormalInv y))+
          C₁*(D*(C₀*(k:ℝ)^5*Real.exp (productWaveFrequency k*φ (threeNormalInv y))))/(k:ℝ) :=
        add_le_add hval (div_le_div_of_nonneg_right (hgrad'.trans (mul_le_mul_of_nonneg_left hder hC₁.le)) hk0.le)
      _ = _ := by field_simp
  · have hps : p∉tsupport (threeWaveLift u) := fun h => hp (threeWaveLift_tsupport hc hs h)
    have he : threeWaveLift u =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hps
    have hval := he.eq_of_nhds
    have ht : Tendsto (chartAt ThreeModel p).symm (𝓝 (0:ThreeModel)) (𝓝 p) := by
      have hh := (three_chart_symm_continuous p).tendsto 0
      simpa only [←three_chart_center p,(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)] using hh
    have hz : threeWaveLift u ∘ (chartAt ThreeModel p).symm =ᶠ[𝓝 (0:ThreeModel)] (fun _ => (0:ℝ)) := ht.eventually he
    rw [hval,hz.fderiv_eq]
    simp only [fderiv_fun_const]
    simp only [Pi.zero_apply,abs_zero,norm_zero,zero_div,zero_add]
    positivity
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeJetDualNorm : NormedAddCommGroup (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeJetDualSpace : NormedSpace ℝ (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeJetFormNorm : NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeJetFormSpace : NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := inferInstance
lemma three_compact_direction_metric_bound (g : SmoothMetric ThreeModel ThreeManifold)
    (r : ℝ) : ∃ C ≥ 1, ∀ y∈closedBall (0:NormalWaveSpace) r, ∀ i : Fin 3,
      chartMetricForm g threeProfileCenter (threeNormalEquiv y)
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))  ≤  C ^ 2 := by
  have hcont : Continuous (chartMetricForm g threeProfileCenter) := by
    exact continuousOn_univ.mp (by simpa only [three_chart_target] using
      (chartMetricForm_contDiffOn g threeProfileCenter).continuousOn)
  obtain ⟨T,hT⟩ := ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalEquiv.continuous).exists_bound_of_continuousOn hcont.norm.continuousOn
  let L := ‖threeNormalEquiv.toContinuousLinearMap‖
  let C := max 1 T+L^2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [le_max_left (1:ℝ) T,sq_nonneg L]
  refine ⟨C,hC,?_⟩
  intro y hy i
  let v := threeNormalEquiv (normalWaveEquiv (Pi.single i 1))
  have hv : ‖v‖ ≤ L := by
    have h := threeNormalEquiv.toContinuousLinearMap.le_opNorm (normalWaveEquiv (Pi.single i 1))
    simpa [v,L,normalWaveEquiv_single,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,mul_one] using h
  have hT' : ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖ ≤ max 1 T :=
    (by simpa only [norm_norm] using hT _ ⟨y,hy,rfl⟩ : ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖ ≤ T) |>.trans (le_max_right _ _)
  calc
    _  ≤  ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y) v v‖ := le_abs_self _
    _  ≤  ‖chartMetricForm g threeProfileCenter (threeNormalEquiv y)‖*‖v‖*‖v‖ :=
      (chartMetricForm g threeProfileCenter (threeNormalEquiv y)).le_opNorm₂ v v
    _  ≤  max 1 T*L*L := by gcongr
    _  ≤  C ^ 2 := by
      have h1 : max 1 T ≤ C := by dsimp [C]; nlinarith [sq_nonneg L]
      have h2 : L^2 ≤ C := by dsimp [C]; linarith [le_max_left (1:ℝ) T]
      nlinarith [mul_le_mul h1 h2 (sq_nonneg L) (by linarith : 0 ≤ C)]

lemma three_realWaveJet_intrinsic_upper {U : ThreeManifold → ℝ}
    (hU : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric ThreeModel ThreeManifold) {n W C : ℝ}
    (hn : 0<n) (hW : 0<W) (hC : 1 ≤ C) (x : Fin 3 → ℝ)
    (hmetric : ∀ i : Fin 3, chartMetricForm g threeProfileCenter
      (threeNormalEquiv (normalWaveEquiv x))
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1))) ≤ C ^ 2) :
    ‖realWaveJet n W ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x‖  ≤
      C*(|U (threeNormalInv (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U (threeNormalInv (normalWaveEquiv x)))/n)/W := by
  let q := threeNormalInv (normalWaveEquiv x)
  let F := U ∘ (chartAt ThreeModel threeProfileCenter).symm
  have hF : ContDiff ℝ ∞ F := three_chart_pullback_smooth hU _
  have hG : 0 ≤ coordinateGradientPair g U U q := coordinateGradientPair_nonneg g U q
  have hC0 : 0 ≤ C := by linarith
  have hder (i : Fin 3) : |fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)|  ≤
      C*Real.sqrt (coordinateGradientPair g U U q) := by
    have hd := chart_derivative_dual_bound hU g threeProfileCenter
      (show threeNormalEquiv (normalWaveEquiv x)∈(chartAt ThreeModel threeProfileCenter).target by rw [three_chart_target]; trivial)
      (threeNormalEquiv (normalWaveEquiv (Pi.single i 1)))
    have hd' := hd.trans (mul_le_mul_of_nonneg_left (hmetric i) hG)
    have he := ((hF.differentiable (by simp) _).hasFDerivAt.comp
      (normalWaveEquiv x) threeNormalEquiv.hasFDerivAt).comp x normalWaveEquiv.hasFDerivAt
    have he' := congrArg (fun T => T (Pi.single i 1)) he.fderiv
    change fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)=
      fderiv ℝ F (threeNormalEquiv (normalWaveEquiv x))
        (threeNormalEquiv (normalWaveEquiv (Pi.single i 1))) at he'
    rw [he']
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC0 (Real.sqrt_nonneg _))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hG]
    exact hd'.trans_eq (mul_comm _ _)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*U q‖  ≤  C*(|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),Real.norm_eq_abs]
    rw [mul_comm W⁻¹,←div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ hW.le
    calc
      _  ≤  |U q|+Real.sqrt (coordinateGradientPair g U U q)/n :=
        le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hn.le)
      _  ≤  _ := le_mul_of_one_le_left (by positivity) hC
  · change ‖n⁻¹*W⁻¹*fderiv ℝ ((U ∘ threeNormalInv) ∘ normalWaveEquiv) x (Pi.single i 1)‖  ≤
      C*(|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),abs_of_pos (inv_pos.mpr hn)]
    calc
      _  ≤  n⁻¹*W⁻¹*(C*Real.sqrt (coordinateGradientPair g U U q)) :=
        mul_le_mul_of_nonneg_left (hder i) (by positivity)
      _ = C*(Real.sqrt (coordinateGradientPair g U U q)/n)/W := by ring
      _  ≤  _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (abs_nonneg _)) hC0) hW.le
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma three_exceptional_intrinsic_margin (g : SmoothMetric ThreeModel ThreeManifold)
    (r : ℝ) : ∃ C ≥ 1, ∀ k : ℕ, 1 ≤ k → C ≤ productWaveFrequency k →
      ∀ φ : ThreeManifold → ℝ, threeExceptional φ k⊆threeNormalInv '' closedBall 0 r →
      ∀ U : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U →
      (∀ y∈threeExceptionalInChart φ k, 1/productWaveFrequency k^110 ≤
        ‖realWaveJet (productWaveFrequency k) (threePacketWeight φ k y)
          ((U ∘ threeNormalInv) ∘ normalWaveEquiv) y‖) →
      ∀ p∈threeExceptional φ k, threeWeight φ k p/productWaveFrequency k^111 ≤
        |U p|+Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k := by
  obtain ⟨C,hC,hmetric⟩ := three_compact_direction_metric_bound g r
  refine ⟨C,hC,?_⟩
  intro k hk hCν φ hcover U hU hjet p hp
  obtain ⟨y,hy,rfl⟩ := hcover hp
  let x := normalWaveEquiv.symm y
  have hxy : normalWaveEquiv x=y := normalWaveEquiv.apply_symm_apply y
  have hx : x∈threeExceptionalInChart φ k := (three_exceptional_chart_iff φ k x).mpr (by simpa only [hxy] using hp)
  have hν1 : 1 ≤ productWaveFrequency k := hC.trans hCν
  have hν0 : 0<productWaveFrequency k := zero_lt_one.trans_le hν1
  have hW : 0<threePacketWeight φ k x := by
    dsimp [threePacketWeight]; positivity
  have hu := three_realWaveJet_intrinsic_upper hU g hν0 hW hC x (fun i => by
    simpa only [hxy] using hmetric y hy i)
  have hh := (le_div_iff₀ hW).mp ((hjet x hx).trans hu)
  let J := |U (threeNormalInv y)|+Real.sqrt (coordinateGradientPair g U U (threeNormalInv y))/productWaveFrequency k
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hh' : threePacketWeight φ k x ≤ (C*J)*productWaveFrequency k^110 := by
    apply (div_le_iff₀ (pow_pos hν0 110)).mp
    simpa only [J,hxy,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  apply (div_le_iff₀ (pow_pos hν0 111)).mpr
  calc
    _  ≤  threePacketWeight φ k x := by simpa only [hxy] using threeWeight_le_packet φ k x
    _  ≤  (C*J)*productWaveFrequency k^110 := hh'
    _  ≤  (productWaveFrequency k*J)*productWaveFrequency k^110 := by gcongr
    _ = J*productWaveFrequency k^111 := by rw [pow_succ]; ring

lemma weighted_exterior_absorption {ν C E P J V : ℝ} (hν : 1 ≤ ν) (_hC : 0 ≤ C)
    (hE : 0 ≤ E) (_hJ : 0 ≤ J) (hV : V ≤ C*ν^4*E) (hP : ν^6*E<P)
    (hback : P ≤ 24*(J+V)) (hsmall : 48*C ≤ ν^2) : P ≤ 48*J := by
  have hs : 48*(C*ν^4*E) ≤ ν^6*E := by
    calc
      _ = (48*C)*ν^4*E := by ring
      _  ≤  ν^2*ν^4*E := by gcongr
      _ = _ := by ring
  have hh : 48*V<P := (mul_le_mul_of_nonneg_left hV (by norm_num)).trans_lt (hs.trans_lt hP)
  linarith

lemma three_exterior_intrinsic_margin (g : SmoothMetric ThreeModel ThreeManifold)
    {φ : ThreeManifold → ℝ} (r C₀ : ℝ) (hC₀ : 0<C₀) :
    ∀ᶠ k : ℕ in atTop, ∀ u : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
        Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
      ∀ p∉threeExceptional φ k,
      (∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p, g.inner p v w=threeBackgroundMetric.inner p v w) →
      let U := threeCoupled threeCouplingRadius k+threeWaveLift u
      threeWeight φ k p/productWaveFrequency k^111 ≤ |U p|+
        Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k := by
  obtain ⟨C,hC,hfirst⟩ := three_wave_centered_first_jet r C₀ hC₀
  have hf := productWaveFrequency_tendsto.eventually (eventually_ge_atTop (max 96 (48*C+1)))
  filter_upwards [hf,eventually_ge_atTop (2:ℕ)] with k hνlarge hk
  intro u hu hc hs hj p hp hagree
  dsimp only
  let ν := productWaveFrequency k
  let v := threeWaveLift u
  let w := threeCoupled threeCouplingRadius k
  let U := w+v
  let D (f : ThreeManifold → ℝ) := fderiv ℝ (f ∘ (chartAt ThreeModel p).symm) 0
  let J (f : ThreeManifold → ℝ) := |f p|+‖D f‖/ν
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hνb := productWaveFrequency_bounds hk1
  have hν96 : 96 ≤ ν := (le_max_left _ _).trans hνlarge
  have hνC : 48*C+1 ≤ ν := (le_max_right _ _).trans hνlarge
  have hν1 : 1 ≤ ν := by linarith
  have hν0 : 0<ν := by linarith
  have hvsm := threeWaveLift_smooth hu hc
  have hwsm := threeCoupled_smooth threeCouplingRadius k
  have hD : D U=D w+D v := by
    exact fderiv_add ((three_chart_pullback_smooth hwsm p).differentiable (by simp) 0)
      ((three_chart_pullback_smooth hvsm p).differentiable (by simp) 0)
  have htri : J w ≤ J U+J v := by
    have ha : |w p| ≤ |U p|+|v p| := by
      have h := norm_sub_le (U p) (v p)
      simpa only [Real.norm_eq_abs,U,Pi.add_apply,add_sub_cancel_right] using h
    have hd : ‖D w‖ ≤ ‖D U‖+‖D v‖ := by
      have he : D w=D U-D v := by rw [hD]; simp only [add_sub_cancel_right]
      rw [he]; exact norm_sub_le _ _
    dsimp [J]
    have hh := div_le_div_of_nonneg_right hd hν0.le
    rw [add_div] at hh
    linarith
  have hback₀ := threeCoupled_global_noncancellation (r:=threeCouplingRadius) (by norm_num [threeCouplingRadius])
    (by norm_num [threeCouplingRadius]) k hk p
  have hr : ‖D w‖/(k:ℝ) ≤ 2*(‖D w‖/ν) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hk0 hν0).mpr
    have hh := mul_le_mul_of_nonneg_left hνb.2 (norm_nonneg (D w))
    nlinarith
  have hback : productWeight threeCouplingRadius k p ≤ 24*(J U+J v) := by
    have h1 : productWeight threeCouplingRadius k p ≤ 24*J w := by
      change _ ≤ 24*(|w p|+‖D w‖/ν)
      change _ ≤ 12*(|w p|+‖D w‖/(k:ℝ)) at hback₀
      nlinarith [abs_nonneg (w p)]
    exact h1.trans (mul_le_mul_of_nonneg_left htri (by norm_num))
  have hfirst' := hfirst u hu hc hs φ k hk1 hj p
  have hv : J v ≤ C*ν^4*Real.exp (ν*φ p) := by
    have hd : ‖D v‖/ν ≤ ‖D v‖/(k:ℝ) := div_le_div_of_nonneg_left (norm_nonneg _) hk0 hνb.1
    have hpow := pow_le_pow_left₀ hk0.le hνb.1 4
    exact (add_le_add (le_refl |v p|) hd).trans (hfirst'.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (Real.exp_pos _).le))
  have hP : ν^6*Real.exp (ν*φ p)<productWeight threeCouplingRadius k p := lt_of_not_ge hp
  have hJ : 0 ≤ J U := by dsimp [J]; positivity
  have hsmall : 48*C ≤ ν^2 := by nlinarith
  have habs := weighted_exterior_absorption hν1 hC.le (Real.exp_pos _).le hJ hv hP hback hsmall
  have hν6 : 1 ≤ ν^6 := one_le_pow₀ hν1
  have hE : Real.exp (ν*φ p) ≤ productWeight threeCouplingRadius k p :=
    (le_mul_of_one_le_left (Real.exp_pos _).le hν6).trans hP.le
  have hW : threeWeight φ k p ≤ 96*J U := by
    have hr := (three_global_radius_weight_bound k p).1
    dsimp [threeWeight]
    linarith
  have hpow : 96 ≤ ν^111 := hν96.trans (le_self_pow₀ hν1 (by omega : 111≠0))
  rw [three_centered_gradient_norm_of_agree g p _ hagree]
  apply (div_le_iff₀ (pow_pos hν0 111)).mpr
  exact hW.trans (by dsimp [J,D,U,w,v,ν] at *; nlinarith)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
theorem exists_three_global_quasimodes :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p ≤ threeGlobalLog p-2*δ) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ (ι : Type) [Fintype ι] (p : ι → ThreeManifold) (K : ι → Set ThreeModel),
          (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ q : ThreeManifold, threeWeight Φ k q/productWaveFrequency k^111  ≤
              |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
                Real.sqrt (coordinateGradientPair g
                  (threeCoupled threeCouplingRadius k+threeWaveLift u)
                  (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k) ∧
            (∀ i, ∀ y∈K i, ∀ j  ≤  m,
              ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k+threeWaveLift u) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^(j+4)*threeWeight Φ k ((chartAt ThreeModel (p i)).symm y) ∧
              ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
                (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
                  productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^4/productWaveFrequency k^D*
                  threeWeight Φ k ((chartAt ThreeModel (p i)).symm y)) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hproduce⟩ := exists_three_chart_quasimodes_with_gaps
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR F hF hFa hext A
  obtain ⟨Φ,hΦ,hφ,δ,hδ,hin,hout,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    hproduce g hg a b ha hab hbR A
  refine ⟨Φ,hΦ,hφ,δ,hδ,hin,hout,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro ι _ p K hK m D
  obtain ⟨C₀,hC₀,hproduce⟩ := hproduce (max m 1) D
  let C₁ := C₀*2^(max m 1+4)
  have hC₁ : 0<C₁ := by dsimp [C₁]; positivity
  have hgap : ∀ q∈F, threeGlobalLog q+δ  ≤  Φ q := by
    intro q hq
    obtain ⟨y,hy,rfl⟩ := hFa hq
    exact (hin y hy).le
  have hbound (i : ι) := three_wave_background_chart_bounds g hF hext hΦ hδ hgap
    (p i) (hK i) (R/2) m D hC₁
  choose Cs hCs hb using hbound
  let C := (1+∑ i, Cs i)*2^D
  have hsum0 : 0  ≤  ∑ i, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
  have hC : 0<C := by dsimp [C]; positivity
  have hCi (i : ι) : Cs i  ≤  1+∑ j, Cs j :=
    (Finset.single_le_sum (fun j _ => (hCs j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Cc,hCc,hmargin⟩ := three_exceptional_intrinsic_margin g b
  have hfreq := productWaveFrequency_tendsto.eventually (eventually_ge_atTop Cc)
  have hcover := three_exceptional_global_coverage Φ (mul_pos (by norm_num : (0:ℝ)<2) hδ) hout
  have hcore := three_core_exceptional hδ hgap
  have hexterior := three_exterior_intrinsic_margin (φ:=Φ) g (R/2) C₁ hC₁
  refine ⟨C,hC,?_⟩
  filter_upwards [hproduce,eventually_all.mpr hb,hfreq,hcover,hcore,hexterior,eventually_ge_atTop (2:ℕ)]
    with k hproduce hb hfreq hcover hcore hexterior hk
  obtain ⟨u,hu,hc,hs,hj,hjet,hscore,hnod⟩ := hproduce
  have hk1 : 1  ≤  k := by omega
  have hkR : (1:ℝ)  ≤  k := by exact_mod_cast hk1
  have hk0 : (0:ℝ)<k := zero_lt_one.trans_le hkR
  have hνb := productWaveFrequency_bounds hk1
  have hν0 : 0<productWaveFrequency k := hk0.trans_le hνb.1
  have hs' : tsupport u⊆closedBall 0 (R/2) := hs.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hj' (y : NormalWaveSpace) (j : ℕ) (hjm : j  ≤  max m 1) :
      ‖iteratedFDeriv ℝ j u y‖  ≤  C₁*(k:ℝ)^(j+4)*Real.exp (productWaveFrequency k*Φ (threeNormalInv y)) ∧
      ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
          productFrequency k*u y) y‖  ≤  C₁*((k:ℝ)^(D+1))⁻¹*
          Real.exp (productWaveFrequency k*Φ (threeNormalInv y)) := by
    have hbd := hj y j hjm
    have hC01 : C₀  ≤  C₁ := le_mul_of_one_le_right hC₀.le (one_le_pow₀ (by norm_num))
    constructor
    · apply hbd.1.trans
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      calc
        _  ≤  C₀*(2*(k:ℝ))^(j+4) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν0.le hνb.2 _) hC₀.le
        _ = (C₀*2^(j+4))*(k:ℝ)^(j+4) := by rw [mul_pow]; ring
        _  ≤  _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)  ≤  2) (by omega)) hC₀.le)
          (pow_nonneg hk0.le _)
    · apply hbd.2.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul hC01
        (inv_anti₀ (pow_pos hk0 _) (pow_le_pow_left₀ hk0.le hνb.1 _))
        (by positivity) hC₁.le) (Real.exp_pos _).le
  have hU := (threeCoupled_smooth threeCouplingRadius k).add (threeWaveLift_smooth hu hc)
  have heq : (threeCoupled threeCouplingRadius k+threeWaveLift u) ∘ threeNormalInv=
      (threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u := by
    funext y; simp only [Function.comp_apply,Pi.add_apply,threeWaveLift_apply]
  have hlow (q : ThreeManifold) : threeWeight Φ k q/productWaveFrequency k^111  ≤
      |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
        Real.sqrt (coordinateGradientPair g
          (threeCoupled threeCouplingRadius k+threeWaveLift u)
          (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k := by
    by_cases hq : q∈threeExceptional Φ k
    · exact hmargin k hk1 hfreq Φ hcover _ hU (by simpa only [heq] using hjet) q hq
    · exact hexterior u hu hc hs' (fun y j hj1 => (hj' y j (hj1.trans (le_max_right _ _))).1)
        q hq (hext q (fun hqF => hq (hcore hqF)))
  refine ⟨u,hu,hc,hs,hlow,?_,hscore,hnod⟩
  intro i y hy j hjm
  have hbd := hb i u hu hc hs' (fun y j hjm => hj' y j (hjm.trans (le_max_left _ _))) y hy j hjm
  have hCsum : 1+∑ i, Cs i  ≤  C := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hCinc : Cs i  ≤  C := (hCi i).trans hCsum
  have hW := (threeWeight_pos Φ k ((chartAt ThreeModel (p i)).symm y)).le
  constructor
  · exact hbd.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hCinc (pow_le_pow_left₀ hk0.le hνb.1 _) (by positivity) hC.le) hW)
  · apply hbd.2.trans
    apply mul_le_mul_of_nonneg_right _ hW
    apply (div_le_div_iff₀ (pow_pos hk0 D) (pow_pos hν0 D)).mpr
    have hνD : productWaveFrequency k^D  ≤  2^D*(k:ℝ)^D := by
      simpa only [mul_pow] using pow_le_pow_left₀ hν0.le hνb.2 D
    calc
      _  ≤  (Cs i*(k:ℝ)^4)*(2^D*(k:ℝ)^D) :=
        mul_le_mul_of_nonneg_left hνD (mul_nonneg (hCs i).le (by positivity))
      _ = ((Cs i*2^D)*(k:ℝ)^4)*(k:ℝ)^D := by ring
      _  ≤  (C*productWaveFrequency k^4)*(k:ℝ)^D := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hk0.le D)
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hCi i) (by positivity))
          (pow_le_pow_left₀ hk0.le hνb.1 4) (by positivity) hC.le
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_three_scalar_producer :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
    ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ (tests : List (CoordinateTest ThreeModel ThreeManifold)) (N P : ℕ),
      ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
      let U := threeCoupled threeCouplingRadius n+threeWaveLift u
      let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) U
      let z := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) U
      (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ b ∧
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ z ∧
      (∀ x, 0 < b x ∧ 0 < z x) ∧
      (∀ x, weightedLaplacian g b U x+productFrequency n*z x*U x=0) ∧
      tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
      tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
      ∃ v : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x = productFrequency n*b x^3*v x^5-productFrequency n*z x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
        ENNReal.ofReal (A*(productWaveFrequency n)) < SignTests.signCertificate
          (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
          (fun a => ε/((productWaveFrequency n)*ℓ a.val))
          ((U ∘ threeNormalInv) ∘ normalWaveEquiv) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hproduce⟩ := exists_three_global_quasimodes
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR F hF hFa hext A
  obtain ⟨φ,hφ,hφnormal,δ,hδ,hin,hout,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    hproduce g hg a b ha hab hbR F hF hFa hext A
  refine ⟨I,hIa,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro tests N P
  let k := N+2
  have hs : Module.finrank ℝ ThreeModel < 2*(2*(k:ℝ)) := by
    simp only [threeModel_finrank,k,Nat.cast_add,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  let atlas := Classical.choice (nonempty_compactMetricAtlas g k hs)
  let D := (P+8)+((2*111+21)*(2*(k+1)+2)+10)+2
  obtain ⟨C,hC,hpacket⟩ := hproduce atlas.t atlas.p atlas.scalarChartSupport
    atlas.scalarChartSupport_compact (2*(k+1)+2) D
  let good (u : NormalWaveSpace → ℝ) := ContDiff ℝ ∞ u ∧ HasCompactSupport u
  have hzero : good 0 := ⟨contDiff_const,by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : NormalWaveSpace → ℝ))⟩
  obtain ⟨u,hu,hpacket⟩ := eventual_choice_with_good_default good 0 hzero
    (fun n u => tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
      (∀ q : ThreeManifold, threeWeight φ n q/(productWaveFrequency n)^111 ≤
        |(threeCoupled threeCouplingRadius n+threeWaveLift u) q|+
        Real.sqrt (coordinateGradientPair g
          (threeCoupled threeCouplingRadius n+threeWaveLift u)
          (threeCoupled threeCouplingRadius n+threeWaveLift u) q)/(productWaveFrequency n)) ∧
      (∀ i : atlas.t, ∀ y ∈ atlas.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
          (chartAt ThreeModel (atlas.p i)).symm) y‖ ≤
          C*(productWaveFrequency n)^(j+4)*threeWeight φ n ((chartAt ThreeModel (atlas.p i)).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
          productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
          (chartAt ThreeModel (atlas.p i)).symm) y‖ ≤
          C*(productWaveFrequency n)^4/(productWaveFrequency n)^D*threeWeight φ n ((chartAt ThreeModel (atlas.p i)).symm y)) ∧
      ENNReal.ofReal (A*(productWaveFrequency n)) < SignTests.signCertificate
        (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
        (fun a => ε/((productWaveFrequency n)*ℓ a.val))
        (((threeCoupled threeCouplingRadius n ∘
          threeNormalInv)+u) ∘ normalWaveEquiv))
    (hpacket.mono (by
      rintro n ⟨u,hu,hc,hs,hlow,hj,hscore,_⟩
      exact ⟨u,⟨hu,hc⟩,hs,hlow,hj,hscore⟩))
  let U (n : ℕ) := threeCoupled threeCouplingRadius n+threeWaveLift (u n)
  have hU (n : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (U n) :=
    (threeCoupled_smooth _ _).add (threeWaveLift_smooth (hu n).1 (hu n).2)
  have hNP : N ≤ 2*(k+1) := by dsimp [k]; omega
  have hN : Module.finrank ℝ ThreeModel < 2*(2*((k+1:ℕ):ℝ)-N) := by
    simp only [threeModel_finrank,k,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨L,hL,hfactor⟩ := atlas.eventually_product_scalar_factor_raw threeModel_finrank tests
    N P 111 D hNP hN (by exact le_rfl) hC U (threeWeight φ) hU (threeWeight_pos φ)
    (hpacket.mono (fun n hn => ⟨hn.2.1,
      fun i y hy j hj => (hn.2.2.1 i y hy j hj).1,
      fun i y hy j hj => (hn.2.2.1 i y hy j (by omega)).2⟩))
  refine ⟨L,hL,?_⟩
  filter_upwards [hpacket,hfactor,eventually_ge_atTop (1:ℕ)] with n hp hf hn
  obtain ⟨hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw⟩ := hf
  have hreg (x : ThreeManifold) (hx : U n x=0) : 0 < coordinateGradientPair g (U n) (U n) x := by
    have hlow := hp.2.1 x
    change threeWeight φ n x/(productWaveFrequency n)^111 ≤ |U n x|+_ at hlow
    rw [hx,abs_zero,zero_add] at hlow
    have hnpos : 0<productWaveFrequency n :=
      (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega)).trans_le (productWaveFrequency_bounds hn).1
    have hsqrt : 0 < Real.sqrt (coordinateGradientPair g (U n) (U n) x) := by
      have hdiv := (div_pos (threeWeight_pos φ n x) (pow_pos hnpos 111)).trans_le hlow
      exact (div_pos_iff_of_pos_right hnpos).mp hdiv
    exact Real.sqrt_pos.mp hsqrt
  refine ⟨u n,(hu n).1,(hu n).2,hp.1,hreg,hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw,?_⟩
  have he : ((U n ∘ threeNormalInv) ∘ normalWaveEquiv)=
      (((threeCoupled threeCouplingRadius n ∘
        threeNormalInv)+u n) ∘ normalWaveEquiv) := by
    funext x
    simp only [U,Function.comp_apply,Pi.add_apply,threeWaveLift_apply]
  rw [he]
  exact hp.2.2.2


end YauCounterexamples
end

end OAI
