import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RoundPowerGlobalProfileResidual
import OAI.Geometry.SmoothYau.Geometry.ThreeProjectionNormedSpace
import OAI.Geometry.SmoothYau.Limits.CutoffFactorCompactRaw
import OAI.Geometry.SmoothYau.Smoothness.RoundPowerExteriorPerturbationJet

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff

def sphericalWaveLift (u : Euclidean 3 → ℝ) : Sphere 3 → ℝ := manifoldChartPush sourcePole u

lemma sphericalWaveLift_apply (u : Euclidean 3 → ℝ) (y : Euclidean 3) :
    sphericalWaveLift u ((chartAt (Euclidean 3) sourcePole).symm y)=u y :=
  manifoldChartPush_apply sourcePole u (by rw [sphere_chart_target]; trivial)

lemma sphericalWaveLift_smooth {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalWaveLift u) :=
  contMDiff_manifoldChartPush sourcePole hu hc (by rw [sphere_chart_target]; exact subset_univ _)

lemma sphericalWaveLift_tsupport {u : Euclidean 3 → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r}) :
    tsupport (sphericalWaveLift u) ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < r} := by
  intro q hq
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport sourcePole hc
    (by rw [sphere_chart_target]; exact subset_univ _) hq
  exact hs hy

lemma sphericalWaveLift_laplacian (g : SmoothMetric (Euclidean 3) (Sphere 3))
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (y : Euclidean 3) :
    laplaceBeltrami g (sphericalWaveLift u) ((chartAt (Euclidean 3) sourcePole).symm y)=
      laplaceBeltrami (sphereChartMetric g sourcePole) u y := by
  apply laplaceBeltrami_manifoldChartPush g (sphereChartMetric g sourcePole) sourcePole
    (by rw [sphere_chart_target]; trivial) hu hc (by rw [sphere_chart_target]; exact subset_univ _)
  exact Filter.Eventually.of_forall (fun z v w => chartMetricForm_pairing g sourcePole z v w)

lemma spherical_sublevel_compact (r : ℝ) :
    IsCompact {q : Sphere 3 | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r} :=
  (isClosed_le (sphericalRadius_continuous _ _) continuous_const).isCompact

theorem spherical_wave_lift_jets (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K) {r : ℝ} (hr : r < 1)
    (m : ℕ) : ∃ C > 0, ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ (B : ℕ → Sphere 3 → ℝ), (∀ j q, 0 ≤ B j q) →
      ∀ (R : Sphere 3 → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
      (∀ x : Euclidean 3, ∀ j ≤ m, ∀ i ≤ j,
        ‖iteratedFDeriv ℝ i u x‖ ≤ B j ((chartAt (Euclidean 3) sourcePole).symm x)) →
      (∀ x : Euclidean 3, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+Λ*u y) x‖ ≤
          R ((chartAt (Euclidean 3) sourcePole).symm x)) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (sphericalWaveLift u ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*B j ((chartAt (Euclidean 3) p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (sphericalWaveLift u) q+Λ*sphericalWaveLift u q) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤ C*R ((chartAt (Euclidean 3) p).symm y) := by
  let L : Set (Sphere 3) := {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r}
  have hLp : L ⊆ (chartAt (Euclidean 3) sourcePole).source :=
    sphericalRadius_sublevel_in_source sourcePole _ _ sphericalRadius_neg_sourcePole hr
  obtain ⟨C,hC,htransfer⟩ := compact_chart_weighted_jet_transfer sourcePole p
    (spherical_sublevel_compact r) hLp hK (by rw [sphere_chart_target]; exact subset_univ _) m
  refine ⟨C,hC,?_⟩
  intro u hu hc hs B hB R hR Λ hj hres y hy j h_j
  have hUs : tsupport (sphericalWaveLift u) ⊆ L := by
    intro q hq
    exact (show sphericalRadius sourceAxisOne sourceAxisTwo q < r from
      sphericalWaveLift_tsupport hc hs hq).le
  have he : ∀ z ∈ (chartAt (Euclidean 3) sourcePole).target,
      sphericalWaveLift u ((chartAt (Euclidean 3) sourcePole).symm z)=u z :=
    fun z _ => sphericalWaveLift_apply u z
  have hUsm := sphericalWaveLift_smooth hu hc
  have hRs : tsupport (fun q => laplaceBeltrami g (sphericalWaveLift u) q+Λ*sphericalWaveLift u q) ⊆ L :=
    (laplaceResidual_tsupport g _ Λ).trans hUs
  have hRsm : ContDiff ℝ ∞ (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+Λ*u y) := by
    rw [←contMDiff_iff_contDiff]
    exact (contMDiff_laplaceBeltrami (contMDiff_iff_contDiff.mpr hu) _).add
      (contMDiff_const.mul (contMDiff_iff_contDiff.mpr hu))
  constructor
  · apply htransfer _ u hu hUs he B hB _ y hy j h_j
    intro q hq j hjm i hij
    simpa only [(chartAt (Euclidean 3) sourcePole).left_inv (hLp hq)] using
      hj (chartAt (Euclidean 3) sourcePole q) j hjm i hij
  · apply htransfer _ _ hRsm hRs _ (fun _ => R) (fun _ => hR) _ y hy j h_j
    · intro z _
      simp only [sphericalWaveLift_laplacian g hu hc,sphericalWaveLift_apply]
    · intro q hq j hjm i hij
      simpa only [(chartAt (Euclidean 3) sourcePole).left_inv (hLp hq)] using
        hres (chartAt (Euclidean 3) sourcePole q) i (hij.trans hjm)


end


section
open Set Filter Manifold
open scoped Topology ContDiff

theorem spherical_wave_centered_first_jet
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {r : ℝ} (hr : r < 1) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ (φ : Sphere 3 → ℝ) (n : ℕ), 1 ≤ n →
      (∀ y : Euclidean 3, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
      ∀ q : Sphere 3,
        |sphericalWaveLift u q|+
          ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
          C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q) := by
  let K := sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo r
  obtain ⟨C₁,hC₁,hgrad⟩ := compact_chart_intrinsic_gradient_bound g₀ sourcePole
    (sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo sphericalRadius_neg_sourcePole hr)
    (by rw [sphere_chart_target]; exact subset_univ _)
  refine ⟨C₀+C₁*C₀,by positivity,?_⟩
  intro u hu hc hs φ n hn hj q
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hUsm := sphericalWaveLift_smooth hu hc
  by_cases hq : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r
  · let y := chartAt (Euclidean 3) sourcePole q
    have hqs := sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole hr hq
    have hy : y ∈ K := ⟨q,hq,rfl⟩
    have hqy : (chartAt (Euclidean 3) sourcePole).symm y=q :=
      (chartAt (Euclidean 3) sourcePole).left_inv hqs
    have he : sphericalWaveLift u ∘ (chartAt (Euclidean 3) sourcePole).symm=u :=
      funext (sphericalWaveLift_apply u)
    have hv := hj y 0 (by omega)
    have hd := hj y 1 (by omega)
    simp only [norm_iteratedFDeriv_zero,hqy,Nat.zero_add] at hv
    simp only [norm_iteratedFDeriv_one,hqy] at hd
    have hg := hgrad (sphericalWaveLift u) hUsm y hy
    rw [hqy,round_centered_gradient_norm g₀ q _ (hg₀ q),he] at hg
    have hval : sphericalWaveLift u q=u y := by rw [←hqy,sphericalWaveLift_apply]
    rw [hval]
    have hdiv := div_le_div_of_nonneg_right
      (hg.trans (mul_le_mul_of_nonneg_left hd hC₁.le)) hn0.le
    calc
      _ ≤ C₀*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q)+
          (C₁*(C₀*(n:ℝ)^(1+4)*Real.exp ((n:ℝ)*φ q)))/(n:ℝ) := add_le_add hv hdiv
      _ = _ := by field_simp; ring
  · have hqs : q ∉ tsupport (sphericalWaveLift u) := fun h =>
      hq (show sphericalRadius sourceAxisOne sourceAxisTwo q < r from
        sphericalWaveLift_tsupport hc hs h).le
    have he : sphericalWaveLift u =ᶠ[𝓝 q] (fun _ => (0:ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hqs
    have hval : sphericalWaveLift u q=0 := he.eq_of_nhds
    have hchart : sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm =ᶠ[𝓝 0]
        (fun _ => (0:ℝ)) := by
      apply he.comp_tendsto
      convert ((sphere_chart_symm_continuous q).continuousAt (x := (0 : Euclidean 3))).tendsto using 1
      have hz := (chartAt (Euclidean 3) q).left_inv (mem_chart_source (Euclidean 3) q)
      rw [sphere_chart_center] at hz
      rw [hz]
    rw [hval,(hchart.fderiv_eq)]
    have hright : 0 ≤ (C₀+C₁*C₀)*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q) := by positivity
    simpa using hright

end


section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff

section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [FiniteDimensional ℝ E] in
lemma scalarDifferential_chart_vector {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v : E) :
    scalarDifferential u ((chartAt E p).symm y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y v := by
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
      (n := ∞)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at he
  exact (congrArg (fun T => T v) he).symm

lemma chart_derivative_dual_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (v : E) :
    (fderiv ℝ (u ∘ (chartAt E p).symm) y v)^2 ≤
      coordinateGradientPair g u u ((chartAt E p).symm y)*chartMetricForm g p y v v := by
  have hh := scalarDifferential_dual_bound hu g ((chartAt E p).symm y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v)
  rw [scalarDifferential_chart_vector hu p hy] at hh
  simpa only [chartMetricForm_pairing] using hh
end

lemma realWaveJet_intrinsic_upper {U : Sphere 3 → ℝ}
    (hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (x : Fin 3 → ℝ)
    (hmetric : ∀ v : Euclidean 3,
      selfMetricFlat (sphereChartMetric g p) (normalWaveEquiv x) v v ≤ ‖v‖^2) :
    ‖realWaveJet n W ((U ∘ (chartAt (Euclidean 3) p).symm) ∘ normalWaveEquiv) x‖ ≤
      (|U ((chartAt (Euclidean 3) p).symm (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U ((chartAt (Euclidean 3) p).symm
          (normalWaveEquiv x)))/n)/W := by
  let q := (chartAt (Euclidean 3) p).symm (normalWaveEquiv x)
  let F := U ∘ (chartAt (Euclidean 3) p).symm
  have hF : ContDiff ℝ ∞ F := spherical_chart_pullback_smooth hU p
  have hG : 0 ≤ coordinateGradientPair g U U q := coordinateGradientPair_nonneg g U q
  have hder (i : Fin 3) : |fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1)| ≤
      Real.sqrt (coordinateGradientPair g U U q) := by
    have hd := chart_derivative_dual_bound hU g p
      (show normalWaveEquiv x ∈ (chartAt (Euclidean 3) p).target by rw [sphere_chart_target]; trivial)
      (normalWaveEquiv (Pi.single i 1))
    have hm := hmetric (normalWaveEquiv (Pi.single i 1))
    rw [normalWaveEquiv_single, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, one_pow] at hm
    have hd' : (fderiv ℝ F (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1)))^2 ≤
        coordinateGradientPair g U U q := by
      exact hd.trans ((mul_le_mul_of_nonneg_left
        (show chartMetricForm g p (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1))
          (normalWaveEquiv (Pi.single i 1)) ≤ 1 from by simpa only [normalWaveEquiv_single,selfMetricFlat_apply,sphereChartMetric_pairing] using hm) hG).trans_eq (mul_one _))
    have he := (hF.differentiable (by simp) _).hasFDerivAt.comp x normalWaveEquiv.hasFDerivAt
    have he' := congrArg (fun T => T (Pi.single i 1)) he.fderiv
    change fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1) =
      fderiv ℝ F (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1)) at he'
    rw [he']
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [sq_abs,Real.sq_sqrt hG]; exact hd')
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*U q‖ ≤ (|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),Real.norm_eq_abs]
    rw [mul_comm W⁻¹,←div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ hW.le
    exact le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hn.le)
  · change ‖n⁻¹*W⁻¹*fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1)‖ ≤
      (|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),abs_of_pos (inv_pos.mpr hn)]
    calc
      _ ≤ n⁻¹*W⁻¹*Real.sqrt (coordinateGradientPair g U U q) :=
        mul_le_mul_of_nonneg_left (hder i) (by positivity)
      _ = (Real.sqrt (coordinateGradientPair g U U q)/n)/W := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) hW.le

lemma realWaveJet_to_intrinsic_lower {U : Sphere 3 → ℝ}
    (hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (x : Fin 3 → ℝ) (B : ℕ)
    (hmetric : ∀ v : Euclidean 3,
      selfMetricFlat (sphereChartMetric g p) (normalWaveEquiv x) v v ≤ ‖v‖^2)
    (hjet : 1/n^B ≤ ‖realWaveJet n W
      ((U ∘ (chartAt (Euclidean 3) p).symm) ∘ normalWaveEquiv) x‖) :
    W/n^B ≤ |U ((chartAt (Euclidean 3) p).symm (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U ((chartAt (Euclidean 3) p).symm
          (normalWaveEquiv x)))/n := by
  have hh := (le_div_iff₀ hW).mp (hjet.trans (realWaveJet_intrinsic_upper hU g p hn hW x hmetric))
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh


end


section
open Set Filter Manifold
open scoped Topology ContDiff

def sphericalWeight (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) : ℝ :=
  Real.exp ((n:ℝ)*φ q)+‖planarLinear sourceAxisOne sourceAxisTwo q‖^n

lemma sphericalWeight_pos (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    0 < sphericalWeight φ n q := add_pos_of_pos_of_nonneg (Real.exp_pos _) (by positivity)

lemma spherical_inner_is_exceptional {φ : Sphere 3 → ℝ} {t : ℝ}
    (hgap : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {n : ℕ} (hn : 1 ≤ n) {q : Sphere 3}
    (hq : sphericalRadius sourceAxisOne sourceAxisTwo q < t) :
    ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
      (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hr := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q
  rw [←sphericalRadius_eq_planar_norm]
  have hbase : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ Real.exp (φ q) := by
    by_cases hz : sphericalRadius sourceAxisOne sourceAxisTwo q=0
    · rw [hz]; exact (Real.exp_pos _).le
    · have hr0 : 0 < sphericalRadius sourceAxisOne sourceAxisTwo q := lt_of_le_of_ne hr (Ne.symm hz)
      have hh := Real.exp_lt_exp.mpr (hgap q hr0 hq)
      rw [Real.exp_log hr0] at hh
      exact hh.le
  calc
    _ ≤ (Real.exp (φ q))^n := pow_le_pow_left₀ hr hbase n
    _ = Real.exp ((n:ℝ)*φ q) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hnR)

lemma spherical_global_exceptional_coverage {φ : Sphere 3 → ℝ}
    (hφ : Continuous φ) {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hgap : ∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
      φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) :
    ∀ᶠ n : ℕ in atTop, ∀ q : Sphere 3,
      ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) →
      sphericalRadius sourceAxisOne sourceAxisTwo q ≤ s := by
  let K : Set (Sphere 3) := {q | s ≤ sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hK : IsCompact K := (isClosed_le continuous_const (sphericalRadius_continuous _ _)).isCompact
  filter_upwards [compact_exterior_background_domination hK
    (sphericalRadius_continuous sourceAxisOne sourceAxisTwo).continuousOn hφ.continuousOn
    (fun q hq => ht.trans_le (hts.le.trans hq))
    (fun q hq => hgap q (hts.trans_le hq)) 6] with n hn
  intro q hq
  by_contra h
  have hh := hn q (le_of_not_ge h)
  rw [sphericalRadius_eq_planar_norm] at hh
  exact (not_lt_of_ge hq) hh

theorem spherical_global_jet_lower
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {φ : Sphere 3 → ℝ} {t : ℝ}
    (hin : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {F : Set (Sphere 3)} (hF : F ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < t})
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
    (hcover : ∀ q : Sphere 3, ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
      (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) → sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10)
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hsmall : ∀ q : Sphere 3, |sphericalWaveLift u q|+
      ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
        C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q))
    (hjet : ∀ y ∈ sphericalExceptionalInChart φ n,
      1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
        (((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) :
    ∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
      |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
      Real.sqrt (coordinateGradientPair g
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ) := by
  let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
  have hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth hu hc)
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  intro q
  by_cases hE : ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*φ q)
  · have hq := hcover q hE
    have hqs := sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) hq
    let x := normalWaveEquiv.symm (chartAt (Euclidean 3) sourcePole q)
    have hx : normalWaveEquiv x=chartAt (Euclidean 3) sourcePole q := normalWaveEquiv.apply_symm_apply _
    have hqx : (chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv x)=q := by
      rw [hx,(chartAt (Euclidean 3) sourcePole).left_inv hqs]
    have hW : sphericalChartWeight φ n x=sphericalWeight φ n q := by
      simp only [sphericalChartWeight,sphericalWeight,roundPlanarChart,hqx]
    have hxE : x ∈ sphericalExceptionalInChart φ n := by
      simpa only [sphericalExceptionalInChart,mem_ofPred_eq,roundPlanarChart,Function.comp_apply,hqx] using hE
    have he : U ∘ (chartAt (Euclidean 3) sourcePole).symm=
        (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) sourcePole).symm)+u := by
      funext y
      simp only [U,Function.comp_apply,Pi.add_apply,sphericalWaveLift_apply]
    have hlow := realWaveJet_to_intrinsic_lower hU g sourcePole hn0
      (hW.symm ▸ sphericalWeight_pos φ n q) x 110
      (hmetric _ (by rw [hx]; exact ⟨q,hq,rfl⟩))
      (by rw [he]; exact hjet x hxE)
    simpa only [hW,hqx] using hlow
  · have hqF : q ∉ F := fun hq => hE (spherical_inner_is_exceptional hin hn1 (hF hq))
    have hround : ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
        g.inner q v w=(inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q v)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q w) :=
      fun v w => (hext q hqF v w).trans (hg₀ q v w)
    have hlow := roundPower_dominant_perturbation_jet_lower sourceAxisOne sourceAxisTwo n hn1
      source_axes_orthonormal.1 source_axes_orthonormal.2.1 source_axes_orthonormal.2.2
      q (sphericalWaveLift u) (sphericalWaveLift_smooth hu hc) (φ q) C hnC (le_of_not_ge hE) (hsmall q)
    have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
    have hfour : (4:ℝ)≤(n:ℝ)^110 := by
      calc
        _ ≤ (n:ℝ)^2 := by nlinarith
        _ ≤ _ := pow_le_pow_right₀ (by linarith : (1:ℝ)≤n) (by omega : 2≤110)
    rw [round_centered_gradient_norm g q U hround]
    exact (div_le_div_of_nonneg_left (sphericalWeight_pos φ n q).le (by norm_num : (0:ℝ)<4) hfour).trans hlow

end


section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma sphericalWeight_chart (φ : Sphere 3 → ℝ) (p : Sphere 3) (n : ℕ) (y : Euclidean 3) :
    sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) =
      Real.exp ((n:ℝ)*(φ ∘ (chartAt (Euclidean 3) p).symm) y)+
        ‖roundPlanarChart sourceAxisOne sourceAxisTwo p y‖^n := rfl

lemma sphericalWeight_ge_exp (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    Real.exp ((n:ℝ)*φ q) ≤ sphericalWeight φ n q :=
  le_add_of_nonneg_right (by positivity)

lemma real_smooth_add_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f+h) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j h x‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  rw [iteratedFDeriv_add_apply (hf.of_le hj).contDiffAt (hh.of_le hj).contDiffAt]
  exact norm_add_le _ _

theorem spherical_wave_background_chart_bounds
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {φ : Sphere 3 → ℝ} (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
    (hgap : ∀ q ∈ F, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K)
    {r : ℝ} (hr : r < 1) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      (∀ y : Euclidean 3, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
          sphereFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
          sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) := by
  have hKt : K ⊆ (chartAt (Euclidean 3) p).target := by rw [sphere_chart_target]; exact subset_univ _
  obtain ⟨C₁,hC₁,hback⟩ := roundPower_weighted_chart_jets sourceAxisOne sourceAxisTwo p hK hKt
    (φ ∘ (chartAt (Euclidean 3) p).symm) (hφ.continuous.comp (sphere_chart_symm_continuous p)).continuousOn m
  obtain ⟨N,hN,hres⟩ := roundPower_global_profile_residual_rapid_decay g g₀ hg₀ hF hext
    sourceAxisOne sourceAxisTwo source_axes_orthonormal.1 source_axes_orthonormal.2.1
    source_axes_orthonormal.2.2 p hK hKt (φ ∘ (chartAt (Euclidean 3) p).symm)
    (hφ.continuous.comp (sphere_chart_symm_continuous p)).continuousOn m D
    (fun y _ hy hz => by
      have h := hgap _ hy (by
        rw [sphericalRadius_eq_planar_norm]
        exact norm_pos_iff.mpr hz)
      simpa only [sphericalRadius_eq_planar_norm,roundPlanarChart,Function.comp_apply] using h)
  obtain ⟨T,hT,htransfer⟩ := spherical_wave_lift_jets g p hK hr m
  let C := C₁+1+T*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast ((le_max_right N 1).trans hn)
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hnD : 0 < (n:ℝ)^D := pow_pos hn0 _
  have hn4 : (1:ℝ)≤(n:ℝ)^4 := one_le_pow₀ hn1
  intro u hu hc hs hj y hy j hjm
  let W := sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y)
  have hW : 0 < W := sphericalWeight_pos φ n _
  have hE := sphericalWeight_ge_exp φ n ((chartAt (Euclidean 3) p).symm y)
  let B := fun j q => C₀*(n:ℝ)^(j+4)*Real.exp ((n:ℝ)*φ q)
  let R := fun q => C₀*((n:ℝ)^(D+1))⁻¹*Real.exp ((n:ℝ)*φ q)
  have hlift := htransfer u hu hc hs B (fun j q => by dsimp [B]; positivity)
    R (fun q => by dsimp [R]; positivity) (sphereFrequency n)
    (fun x j hjm i hij => (hj x i (hij.trans hjm)).1.trans (by
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega : i+4≤j+4)) hC₀.le)
        (Real.exp_pos _).le))
    (fun x j hjm => (hj x j hjm).2) y hy j hjm
  have hback' := hback n y hy j hjm
  rw [←sphericalWeight_chart] at hback'
  have hres' := hres n ((le_max_left _ _).trans hn) y hy j hjm
  have hsmooth := sphericalWaveLift_smooth hu hc
  have hsum : ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
      (chartAt (Euclidean 3) p).symm)=
      (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) p).symm)+
      (sphericalWaveLift u ∘ (chartAt (Euclidean 3) p).symm) := rfl
  have hroundsm := roundPower_smooth sourceAxisOne sourceAxisTwo n
  constructor
  · rw [hsum]
    apply (real_smooth_add_jet_bound (spherical_chart_pullback_smooth hroundsm p)
      (spherical_chart_pullback_smooth hsmooth p) j y).trans
    apply (add_le_add hback' hlift.1).trans
    have hnj : (n:ℝ)^j ≤ (n:ℝ)^(j+4) := pow_le_pow_right₀ hn1 (by omega)
    calc
      _ ≤ C₁*(n:ℝ)^(j+4)*W+T*(C₀*(n:ℝ)^(j+4)*W) :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnj hC₁.le) hW.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hT.le)
      _ ≤ C*(n:ℝ)^(j+4)*W := by dsimp [C]; nlinarith [mul_nonneg (pow_nonneg hn0.le (j+4)) hW.le]
  · let R₁ := fun q => laplaceBeltrami g (roundPower sourceAxisOne sourceAxisTwo n) q+
      sphereFrequency n*roundPower sourceAxisOne sourceAxisTwo n q
    let R₂ := fun q => laplaceBeltrami g (sphericalWaveLift u) q+
      sphereFrequency n*sphericalWaveLift u q
    have hR₁ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ R₁ :=
      (contMDiff_laplaceBeltrami hroundsm g).add (contMDiff_const.mul hroundsm)
    have hR₂ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ R₂ :=
      (contMDiff_laplaceBeltrami hsmooth g).add (contMDiff_const.mul hsmooth)
    have he : ((fun q => laplaceBeltrami g
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
        sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
        (chartAt (Euclidean 3) p).symm)=
        (R₁ ∘ (chartAt (Euclidean 3) p).symm)+(R₂ ∘ (chartAt (Euclidean 3) p).symm) := by
      funext x
      have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
        le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
      have hadd := laplaceBeltrami_add (hroundsm.of_le h2) (hsmooth.of_le h2) g
        ((chartAt (Euclidean 3) p).symm x)
      dsimp only [Function.comp_apply,Pi.add_apply,R₁,R₂]
      change laplaceBeltrami g (fun y => roundPower sourceAxisOne sourceAxisTwo n y+sphericalWaveLift u y)
        ((chartAt (Euclidean 3) p).symm x) + _ = _
      rw [hadd]
      ring
    rw [he]
    apply (real_smooth_add_jet_bound (spherical_chart_pullback_smooth hR₁ p)
      (spherical_chart_pullback_smooth hR₂ p) j y).trans
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
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace
local instance threeWeightedNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeWeightedContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

lemma real_power_variable_weighted_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C > 0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^k).re) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  obtain ⟨C,hC,hjet⟩ := real_power_weighted_jets hf hK (fun _ => -2*D)
    continuousOn_const h
  refine ⟨C,hC,?_⟩
  intro k hk x hx j hj
  have hp : (0:ℝ)≤k := Nat.cast_nonneg _
  have hν := productWaveFrequency_bounds hk
  have hν0 : 0≤productWaveFrequency k := hp.trans hν.1
  have hm : -D≤φ x := by
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    exact (neg_le_neg (le_max_left B 0)).trans ((neg_le_neg hb).trans (neg_abs_le _))
  have he : Real.exp ((k:ℝ)*(-2*D))≤Real.exp (productWaveFrequency k*φ x) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (2*(k:ℝ))*(-D) := by ring
      _ ≤ productWaveFrequency k*(-D) := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr hD)
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hν0
  exact (hjet k x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add he le_rfl) (by positivity))

def threeWeight (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) : ℝ :=
  Real.exp (productWaveFrequency k*φ p)+threeGlobalRadius p^k
lemma threeWeight_pos (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) :
    0<threeWeight φ k p := add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (pow_nonneg (threeGlobalRadius_pos p).le _)

lemma threeCoupled_split_powers (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    threeCoupled r k p =
      ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k).re+
      (((r:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k).re := by
  simp only [threeCoupled,threeCoupledComplex,threeComplexPower,pow_one,mul_pow,
    Complex.add_re,add_mul,productA,productB,mul_assoc]

theorem threeCoupled_weighted_chart_jets {φ : ThreeManifold → ℝ}
    (hφ : Continuous φ) (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h : ℕ) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘
        (chartAt ThreeModel p).symm) x‖ ≤ C*(k:ℝ)^j*
          threeWeight φ k ((chartAt ThreeModel p).symm x) := by
  let a := threeComplexPower (productAxis 0) (productAxis 1) 1 ∘ (chartAt ThreeModel p).symm
  let b := fun x => (threeCouplingRadius:ℂ)*
    (threeComplexPower (productAxis 0) (productAxis 2) 1 ∘ (chartAt ThreeModel p).symm) x
  have ha : ContDiff ℝ ∞ a := threeComplexPower_chart_smooth _ _ _ _
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul (threeComplexPower_chart_smooth _ _ _ _)
  have hc : ContinuousOn (φ ∘ (chartAt ThreeModel p).symm) K :=
    (hφ.comp (three_chart_symm_continuous p)).continuousOn
  obtain ⟨A,hA,haj⟩ := real_power_variable_weighted_jets ha hK _ hc h
  obtain ⟨B,hB,hbj⟩ := real_power_variable_weighted_jets hb hK _ hc h
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro k hk x hx j hj
  have he : threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm =
      (fun y => (a y^k).re)+(fun y => (b y^k).re) := by
    funext y
    exact threeCoupled_split_powers _ _ _
  have han : ‖a x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [a,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one]
    exact le_max_left _ _
  have hbn : ‖b x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [b,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
    exact le_max_right _ _
  have hja := (haj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) han k)) (by positivity))
  have hjb := (hbj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hbn k)) (by positivity))
  rw [he]
  exact (real_smooth_add_jet_bound (Complex.reCLM.contDiff.comp (ha.pow k))
    (Complex.reCLM.contDiff.comp (hb.pow k)) j x).trans
    (calc
      _ ≤ A*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x)+
          B*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x) := add_le_add hja hjb
      _ = _ := by ring)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeResidualNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeResidualContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_dominated_chart_jets {φ : ThreeManifold → ℝ} (hφ : Continuous φ)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h : ℕ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ x∈K, threeGlobalLog ((chartAt ThreeModel p).symm x)+δ ≤ φ ((chartAt ThreeModel p).symm x)) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ x∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
  obtain ⟨C,hC,hJ⟩ := threeCoupled_weighted_chart_jets (hφ.sub continuous_const) p hK h (φ:=fun z => φ z-δ/2)
  refine ⟨2*C,by positivity,?_⟩
  intro k hk x hx j hj
  let z := (chartAt ThreeModel p).symm x
  have hb := productWaveFrequency_bounds hk
  have hn : 0≤productWaveFrequency k := (Nat.cast_nonneg k).trans hb.1
  have hrad : threeGlobalRadius z^k≤ Real.exp (productWaveFrequency k*(φ z-δ/2)) := by
    apply three_positive_envelope_gap z hk (δ:=δ/2)
    dsimp [z]
    linarith [hgap x hx]
  have he : Real.exp (productWaveFrequency k*(φ z-δ/2)) ≤
      (Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hb.1 (half_pos hδ).le
    nlinarith
  have hw : threeWeight (fun z => φ z-δ/2) k z ≤
      2*((Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z)) := by
    dsimp [threeWeight]
    linarith
  apply (hJ k hk x hx j hj).trans
  calc
    _ ≤ C*(k:ℝ)^j*(2*((Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

theorem threeCoupled_dominated_residual_rapid_decay
    (g : SmoothMetric ThreeModel ThreeManifold) {φ : ThreeManifold → ℝ} (hφ : Continuous φ)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ x∈K, threeGlobalLog ((chartAt ThreeModel p).symm x)+δ ≤ φ ((chartAt ThreeModel p).symm x)) :
    ∃ N : ℕ, 1≤N ∧ ∀ k≥N, ∀ x∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
        productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) x‖ ≤
          ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
  obtain ⟨A,hA,hAJ⟩ := threeCoupled_dominated_chart_jets hφ p hK (h+2) hδ hgap
  obtain ⟨L,hL,hLJ⟩ := laplaceBeltrami_residual_small_jets_on_compact g p hK
    (by rw [three_chart_target]; exact subset_univ _) h
  let ρ := Real.exp (-δ/2)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  let D := (L+3)*A
  have ht : Tendsto (fun k : ℕ => D*((k:ℝ)^(h+4+P)*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (h+4+P) hρ.le hρ1).const_mul D
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro k hk x hx j hj
  have hk1 : 1≤k := (le_max_right _ _).trans hk
  have hkR : 1≤(k:ℝ) := by exact_mod_cast hk1
  have hkpos : 0<(k:ℝ) := zero_lt_one.trans_le hkR
  have hsmall : D*(k:ℝ)^(h+4)*ρ^k≤((k:ℝ)^P)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hkpos P)).mpr
    have he : D*(k:ℝ)^(h+4)*ρ^k*(k:ℝ)^P=D*((k:ℝ)^(h+4+P)*ρ^k) := by rw [pow_add]; ring
    rw [he]
    exact (hN k ((le_max_left _ _).trans hk)).le
  let ε := A*(k:ℝ)^(h+2)*ρ^k*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x))
  have hε : 0≤ε := by dsimp [ε]; positivity
  have hraw : ∀ q≤h+2, ‖iteratedFDeriv ℝ q (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) x‖ ≤ ε := by
    intro q hq
    apply (hAJ k hk1 x hx q hq).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hkR hq) hA.le) (pow_nonneg hρ.le k)) (Real.exp_pos _).le
  have hh := hLJ _ (threeCoupled_smooth _ _) x hx ε (productFrequency k) hε
    (productFrequency_nonneg k) hraw j hj
  have hquad : (k:ℝ)≤(k:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hkpos.le]
  have hLb : L≤L*(k:ℝ)^2 := le_mul_of_one_le_right hL.le (one_le_pow₀ hkR)
  have hLam : L+productFrequency k≤(L+3)*(k:ℝ)^2 := by dsimp [productFrequency]; nlinarith
  apply hh.trans
  calc
    _ ≤ ((L+3)*(k:ℝ)^2)*ε := mul_le_mul_of_nonneg_right hLam hε
    _ = (D*(k:ℝ)^(h+4)*ρ^k)*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
      dsimp [D,ε]
      rw [show h+4=2+(h+2) by omega,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
lemma threeCoupled_clean_chart_jets (p : ThreeManifold) {K : Set ThreeModel}
    (hK : IsCompact K) (h : ℕ)
    (hρ : ∀ y∈K, 1/2≤‖productA ((chartAt ThreeModel p).symm y).1‖) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ y∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) y‖
        ≤ C*(k:ℝ)^j*‖productA ((chartAt ThreeModel p).symm y).1‖^k := by
  obtain ⟨C,hC,hj⟩ := threeCoupled_weighted_chart_jets
    (φ:=fun _ => Real.log (1/2)) continuous_const p hK h
  refine ⟨2*C,by positivity,?_⟩
  intro k hk y hy j hjh
  let q := (chartAt ThreeModel p).symm y
  have hr : threeGlobalRadius q=‖productA q.1‖ := by
    apply max_eq_left
    have hb := mul_le_mul_of_nonneg_left (productB_norm_le q.1)
      (show 0≤threeCouplingRadius by norm_num [threeCouplingRadius])
    norm_num [threeCouplingRadius] at hb ⊢
    linarith [hρ y hy]
  have he : Real.exp (productWaveFrequency k*Real.log (1/2))≤‖productA q.1‖^k := by
    calc
      _ ≤ Real.exp ((k:ℝ)*Real.log (1/2)) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (productWaveFrequency_bounds hk).1
          (Real.log_nonpos (by norm_num) (by norm_num)))
      _ = (1/2:ℝ)^k := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<1/2)]
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (hρ y hy) k
  have hh := hj k hk y hy j hjh
  change _ ≤ C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*Real.log (1/2))+threeGlobalRadius q^k) at hh
  rw [hr] at hh
  exact hh.trans (calc
    _ ≤ C*(k:ℝ)^j*(‖productA q.1‖^k+‖productA q.1‖^k) :=
      mul_le_mul_of_nonneg_left (add_le_add he le_rfl) (by positivity)
    _ = _ := by ring)

theorem threeCoupled_conjugate_projection_uniform
    (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
    {K : Set ThreeModel} (hK : IsCompact K)
    (hKO : K ⊆ (chartAt ThreeModel p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel p).symm y),
      g.inner _ v z = threeBackgroundMetric.inner _ v z)
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, 1/2 ≤ ‖productA ((chartAt ThreeModel p).symm y).1‖)
    (hKt : ∀ y ∈ K, ‖productA ((chartAt ThreeModel p).symm y).1‖ ≤ 3/4)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : ThreeManifold → ℝ),
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt ThreeModel p).symm y)) →
      (∀ y ∈ K, w ((chartAt ThreeModel p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt ThreeModel p).symm y) ≤ 1/4096) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex ThreeModel,
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => threeCoupled threeCouplingRadius n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  obtain ⟨C0,hC0,hCj⟩ := threeCoupled_clean_chart_jets p hK (h+1) hKr
  obtain ⟨A,hA,hAj⟩ := compact_metric_inverse_jets g p hK hKO h
  let C1 := C0*((h+1).factorial:ℝ)^2/(1/2)*(1+max 1 (D/(1/2)))^(h+1)
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let L := ∑ j, ‖Module.finBasis ℝ ThreeModel j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he (i : CoordIndex ThreeModel) : ‖Module.finBasis ℝ ThreeModel i‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let δ := (1/1024:ℝ)
  have hδ : 0 < δ := by norm_num [δ]
  let J := 2^h*A*C1*L
  let C := J*(C1*L)*(h.factorial:ℝ)^2/δ*
    (2+2*max 1 ((Fintype.card (CoordIndex ThreeModel):ℝ)*J*(C1*L)/δ))^h
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro w hw hw0 hwl hwu hwj hwG n hn y hy i j
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let W := ‖productA ((chartAt ThreeModel p).symm y).1‖^n
  have hrY : 0 < ‖productA ((chartAt ThreeModel p).symm y).1‖ :=
    (by norm_num : (0:ℝ)<1/2).trans_le (hKr y hy)
  have hW : 0 < W := pow_pos hrY _
  let u := fun x => threeCoupled threeCouplingRadius n x/w x
  have hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u :=
    (threeCoupled_smooth _ _).div₀ hw hw0
  have huw : ContDiffOn ℝ ∞ (w ∘ (chartAt ThreeModel p).symm)
      (chartAt ThreeModel p).target := fun z hz => (contDiffAt_inChart hw p hz).contDiffWithinAt
  have hu0 : ContDiffOn ℝ ∞ (threeCoupled threeCouplingRadius n ∘ (chartAt ThreeModel p).symm)
      (chartAt ThreeModel p).target :=
    fun z hz => (contDiffAt_inChart (threeCoupled_smooth _ _) p hz).contDiffWithinAt
  have huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt ThreeModel p).symm) y‖ ≤
      C1*(n:ℝ)^k*W := by
    exact sharp_conjugate_jet_bound_on (chartAt ThreeModel p).open_target (hKO hy)
      hu0 huw (h+1) (by norm_num : (0:ℝ)<1/2) hW hnR hC0.le hD (hwl y hy)
      (fun k hk => hCj n hn y hy k hk) (fun k hk hkh => hwj k hk hkh y hy)
  have hgrad : δ*((n:ℝ)*W)^2 ≤ coordinateGradientPair g u u ((chartAt ThreeModel p).symm y) :=
    threeCoupled_conjugate_gradient_lower g _ (hg y hy) n hn (hKr y hy) (hKt y hy)
      w hw hw0 (hwl y hy) (hwu y hy) (hwG y hy)
  have hp := chartGradientProjection_jet_bound hu g p (hKO hy) h hδ hnR hW hC1
    (zero_le_one.trans hA) hL he (fun i j k hk => hAj i j k hk y hy) huj hgrad i j
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg (Nat.cast_nonneg _) _))

end YauCounterexamples
end

end OAI
