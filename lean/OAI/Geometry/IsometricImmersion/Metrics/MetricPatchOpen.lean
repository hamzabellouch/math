import OAI.Geometry.IsometricImmersion.Assembly.SupportedMetricJets
import OAI.Geometry.IsometricImmersion.Assembly.SupportedSmoothComplete
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def metricQuadraticValue (G : MetricMatrix) (v : Coord) : ℝ := v ⬝ᵥ (G *ᵥ v)

theorem metricQuadraticValue_continuousAt {T : Type*} [TopologicalSpace T]
    {G : T → MetricMatrix} {v : T → Coord} {t : T}
    (hG : ∀ i j, ContinuousAt (fun a => G a i j) t)
    (hv : ∀ i, ContinuousAt (fun a => v a i) t) :
    ContinuousAt (fun a => metricQuadraticValue (G a) (v a)) t := by
  simp only [metricQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fun_prop

theorem posDef_of_positive_on_sphere {G : MetricMatrix} (hG : G.IsHermitian)
    (hQ : ∀ v ∈ Metric.sphere (0 : Coord) 1, 0 < metricQuadraticValue G v) : G.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hG
  intro v hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w : Coord := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : Coord) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right]
    simp [w, norm_smul, hn]
  have heq : metricQuadraticValue G w = (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    simp only [metricQuadraticValue, w, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hmul : 0 < (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    rw [← heq]
    exact hQ w hw
  have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_ne_zero (inv_ne_zero hn)
  have hvQ : 0 < metricQuadraticValue G v := (mul_pos_iff_of_pos_left hs).mp hmul
  simpa only [metricQuadraticValue, star_trivial] using hvQ

theorem perturbationTensor_isHermitian (η : SymmetricPerturbation) (p : Coord) :
    (perturbationTensor η p).IsHermitian := by
  change (perturbationTensor η p)ᴴ = perturbationTensor η p
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using
    perturbationTensor_symmetric η p j i

theorem perturbedMetric_isHermitian {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) : (perturbedMetric g0 η p).IsHermitian :=
  (hg0.2 p hp).isHermitian.add (perturbationTensor_isHermitian η p)

def metricPositiveSet (g0 : MetricField) : Set SymmetricPerturbation :=
  {η | ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef}

theorem metricPositiveSet_mem_nhds {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {η : SymmetricPerturbation} (hη : η ∈ metricPositiveSet g0) :
    metricPositiveSet g0 ∈ 𝓝 η := by
  have hcompact : IsCompact (modelSquare ×ˢ Metric.sphere (0 : Coord) 1) :=
    modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hgood : ∀ᶠ θ in 𝓝 η, ∀ pv ∈ modelSquare ×ˢ Metric.sphere (0 : Coord) 1,
      0 < metricQuadraticValue (perturbedMetric g0 θ pv.1) pv.2 := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro pv hpv
    have hm : Continuous (fun a : SymmetricPerturbation × (Coord × Coord) => (a.1, a.2.1)) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have hcoeff (i j : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => perturbedMetric g0 a.1 a.2.1 i j)
        (η, pv) := by
      have hb : ContinuousAt
          (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j) (η, pv.1) :=
        perturbedMetric_coeff_joint_continuousAt (η := η) hg0 hU (hSU hpv.1) i j
      have hh := hb.comp (x := (η, pv)) hm.continuousAt
      convert hh using 1
      rfl
    have hv (i : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => a.2.2 i) (η, pv) := by fun_prop
    have hc := metricQuadraticValue_continuousAt hcoeff hv
    have hvne : pv.2 ≠ 0 := by
      intro hz
      have hn : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hpv.2
      simp only [hz, norm_zero] at hn
      norm_num at hn
    have hq : 0 < metricQuadraticValue (perturbedMetric g0 η pv.1) pv.2 := by
      simpa only [metricQuadraticValue, star_trivial] using (hη pv.1 hpv.1).dotProduct_mulVec_pos hvne
    exact continuousAt_const.eventually_lt hc hq
  filter_upwards [hgood] with θ hθ
  intro p hp
  exact posDef_of_positive_on_sphere (perturbedMetric_isHermitian hg0 θ (hSU hp))
    (fun v hv => hθ (p, v) ⟨hp, hv⟩)

theorem metricPositiveSet_isOpen {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) :
    IsOpen (metricPositiveSet g0) :=
  isOpen_iff_mem_nhds.mpr fun _ hη => metricPositiveSet_mem_nhds hg0 hU hSU hη

theorem centralBox_subset_modelSquare : centralBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem centralCurvatureJet_eventually {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {kappa : ℝ} {η : SymmetricPerturbation}
    (hpos : η ∈ metricPositiveSet g0)
    (hK : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2) :
    ∀ᶠ θ in 𝓝 η, ∀ p ∈ centralBox, perturbedCurvatureJet g0 θ p < -kappa / 2 := by
  have hc : IsCompact centralBox := isCompact_Icc
  apply hc.eventually_forall_of_forall_eventually
  intro p hp
  have hpU := hSU (centralBox_subset_modelSquare hp)
  have hpd : (perturbedMetric g0 η p).PosDef := hpos p (centralBox_subset_modelSquare hp)
  have hd : (perturbedMetric g0 η p).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit).ne_zero
  have hcont := perturbedCurvatureJet_joint_continuousAt hg0 hU hpU hd
  have hval : perturbedCurvatureJet g0 η p < -kappa / 2 := by
    rw [← gaussianCurvature_perturbedMetric_eq_jet hg0 hU η hpos hpU]
    exact hK p hp
  exact hcont.eventually_lt continuousAt_const hval

theorem metricPatchSet_isOpen {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    IsOpen (metricPatchSet g0 kappa) := by
  apply isOpen_iff_mem_nhds.mpr
  intro η hη
  have hpos : η ∈ metricPositiveSet g0 := hη.1
  filter_upwards [metricPositiveSet_mem_nhds hg0 hU hSU hpos,
    centralCurvatureJet_eventually hg0 hU hSU hpos hη.2] with θ hθpos hθK
  refine ⟨hθpos, ?_⟩
  intro p hp
  rw [gaussianCurvature_perturbedMetric_eq_jet hg0 hU θ hθpos
    (hSU (centralBox_subset_modelSquare hp))]
  exact hθK p hp

theorem metricPatchSet_baire {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    BaireSpace (metricPatchSet g0 kappa) := by
  let : BaireSpace SymmetricPerturbation := symmetricPerturbation_baire
  exact (metricPatchSet_isOpen hg0 hU hSU kappa).baireSpace

theorem constructedModel_metricPatchSet_isOpen {kappa : ℝ}
    (hk : 0 < kappa) (hkSmall : kappa ≤ (1 : ℝ) / 31000) :
    IsOpen (metricPatchSet (constructedModelMetric kappa) kappa) :=
  metricPatchSet_isOpen (constructedModelMetric_spec hk hkSmall).1 modelMetricDomain_isOpen
    modelMetricDomain_contains_model_square kappa

theorem constructedModel_metricPatchSet_baire {kappa : ℝ}
    (hk : 0 < kappa) (hkSmall : kappa ≤ (1 : ℝ) / 31000) :
    BaireSpace (metricPatchSet (constructedModelMetric kappa) kappa) :=
  metricPatchSet_baire (constructedModelMetric_spec hk hkSmall).1 modelMetricDomain_isOpen
    modelMetricDomain_contains_model_square kappa

end SmoothLocal.Perturbation

end

end OAI
