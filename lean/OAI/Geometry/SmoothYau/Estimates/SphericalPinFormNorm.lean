import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SourceSignBox
import OAI.Geometry.SmoothYau.Spectrum.PinnedMetricContinuousSmoothFamily
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
local instance sphericalAmbientFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalAmbientFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
def sphericalTensorSupport : Compacts (Euclidean 3) :=
  ⟨sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
    sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num)⟩
abbrev SphericalTensor := 𝓓_{sphericalTensorSupport}(Euclidean 3,MetricForm (Euclidean 3))
def sphericalExterior (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)) (R : ℝ) : Prop :=
  ∀ q, R < sphericalRadius sourceAxisOne sourceAxisTwo q → g.inner q=g₀.inner q
lemma sphericalTensorSupport_image :
    (chartAt (Euclidean 3) sourcePole).symm '' (sphericalTensorSupport : Set (Euclidean 3)) =
      {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10} := by
  ext q
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num) y).mp hy
  · intro hq
    refine ⟨(chartAt (Euclidean 3) sourcePole) q,⟨q,hq,rfl⟩,?_⟩
    exact (chartAt (Euclidean 3) sourcePole).left_inv
      (sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
        sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) hq)
lemma sphericalExterior_support {g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)}
    {R : ℝ} (hR : R ≤ 3/10) (he : sphericalExterior g₀ g R) :
    ∀ q, q ∉ (chartAt (Euclidean 3) sourcePole).symm ''
      (sphericalTensorSupport : Set (Euclidean 3)) → g.inner q=g₀.inner q := by
  intro q hq
  rw [sphericalTensorSupport_image] at hq
  exact he q (hR.trans_lt (lt_of_not_ge hq))
def sphericalTensorOf (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) : SphericalTensor :=
  chartTensorOfMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole) g
    (sphericalExterior_support le_rfl he)
lemma sphericalExterior_mono {g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)}
    {R S : ℝ} (h : R ≤ S) (he : sphericalExterior g₀ g R) : sphericalExterior g₀ g S :=
  fun q hq => he q (h.trans_lt hq)
lemma sphericalTensorOf_zero (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    sphericalTensorOf g₀ g₀ (fun _ _ => rfl)=0 := by
  apply DFunLike.ext
  intro y
  change chartMetricForm g₀ sourcePole y-chartMetricForm g₀ sourcePole y=0
  exact sub_self _
lemma sphericalRadius_sq_planar (q : Sphere 3) :
    (sphericalRadius sourceAxisOne sourceAxisTwo q)^2 =
      Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) := by
  rw [sphericalRadius_sq]
  simp [planarLinear,Complex.normSq_apply,pow_two]
lemma spherical_regular_nonzero (u : Sphere 3 → ℝ)
    (hreg : ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm)
      ((chartAt (Euclidean 3) q) q) ≠ 0) : u ≠ 0 := by
  intro hu
  have hh := hreg sourcePole (by rw [hu]; rfl)
  apply hh
  simp only [hu,Function.comp_def,Pi.zero_apply]
  exact fderiv_const_apply 0
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
def SphericalSignAbove (u : Sphere 3 → ℝ) (L : ℝ) : Prop :=
  ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧
    ∃ d : {J : Box (Fin 3) // J ∈ partition.boxes} → ℝ, (∀ j, 0 < d j) ∧
      ENNReal.ofReal L < SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
def SphericalRegular (u : Sphere 3 → ℝ) : Prop :=
  ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm)
    ((chartAt (Euclidean 3) q) q) ≠ 0
def SphericalSimple (g : SmoothMetric (Euclidean 3) (Sphere 3)) (u : Sphere 3 → ℝ) (lam : ℝ) : Prop :=
  ∀ v, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
    (∀ x, -laplaceBeltrami g v x=lam*v x) → ∃ c : ℝ, v=fun x => c*u x

def SphericalLargeWitness (g : SmoothMetric (Euclidean 3) (Sphere 3)) (A B : ℝ) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ ∃ e : ℝ, ∃ u : Sphere 3 → ℝ,
    B < e ∧ e < 2*(k:ℝ)^2 ∧ ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      (∀ x, -laplaceBeltrami g u x=e*u x) ∧ SphericalRegular u ∧ SphericalSignAbove u (A*(k:ℝ))
lemma spherical_largeWitness_eventually {P : Type*} [TopologicalSpace P]
    (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt (Euclidean 3) r).target) (a₀ : P) (k : ℕ) (hk : 3≤k)
    (e : ℝ) (he : 0<e) (u : Sphere 3 → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
    (hreg : SphericalRegular u) (hsimple : SphericalSimple (q a₀) u e)
    (A B : ℝ) (hB : B<e) (hD : e<2*(k:ℝ)^2) (hscore : SphericalSignAbove u (A*(k:ℝ))) :
    ∀ᶠ a in 𝓝 a₀, SphericalLargeWitness (q a) A B := by
  classical
  obtain ⟨partition,hpart,d,hd,hscore⟩ := hscore
  have hev := spherical_simple_eigenpair_open q hq a₀ e he u hu hu0 hue hsimple hreg
    (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val) d
    ((chartAt (Euclidean 3) sourcePole).symm ∘ normalWaveEquiv)
    ((sphere_chart_symm_continuous sourcePole).comp normalWaveEquiv.continuous)
    (ENNReal.ofReal (A*(k:ℝ))) hscore hB hD
  filter_upwards [hev] with a ha
  obtain ⟨e,v,heb,hed,hv,hv0,hve,hvr,hvl⟩ := ha
  exact ⟨k,hk,e,v,heb,hed,hv,hv0,hve,hvr,partition,hpart,d,hd,hvl⟩
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalPinFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalPinFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem spherical_pin_near
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) {b c : ℝ}
    (hb0 : 0<b) (hbc : b<c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g b) (k : ℕ) (hk3 : 3≤k)
    (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ q, -laplaceBeltrami g u q=sphereFrequency k*u q)
    (hout : ∀ q, b<sphericalRadius sourceAxisOne sourceAxisTwo q → u q=roundPower sourceAxisOne sourceAxisTwo k q)
    (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (hbc.trans hc).le hext) ∈ U) :
    ∃ h : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
      SphericalSimple h u (sphereFrequency k) := by
  classical
  have hc0 : 0<c := hb0.trans hbc
  let I := (nonempty_metricIntegralAtlas (E:=Euclidean 3) (M:=Sphere 3)).some
  let caxis : Euclidean 4 := EuclideanSpace.single 2 1
  have haxis : inner ℝ caxis caxis=1 ∧ inner ℝ sourceAxisOne caxis=0 ∧
      inner ℝ sourceAxisTwo caxis=0 := by
    norm_num [caxis,sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]
  have hbl : 0 < b^2 := sq_pos_of_pos hb0
  have hblc : b^2<c^2 := by nlinarith
  have hc1 : c^2<1 := by nlinarith
  obtain ⟨K,hKsimple⟩ := exists_annular_simple_pinned_family I g sourceAxisOne sourceAxisTwo caxis
    source_axes_orthonormal.1 source_axes_orthonormal.2.1 haxis.1
    source_axes_orthonormal.2.2 haxis.2.1 haxis.2.2 k (by omega) hbl hblc hc1
    ⟨u,hu⟩ hu0 hue
    (fun q hq _ => hout q (by rw [← sphericalRadius_sq_planar] at hq; nlinarith [sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q]))
    (fun q hq _ X Y => by
      have hqb : b < sphericalRadius sourceAxisOne sourceAxisTwo q := by
        rw [← sphericalRadius_sq_planar] at hq
        nlinarith [sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q]
      exact (congrArg (fun T => T X Y) (hext q hqb)).trans (hg₀ q X Y))
  let qp (z : ℝ) := pinnedMetric g K.val K.property.1 z
  have heqp (z : ℝ) : sphericalExterior g₀ (qp z) c := by
    intro q hq
    have hn : q ∉ {p : Sphere 3 | b^2 < Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo p) ∧
        Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo p) < c^2} := by
      intro hh
      change b^2 < Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) ∧
        Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) < c^2 at hh
      rw [← sphericalRadius_sq_planar] at hh
      nlinarith [hh.2]
    exact (pinnedMetric_exterior g K z q hn).trans (hext q (hbc.trans hq))
  let eqp (z : ℝ) := sphericalExterior_support hc.le (heqp z)
  have hcont : Continuous (fun z => chartTensorOfMetric g₀ sourcePole sphericalTensorSupport
      (sphere_chart_target sourcePole) (qp z) (eqp z)) := by
    apply continuous_chartTensorOfMetric
    intro i j
    simpa only [sphere_chart_target] using pinnedMetric_continuousSmoothFamily g K sourcePole i j
  have hzero : qp 0=g := pinnedMetric_at_zero g K.val K.property.1
  have hmem : ∀ᶠ z in 𝓝 (0:ℝ), chartTensorOfMetric g₀ sourcePole sphericalTensorSupport
      (sphere_chart_target sourcePole) (qp z) (eqp z) ∈ U :=
    hcont.continuousAt.eventually (hU.mem_nhds (by simpa only [hzero,sphericalTensorOf] using hgU))
  obtain ⟨z,hzU,hzs⟩ := ((hmem.filter_mono nhdsWithin_le_nhds).and hKsimple).exists
  refine ⟨qp z,heqp z,hzU,?_,hzs⟩
  exact pinnedMetric_preserves_eigenfunction g K hu hue z

end YauCounterexamples
end

end OAI
