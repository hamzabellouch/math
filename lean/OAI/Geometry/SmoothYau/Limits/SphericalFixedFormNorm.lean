import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.SphericalOpenFormNorm
import OAI.Geometry.SmoothYau.Geometry.ChartTensorNeighborhoodInst1
import OAI.Geometry.SmoothYau.Geometry.FixedMetricDiagonal
import OAI.Geometry.SmoothYau.Smoothness.CompactSmoothJetMap
import OAI.Geometry.SmoothYau.Spectrum.InverseFrequencyWeightedZero

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalStageFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalStageFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))

theorem exists_spherical_simple_stage
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {R t s r a b c : ℝ} (hR : (1/5:ℝ) ≤ R) (hRt : R<t) (hts : t<s) (hsr : s<r)
    (hra : r<a) (hab : a<b) (hbc : b<c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g R)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (M : ℕ) (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (by linarith) hext) ∈ U) :
    ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric (Euclidean 3) (Sphere 3),
      ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      ∃ u : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
        (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
        SphericalRegular u ∧ SphericalSimple h u (sphereFrequency k) ∧
        SphericalSignAbove u (A*(k:ℝ)) := by
  classical
  have hRc : R < c := hRt.trans (hts.trans (hsr.trans (hra.trans (hab.trans hbc))))
  have hRsmall : R≤3/10 := (hRc.trans hc).le
  let eg := sphericalExterior_support hRsmall hext
  let N : Set (SmoothMetric (Euclidean 3) (Sphere 3)) := {h | ∀ eh,
    chartTensorOfMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole) h eh ∈ U}
  have hN : IsSmoothNeighborhood g N := chartTensorRepresentation_neighborhood g₀ sourcePole
    sphericalTensorSupport (sphere_chart_target sourcePole) g eg U (hU.mem_nhds hgU)
  obtain ⟨partition,hpart,ell,hell,ε,hε,hpacket⟩ := exists_spherical_exact_stage g₀ hg₀ g hg
    (hR.trans hRt.le) hts hsr hra hab (hbc.trans hc)
    (isClosed_le (sphericalRadius_continuous _ _) continuous_const)
    (fun q hq => (show sphericalRadius sourceAxisOne sourceAxisTwo q≤R from hq).trans_lt hRt)
    (fun q hq v w => congrArg (fun T => T v w) (hext q (lt_of_not_ge hq))) hmetric A N hN
  obtain ⟨k,⟨hkpacket,hkM⟩,hk3⟩ := (hpacket.and (eventually_ge_atTop M) |>.and (eventually_ge_atTop 3)).exists
  obtain ⟨ĝ,hĝN,u,hu,hue,hreg,hout,hscore⟩ := hkpacket
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have heĝ : sphericalExterior g₀ ĝ b := by
    intro q hq
    ext v w
    exact ((hout q hq).1 v w).trans (congrArg (fun T => T v w) (hext q (by linarith)))
  let eĝ := sphericalExterior_support (hbc.trans hc).le heĝ
  have hĝU := hĝN eĝ
  have hu0 : u ≠ 0 := spherical_regular_nonzero u hreg
  obtain ⟨h,he,hhU,hhe,hsimple⟩ := spherical_pin_near g₀ hg₀ ĝ hb0 hbc hc heĝ k hk3 u hu hu0 hue
    (fun q hq => (hout q hq).2) U hU hĝU
  refine ⟨k,hkM,hk3,h,he,hhU,u,hu,hu0,hhe,hreg,hsimple,partition,hpart,(fun j => ε/((k:ℝ)*ell j.val)),?_,hscore⟩
  intro j
  exact div_pos hε (mul_pos (by exact_mod_cast (show 0<k by omega)) (hell j.val j.property))
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalFixedFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalFixedFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalFixedFormComplete : CompleteSpace (MetricForm (Euclidean 3)) := by
  let : ContinuousSMul ℝ (Euclidean 3) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean 3 →L[ℝ] ℝ) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Euclidean 3 →L[ℝ] ℝ) := ContinuousLinearMap.instCompleteSpace
  exact ContinuousLinearMap.instCompleteSpace

def sphericalStageRadius (n : ℕ) : ℝ := 3/10-1/(10*((n:ℝ)+1))
lemma sphericalStageRadius_bounds (n : ℕ) :
    1/5 ≤ sphericalStageRadius n ∧ sphericalStageRadius n < sphericalStageRadius (n+1) ∧
      sphericalStageRadius (n+1)<3/10 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0<10*((n:ℝ)+1) := by positivity
  have h2 : 0<10*((n:ℝ)+1+1) := by positivity
  dsimp [sphericalStageRadius]
  rw [Nat.cast_add,Nat.cast_one]
  constructor
  · have hh : 1/(10*((n:ℝ)+1)) ≤ 1/10 := (div_le_div_iff₀ h1 (by norm_num)).mpr (by nlinarith)
    linarith
  constructor
  · have hh : 1/(10*((n:ℝ)+1+1)) < 1/(10*((n:ℝ)+1)) :=
      (div_lt_div_iff₀ h2 h1).mpr (by linarith)
    linarith
  · have hh := div_pos (show (0:ℝ)<1 by norm_num) h2
    linarith

theorem exists_spherical_fixed_witnesses
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
    ∃ g ∈ N, ∀ n : ℕ, SphericalLargeWitness g ((n:ℝ)+1) ((n:ℝ)+1) := by
  classical
  let : MetricSpace SphericalTensor := compactSmoothMetricSpace sphericalTensorSupport
  let : CompleteSpace SphericalTensor := compactSmooth_complete sphericalTensorSupport
  obtain ⟨O,hO,h0O,hON⟩ := exists_spherical_open_model g₀ hg₀ N hN
  let P : ℕ → Set SphericalTensor := fun n =>
    {H | ∃ g : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ g (sphericalStageRadius n),
      H=sphericalTensorOf g₀ g (sphericalExterior_mono
        ((sphericalStageRadius_bounds n).2.1.trans (sphericalStageRadius_bounds n).2.2).le he) ∧ H∈O}
  let W : ℕ → Set SphericalTensor := fun n =>
    {H | ∃ hp : H∈sphericalPositiveSet g₀,
      SphericalLargeWitness (sphericalTensorMetric g₀ ⟨H,hp⟩) ((n:ℝ)+1) ((n:ℝ)+1)}
  have hstep : ∀ n, ∀ H ∈ P n, ∀ U : Set SphericalTensor, IsOpen U → H∈U →
      ∃ K∈P (n+1), K∈U ∧ ∃ V : Set SphericalTensor, IsOpen V ∧ K∈V ∧ V⊆W n := by
    intro n H hH U hU hHU
    obtain ⟨g,he,rfl,hgO⟩ := hH
    let e := sphericalExterior_mono
      ((sphericalStageRadius_bounds n).2.1.trans (sphericalStageRadius_bounds n).2.2).le he
    obtain ⟨hp,hgN,hgood⟩ := hON _ hgO
    have hmetric : sphericalTensorMetric g₀ ⟨sphericalTensorOf g₀ g e,hp⟩=g := sphericalTensorMetric_of g₀ g e
    rw [hmetric] at hgood
    let R := sphericalStageRadius n
    let C := sphericalStageRadius (n+1)
    have hR := (sphericalStageRadius_bounds n).1
    have hRC : R<C := (sphericalStageRadius_bounds n).2.1
    have hC : C<3/10 := (sphericalStageRadius_bounds n).2.2
    obtain ⟨k,hkM,hk3,h,eh,hhU,u,hu,hu0,hue,hreg,hsimple,hscore⟩ :=
      exists_spherical_simple_stage g₀ hg₀ g hgood.1 (R:=R)
        (t:=(5*R+C)/6) (s:=(4*R+2*C)/6) (r:=(3*R+3*C)/6)
        (a:=(2*R+4*C)/6) (b:=(R+5*C)/6) (c:=C) hR
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) hC he hgood.2 ((n:ℝ)+1) (n+3) (U∩O) (hU.inter hO) ⟨hHU,hgO⟩
    let eh' := sphericalExterior_mono hC.le eh
    let K := sphericalTensorOf g₀ h eh'
    let z : SphericalPositiveTensor g₀ := ⟨K,sphericalTensorOf_positive g₀ h eh'⟩
    have hqz : sphericalTensorMetric g₀ z=h := sphericalTensorMetric_of g₀ h eh'
    have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hkreal : (n:ℝ)+3≤k := by exact_mod_cast hkM
    have hk3real : (3:ℝ)≤k := by exact_mod_cast hk3
    have hepos : 0<sphereFrequency k := by dsimp [sphereFrequency]; positivity
    have heB : (n:ℝ)+1<sphereFrequency k := by dsimp [sphereFrequency]; nlinarith
    have heD : sphereFrequency k<2*(k:ℝ)^2 := by dsimp [sphereFrequency]; nlinarith
    have hev := spherical_largeWitness_eventually (sphericalTensorMetric g₀)
      (sphericalTensorMetric_family g₀) z k hk3 (sphereFrequency k) hepos u hu hu0
      (by simpa only [hqz] using hue) hreg (by simpa only [hqz] using hsimple)
      ((n:ℝ)+1) ((n:ℝ)+1) heB heD hscore
    obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
    refine ⟨K,⟨h,eh,rfl,hhU.2⟩,hhU.1,Subtype.val '' V,
      (sphericalPositiveSet_isOpen g₀).isOpenMap_subtype_val V hVo,⟨z,hzV,rfl⟩,?_⟩
    rintro H ⟨v,hv,rfl⟩
    exact ⟨v.property,hV hv⟩
  have hzP : (0:SphericalTensor)∈P 0 := by
    refine ⟨g₀,(fun _ _ => rfl),?_,h0O⟩
    exact (sphericalTensorOf_zero g₀).symm
  obtain ⟨H,hHO,hHW⟩ := fixed_metric_diagonal P W hstep 0 hzP hO h0O
  obtain ⟨hp,hgN,hgood⟩ := hON H hHO
  refine ⟨sphericalTensorMetric g₀ ⟨H,hp⟩,hgN,?_⟩
  intro n
  exact (hHW n).choose_spec

end YauCounterexamples
end

end OAI
