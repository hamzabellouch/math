import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.QuadricSmoothExhaustion
import OAI.Geometry.BallPacking.SurfaceArea.CubicRadialEndSmooth

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian
open scoped BigOperators
open FiniteMoment
section

local instance cubicAreaExhaustionSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

theorem exists_cubic_end_cutoff : ∃ (g : ℝ → ℝ) (r R : ℝ),0<r ∧ 0<R ∧
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ t,g t∈Icc (0:ℝ) 1) ∧
    (∀ t∈Ioo (-r) r,g t=1) ∧ tsupport g⊆Iic R ∧
    {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
  obtain ⟨d,hd,hdb⟩ := Metric.mem_nhds_iff.mp
    (endRegularRegion_open.mem_nhds zero_mem_endRegularRegion)
  let R := (d/2)^2
  have hR : 0<R := sq_pos_of_pos (by linarith)
  have hreg : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
    intro s hs
    apply hdb
    rw [Metric.mem_ball,dist_zero_right]
    have hn : ‖s‖≤d/2 := (sq_le_sq₀ (norm_nonneg s) (by linarith : 0≤d/2)).mp (by
      simpa only [Complex.normSq_eq_norm_sq,R,mem_ofPred_eq] using hs)
    linarith
  obtain ⟨g,hg,hgc,hgs,hg1,hgb⟩ := exists_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (-R/2) (R/2))) isOpen_Ioo
    (show Icc (-R/2) (R/2)⊆Ioo (-R) R by intro t ht; constructor <;> linarith [ht.1,ht.2])
  refine ⟨g,R/2,R,by linarith,hR,hg,hgc,hgb,?_,?_,hreg⟩
  · intro t ht
    have he : g=ᶠ[𝓝 t] fun _ => 1 := hg1.filter_mono
      (nhds_le_nhdsSet (show t∈Icc (-R/2) (R/2) by
        constructor <;> linarith [ht.1,ht.2]))
    exact he.eq_of_nhds
  · exact fun t ht => (hgs ht).2.le

theorem tendsto_cubic_cutoff_mass
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hb : ∀ t,g t∈Icc (0:ℝ) 1) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
      (curveFSForm c)) atTop (𝓝 (3*c*Real.pi)) := by
  classical
  choose β hβ hβc he using fun ε : EndIndex => exists_regularEndPrimitive_extension hR ε c
  have ht := tendsto_curveEndCutoff_variable_residue (parameters 0)
    (curveFSPrimitive c) (curveFSPrimitive_smooth c) (curveFSForm c)
    (curveFSForm_smooth c) (curveFSForm_skew c) (curveFSPrimitive_exterior c)
    hg hc hr hRp (fun s hs => (hR hs).1) h1 h0 hb (fun ε => endResidue ε c) β hβ hβc
    (fun ε y hy hys => by
      have hRy : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
        apply hR
        change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
        rw [radiusSq_complex]
        exact hy.2
      have hU := endRegularRegion_open.preimage Complex.equivRealProdCLM.symm.continuous
      have hgβ := cubic_regular_extension_germ (he ε) hy.2
      filter_upwards [(infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hys,
        hU.mem_nhds hRy,hgβ] with z hz hzR hzβ
      rw [cubic_curveFSPrimitive_infinity ε c hz hzR,hzβ])
  convert ht using 1
  congr 1
  exact congrArg (fun x : ℝ => x*Real.pi) (sum_endResidue c).symm

theorem cubic_compact_area_le_degree {c : ℝ} (hc : 0<c) {D : Set BaseCurve} (hD : IsCompact D) :
    compactSurfaceFormIntegral hD (curveFSForm c)≤3*c*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_cubic_end_cutoff
  apply ge_of_tendsto (tendsto_cubic_cutoff_mass hg hgc hr hR.le hreg h1 h0 hb c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact (parameters 0) hR.le h0 hD] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions (parameters 0)) hD
    (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
    (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range (parameters 0) (fun t => hb _) x).1) hn
    (curveFSForm_smooth c) (curveFSForm_skew c)
    (fun b y hy => (curveFSForm_positive hc b hy).le)

theorem tendsto_cubic_exhaustion_area {c : ℝ} (hc : 0<c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ)) (curveFSForm c))
      atTop (𝓝 (3*c*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_cubic_end_cutoff
  have ht := tendsto_cubic_cutoff_mass hg hgc hr hR.le hreg h1 h0 hb c
  apply tendsto_order.mpr
  constructor
  · intro b hbdeg
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hbdeg).exists
    filter_upwards [compact_eventually_subset_projectionDomain (parameters 0)
      (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions (parameters 0))
      (projectionDomain_compact (parameters 0) _) (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n) hℓ
      (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range (parameters 0) (fun t => hb _) x).2)
      (curveFSForm_smooth c) (curveFSForm_skew c)
      (fun b y hy => (curveFSForm_positive hc b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (cubic_compact_area_le_degree hc
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))).trans_lt hb)

end
section

local instance cubicAreaCutoffSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

 theorem exists_small_cubic_end_cutoff : ∃ (g : ℝ → ℝ) (r R : ℝ),0<r ∧ 0<R ∧ R<1 ∧
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ t,g t∈Icc (0:ℝ) 1) ∧
    (∀ t∈Ioo (-r) r,g t=1) ∧ tsupport g⊆Iic R ∧
    {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
  obtain ⟨d,hd,hdb⟩ := Metric.mem_nhds_iff.mp
    (endRegularRegion_open.mem_nhds zero_mem_endRegularRegion)
  let e := min d 1
  have he : 0<e := lt_min hd (by norm_num)
  have hed : e≤d := min_le_left _ _
  have he1 : e≤1 := min_le_right _ _
  let R := (e/2)^2
  have hR : 0<R := sq_pos_of_pos (by linarith)
  have hR1 : R<1 := by dsimp [R]; nlinarith
  have hreg : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
    intro s hs
    apply hdb
    rw [Metric.mem_ball,dist_zero_right]
    have hn : ‖s‖≤e/2 := (sq_le_sq₀ (norm_nonneg s) (by linarith : 0≤e/2)).mp (by
      simpa only [Complex.normSq_eq_norm_sq,R,mem_ofPred_eq] using hs)
    linarith
  obtain ⟨g,hg,hgc,hgs,hg1,hgb⟩ := exists_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (-R/2) (R/2))) isOpen_Ioo
    (show Icc (-R/2) (R/2)⊆Ioo (-R) R by intro t ht; constructor <;> linarith [ht.1,ht.2])
  refine ⟨g,R/2,R,by linarith,hR,hR1,hg,hgc,hgb,?_,?_,hreg⟩
  · intro t ht
    have heq : g=ᶠ[𝓝 t] fun _ => 1 := hg1.filter_mono
      (nhds_le_nhdsSet (show t∈Icc (-R/2) (R/2) by constructor <;> linarith [ht.1,ht.2]))
    exact heq.eq_of_nhds
  · exact fun t ht => (hgs ht).2.le

 theorem reduced_cubic_compact_area_le {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : MomentPlane} (hp : p∈openTrapezoid A B) {c : ℝ} (hc : 0<c)
    {K : Set BaseCurve} (hK : IsCompact K) :
    compactSurfaceFormIntegral hK
      (reducedForm (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)≤
      c*(3*((D:ℝ)-3*(p 0+p 1))-2*markedHeight S p)*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  have hs := trapezoidWeight_surrounds hAB hp
  apply ge_of_tendsto (tendsto_reduced_cubic_cutoff_mass hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact (parameters 0) hR.le h0 hK] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions (parameters 0)) hK
    (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
    (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).1) hn
    (reducedForm_smooth _ _ c hs) (reducedForm_skew _ _ _ c p)
    (fun b y hy => (reducedForm_positive (cubicMarked_lt_degree hB hS) hc hs b hy).le)

 theorem tendsto_reduced_cubic_exhaustion_area {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : MomentPlane} (hp : p∈openTrapezoid A B) {c : ℝ} (hc : 0<c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (reducedForm (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p 0+p 1))-2*markedHeight S p)*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  have hs := trapezoidWeight_surrounds hAB hp
  have ht := tendsto_reduced_cubic_cutoff_mass hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hb).exists
    filter_upwards [compact_eventually_subset_projectionDomain (parameters 0)
      (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions (parameters 0))
      (projectionDomain_compact (parameters 0) _) (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n) hℓ
      (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).2)
      (reducedForm_smooth _ _ c hs) (reducedForm_skew _ _ _ c p)
      (fun b y hy => (reducedForm_positive (cubicMarked_lt_degree hB hS) hc hs b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (reduced_cubic_compact_area_le hA hS0 hAB hSB hB hS hp hc
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))).trans_lt hb)

end

local instance radialCubicCompactAreaSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

 theorem radial_cubic_compact_area_le {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) {c : ℝ} (hc : 0<c)
    {K : Set BaseCurve} (hK : IsCompact K) :
    compactSurfaceFormIntegral hK
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)≤
      c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  apply ge_of_tendsto (tendsto_radial_cubic_cutoff_mass hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact (parameters 0) hR.le h0 hK] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions (parameters 0)) hK
    (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
    (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).1) hn
    (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p)
    (fun b y hy => (radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc hp b hy).le)

 theorem tendsto_radial_cubic_exhaustion_area {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) {c : ℝ} (hc : 0<c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  have ht := tendsto_radial_cubic_cutoff_mass hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hb).exists
    filter_upwards [compact_eventually_subset_projectionDomain (parameters 0)
      (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions (parameters 0))
      (projectionDomain_compact (parameters 0) _) (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n) hℓ
      (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).2)
      (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p)
      (fun b y hy => (radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc hp b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (radial_cubic_compact_area_le hA hS0 hAB hSB hB hS hp hc
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))).trans_lt hb)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem compactSurfaceFormIntegral_mono {C D : Set M} (hC : IsCompact C)
    (hD : IsCompact D) (hCD : C⊆D) (hor : PositivePlaneTransitions M)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0≤chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hC Ω≤compactSurfaceFormIntegral hD Ω := by
  let B := fun b : compactSurfaceBoxes hD => b.1
  let ρ := compactSurfacePartition hD
  have hρ := compactSurfacePartition_subordinate hD
  rw [compactSurfaceFormIntegral_eq_setIntegral hC hor hCD B ρ hρ hΩ ha hp,
    compactSurfaceFormIntegral_eq_setIntegral hD hor Subset.rfl B ρ hρ hΩ ha hp]
  apply setIntegral_mono_set
  · exact (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp
      (contMDiff_const (c := (1:ℝ)))).integrableOn
  · exact Filter.Eventually.of_forall (fun _ => zero_le_one)
  · exact Filter.Eventually.of_forall (fun x hx => hCD hx)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

local instance radialCubicUniformAreaSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

 theorem tendstoUniformlyOn_radial_cubic_area {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {c : ℝ} (hc : 0<c) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p))
      (fun p => c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)
      atTop P := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto hP
  · intro ℓ
    exact radial_compact_area_continuousOn hA hAB _ _ c hP hPS
      (projectionDomain_compact (parameters 0) _)
  · intro p hp i j hij
    apply compactSurfaceFormIntegral_mono _ _ ?_ (positivePlaneTransitions (parameters 0))
      (radialForm_smooth hA hAB _ _ c (hPS hp)) (radialForm_skew _ _ _ c p)
      (fun b y hy => (radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy).le)
    intro x hx
    change ‖x.val.1‖≤exhaustionRadius (parameters 0) j
    have hh : exhaustionRadius (parameters 0) i≤exhaustionRadius (parameters 0) j := by
      dsimp only [exhaustionRadius]
      gcongr
    exact hx.trans hh
  · have hct : Continuous (fun p : Radial.Plane =>
        c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi) := by
      simp only [markedHeight,planeVector,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop
    exact hct.continuousOn
  · exact fun p hp => tendsto_radial_cubic_exhaustion_area hA hS0 hAB hSB hB hS (hPS hp) hc

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Filter

def squareSqueeze (k : ℝ) (x : Plane) : Plane :=
  (Real.tanh (k*x.1),Real.tanh (k*x.2))

def squeezedDisk (k : ℝ) : Set Plane := squareSqueeze k '' closedRoundDisk 1

theorem tanh_smooth : ContDiff ℝ ∞ Real.tanh := by
  have ht : Real.tanh = fun y => Real.sinh y / Real.cosh y :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [ht]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun y => (Real.cosh_pos y).ne')

theorem tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have ht : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  have he : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  simpa only [← ht,he] using h

theorem squareSqueeze_smooth (k : ℝ) : ContDiff ℝ ∞ (squareSqueeze k) := by
  exact (tanh_smooth.comp (contDiff_const.mul contDiff_fst)).prodMk
    (tanh_smooth.comp (contDiff_const.mul contDiff_snd))

theorem squareSqueeze_injective {k : ℝ} (hk : k ≠ 0) : Injective (squareSqueeze k) := by
  intro x y h
  have ha := Real.tanh_injective (congrArg Prod.fst h)
  have hb := Real.tanh_injective (congrArg Prod.snd h)
  exact Prod.ext (mul_left_cancel₀ hk ha) (mul_left_cancel₀ hk hb)

theorem squareSqueeze_fderiv (k : ℝ) (x v : Plane) :
    fderiv ℝ (squareSqueeze k) x v =
      (k/(Real.cosh (k*x.1))^2*v.1,k/(Real.cosh (k*x.2))^2*v.2) := by
  have h1 := (tanh_hasDerivAt (k*x.1)).comp_hasFDerivAt x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul k)
  have h2 := (tanh_hasDerivAt (k*x.2)).comp_hasFDerivAt x
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).const_mul k)
  change fderiv ℝ (fun z : Plane => (Real.tanh (k*z.1),Real.tanh (k*z.2))) x v = _
  erw [(h1.prodMk h2).fderiv]
  ext <;> simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem squareSqueeze_det_pos {k : ℝ} (hk : 0 < k) (x : Plane) :
    0 < (fderiv ℝ (squareSqueeze k) x).det := by
  rw [planar_det]
  simp only [squareSqueeze_fderiv]
  change 0 < (k/(Real.cosh (k*x.1))^2*1)*(k/(Real.cosh (k*x.2))^2*1) -
    (k/(Real.cosh (k*x.2))^2*0)*(k/(Real.cosh (k*x.1))^2*0)
  simp only [mul_one,mul_zero,sub_zero]
  exact mul_pos (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))
    (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))

theorem squeezedDisk_compact (k : ℝ) : IsCompact (squeezedDisk k) :=
  (closedRoundDisk_isCompact 1).image (squareSqueeze_smooth k).continuous

theorem squeezedDisk_subset (k : ℝ) : squeezedDisk k ⊆ Ioo (-1) 1 ×ˢ Ioo (-1) 1 := by
  rintro _ ⟨x,_,rfl⟩
  exact ⟨⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩,
    ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩⟩

theorem exists_squeezedDisk_contains {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k := by
  let M := max |Real.artanh (-q)| |Real.artanh q|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  let k := 2*(M+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have hb (a : ℝ) (ha : a ∈ Icc (-q) q) : |Real.artanh a| ≤ M := by
    have hlo := Real.artanh_le_artanh (by linarith : -1 < -q) (by linarith [ha.2] : a < 1) ha.1
    have hhi := Real.artanh_le_artanh (by linarith [ha.1] : -1 < a) hq1 ha.2
    apply abs_le.mpr
    constructor
    · exact ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans hlo
    · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))
  refine ⟨k,hk,?_⟩
  intro x hx
  refine ⟨(Real.artanh x.1/k,Real.artanh x.2/k),?_,?_⟩
  · have h1 := hb x.1 hx.1
    have h2 := hb x.2 hx.2
    have hb1 : |Real.artanh x.1/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k]; linarith
    have hb2 : |Real.artanh x.2/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k]; linarith
    change (Real.artanh x.1/k)^2+(Real.artanh x.2/k)^2 ≤ 1^2
    have ha1 := (abs_lt.mp hb1)
    have ha2 := (abs_lt.mp hb2)
    nlinarith [sq_nonneg (Real.artanh x.1/k),sq_nonneg (Real.artanh x.2/k)]
  · ext <;> simp only [squareSqueeze,mul_div_cancel₀ _ hk.ne']
    · exact Real.tanh_artanh ⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩
    · exact Real.tanh_artanh ⟨by linarith [hx.2.1],by linarith [hx.2.2]⟩

def squeezedArea (k : ℝ) : ℝ := (volume (squeezedDisk k)).toReal

theorem squeezedArea_nonneg (k : ℝ) : 0 ≤ squeezedArea k := ENNReal.toReal_nonneg

theorem planar_closed_square_volume {q : ℝ} (hq : 0 ≤ q) :
    volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) = ENNReal.ofReal (4*q^2) := by
  change (volume.prod volume) (Icc (-q) q ×ˢ Icc (-q) q) = _
  rw [Measure.prod_prod,Real.volume_Icc,← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

theorem squeezedArea_le (k : ℝ) : squeezedArea k ≤ 4 := by
  have hm : volume (squeezedDisk k) ≤ volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) :=
    measure_mono (squeezedDisk_subset k)
  have hv : volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) = ENNReal.ofReal 4 := by
    change (volume.prod volume) (Ioo (-1) 1 ×ˢ Ioo (-1) 1) = _
    rw [Measure.prod_prod,Real.volume_Ioo]
    norm_num
  rw [hv] at hm
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4)] using hh

theorem squeezedArea_lower {q k : ℝ} (hq : 0 ≤ q)
    (hsub : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) : 4*q^2 ≤ squeezedArea k := by
  have hm : volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) ≤ volume (squeezedDisk k) :=
    measure_mono hsub
  rw [planar_closed_square_volume hq] at hm
  have hh := ENNReal.toReal_mono (squeezedDisk_compact k).measure_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*q^2)] using hh

theorem exists_rounded_square {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧ 4*q^2 ≤ squeezedArea k ∧ squeezedArea k ≤ 4 := by
  obtain ⟨k,hk,hs⟩ := exists_squeezedDisk_contains hq0.le hq1
  have hl := squeezedArea_lower hq0.le hs
  exact ⟨k,hk,hs,lt_of_lt_of_le (by positivity) hl,hl,squeezedArea_le k⟩

def diagonalScale (a b : ℝ) : Plane →L[ℝ] Plane :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (b • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem diagonalScale_apply (a b : ℝ) (x : Plane) :
    diagonalScale a b x = (a*x.1,b*x.2) := rfl

@[simp] theorem diagonalScale_det (a b : ℝ) : (diagonalScale a b).det = a*b := by
  rw [planar_det]
  simp [planarArea_apply]

def affineRectangle (c : Plane) (a b : ℝ) (x : Plane) : Plane := c + diagonalScale a b x

theorem affineRectangle_image_volume (c : Plane) (a b : ℝ) (S : Set Plane) :
    volume (affineRectangle c a b '' S) = ENNReal.ofReal |a*b| * volume S := by
  change volume (((fun x : Plane => c+x) ∘ diagonalScale a b) '' S) = _
  rw [Set.image_comp]
  simp only [image_add_left,MeasureTheory.measure_preimage_add]
  rw [Measure.addHaar_image_continuousLinearMap]
  change ENNReal.ofReal |(diagonalScale a b).det| * volume S = _
  rw [diagonalScale_det]

theorem affineRectangle_squeezedArea {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : Plane) (k : ℝ) :
    (volume (affineRectangle c a b '' squeezedDisk k)).toReal = a*b*squeezedArea k := by
  rw [affineRectangle_image_volume,ENNReal.toReal_mul,abs_of_nonneg (mul_nonneg ha hb),
    ENNReal.toReal_ofReal (mul_nonneg ha hb)]
  rfl

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_rounded_square_with_control {Y : Set P} (hY : IsCompact Y)
    {F : Plane × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (hbase : ∀ y ∈ Y, F ((1,1),y) ∈ W) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧
      ∀ y ∈ Y, F ((q,4/squeezedArea k),y) ∈ W := by
  have hsub : ({(1,1)} : Set Plane) ×ˢ Y ⊆ F ⁻¹' W := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have he : x = (1,1) := hx
    subst x
    exact hbase y hy
  obtain ⟨U,V,hU,_,h1U,hYV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hY (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h1U rfl))
  have hqcont : ContinuousAt (fun q : ℝ => 1/q^2) 1 :=
    continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
  have hevent : ∀ᶠ q : ℝ in 𝓝 1,
      0 < q ∧ |q-1| < δ ∧ |1/q^2-1| < δ := by
    have ha : ∀ᶠ q : ℝ in 𝓝 1, 0 < q := isOpen_Ioi.mem_nhds (by norm_num)
    have hb : ∀ᶠ q : ℝ in 𝓝 1, |q-1| < δ := by
      filter_upwards [Metric.ball_mem_nhds (1:ℝ) hδ] with q hq
      exact hq
    have hc : ∀ᶠ q : ℝ in 𝓝 1, |1/q^2-1| < δ := by
      have hct : Tendsto (fun q : ℝ => 1/q^2) (𝓝 1) (𝓝 1) := by
        simpa only [one_pow,div_one] using hqcont.tendsto
      filter_upwards [hct.eventually (Metric.ball_mem_nhds (1:ℝ) hδ)] with q hq
      exact hq
    filter_upwards [ha,hb,hc] with q ha hb hc using ⟨ha,hb,hc⟩
  obtain ⟨q,hq,hq1⟩ := ((hevent.filter_mono
    (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  obtain ⟨k,hk,hs,hA,hAl,hAu⟩ := exists_rounded_square hq.1 hq1
  have htlo : 1 ≤ 4/squeezedArea k := (le_div_iff₀ hA).mpr (by simpa using hAu)
  have hthi : 4/squeezedArea k ≤ 1/q^2 := by
    apply (div_le_div_iff₀ hA (sq_pos_of_pos hq.1)).mpr
    simpa using hAl
  have htd : |4/squeezedArea k-1| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr htlo)]
    exact (sub_le_sub_right hthi 1).trans_lt ((le_abs_self _).trans_lt hq.2.2)
  refine ⟨q,k,hq.1,hq1,hk,hs,hA,?_⟩
  intro y hy
  apply hUV ⟨hδU ?_,hYV hy⟩
  rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  exact ⟨by simpa only [Real.dist_eq] using hq.2.1,
    by simpa only [Real.dist_eq] using htd⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
