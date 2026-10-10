import Mathlib
import OAI.Geometry.BallPacking.Toric.CubicRadialProbability
import OAI.Geometry.BallPacking.SurfaceArea.QuadricEndResidueMass

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory

 theorem radialAnnulus_coordinate_bound {r R : ℝ} (hR : 0≤R) {z : Plane}
    (hz : z∈radialAnnulus r R) : |z.1|≤Real.sqrt R ∧ |z.2|≤Real.sqrt R := by
  have hs := Real.sq_sqrt hR
  have hp := Real.sqrt_nonneg R
  have hb := hz.2
  change z.1^2+z.2^2≤R at hb
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

 theorem radialAnnulus_real_volume_le {r R : ℝ} (hR : 0≤R) :
    volume.real (radialAnnulus r R)≤4*R := by
  have hsub : radialAnnulus r R⊆Icc (-Real.sqrt R) (Real.sqrt R) ×ˢ
      Icc (-Real.sqrt R) (Real.sqrt R) := by
    intro z hz
    have he := radialAnnulus_coordinate_bound hR hz
    exact ⟨abs_le.mp he.1,abs_le.mp he.2⟩
  have hv : volume (Icc (-Real.sqrt R) (Real.sqrt R) ×ˢ
      Icc (-Real.sqrt R) (Real.sqrt R) : Set Plane)=ENNReal.ofReal (4*R) := by
    change (volume.prod volume) _=_
    rw [Measure.prod_prod,Real.volume_Icc,←ENNReal.ofReal_mul (by linarith [Real.sqrt_nonneg R])]
    congr 1
    nlinarith [Real.sq_sqrt hR]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans_eq hv)
  simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : 0≤4*R)] using hb

 theorem cutoffWedge_radial_apply {g : ℝ → ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (β : Plane → Plane →L[ℝ] ℝ) :
    cutoffWedge (fun y => g (radiusSq y)) β z=
      2*deriv g (radiusSq z)*(z.1*β z (0,1)-z.2*β z (1,0)) := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  unfold cutoffWedge
  rw [hd]
  simp only [smul_apply,smul_eq_mul,planarDot_apply,mul_one,mul_zero,add_zero,zero_add]
  ring

 theorem cutoffWedge_radial_bound {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane} {r R K M : ℝ} (hg : DifferentiableAt ℝ g (radiusSq z))
    (hR : 0≤R) (hK : 0≤K) (_hM : 0≤M) (hz : z∈radialAnnulus r R)
    (hd : |deriv g (radiusSq z)|≤K) (hβ : ‖β z‖≤M) :
    |cutoffWedge (fun y => g (radiusSq y)) β z|≤4*K*Real.sqrt R*M := by
  have hb0 : |β z (1,0)|≤M := by
    have h := (β z).le_opNorm ((1:ℝ),(0:ℝ))
    simpa only [Real.norm_eq_abs,Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one] using h.trans
      (by simpa using hβ)
  have hb1 : |β z (0,1)|≤M := by
    have h := (β z).le_opNorm ((0:ℝ),(1:ℝ))
    simpa only [Real.norm_eq_abs,Prod.norm_def,norm_one,norm_zero,max_eq_right zero_le_one,mul_one] using h.trans
      (by simpa using hβ)
  have hz' := radialAnnulus_coordinate_bound hR hz
  have hx : |z.1*β z (0,1)|≤Real.sqrt R*M := by
    rw [abs_mul]
    exact mul_le_mul hz'.1 hb1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have hy : |z.2*β z (1,0)|≤Real.sqrt R*M := by
    rw [abs_mul]
    exact mul_le_mul hz'.2 hb0 (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [cutoffWedge_radial_apply hg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hd' := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2)
  calc
    _≤(2*K)*(2*Real.sqrt R*M) :=
      mul_le_mul hd' ((abs_sub _ _).trans (by linarith)) (abs_nonneg _)
        (by positivity)
    _=_ := by ring

 theorem bounded_residue_error_integral {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ∀ z∈radialAnnulus r R,DifferentiableAt ℝ g (radiusSq z))
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ z∈radialAnnulus r R,|deriv g (radiusSq z)|≤K)
    (hβ : ∀ z∈radialAnnulus r R,‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus r R,|d z-c|≤e) :
    |∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      (d z-c)*deriv g (radiusSq z)|≤(4*K*Real.sqrt R*M+e*K)*(4*R) := by
  have hbound (z : Plane) (hz : z∈radialAnnulus r R) :
      ‖cutoffWedge (fun y => g (radiusSq y)) β z-(d z-c)*deriv g (radiusSq z)‖≤
        4*K*Real.sqrt R*M+e*K := by
    rw [Real.norm_eq_abs]
    apply (abs_sub _ _).trans
    apply add_le_add (cutoffWedge_radial_bound (hg z hz) hR hK hM hz (hd z hz) (hβ z hz))
    rw [abs_mul]
    exact mul_le_mul (hc z hz) (hd z hz) (abs_nonneg _) he
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (radialAnnulus_compact r R).measure_lt_top hbound
  exact (show |∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
    (d z-c)*deriv g (radiusSq z)|≤_ from hi).trans
      (mul_le_mul_of_nonneg_left (radialAnnulus_real_volume_le hR) (by positivity))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance boundedPlanarResidueSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

 theorem curveCutoffDefect_variable_coefficient
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ε : Fin m → Bool) {β : Plane → Plane →L[ℝ] ℝ} {d : Plane → ℝ} {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source)
    (he : euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,y)=
      β y-(d y/2) • angularOneForm y) :
    partialChartCoefficient (infinityDiffeomorph a ε)
      (spatialCutoffDefect (curveEndCutoff a g) α) y=
      -cutoffWedge (fun z => g (radiusSq z)) β y+d y*deriv g (radiusSq y) := by
  let A := fun z => euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z)
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [←radiusSq_complex]
    exact ne_of_gt (Complex.normSq_pos.mpr hD.1)
  have hA : DifferentiableAt ℝ A y := by
    have ha := euclideanPullbackOneForm_contDiffAt
      (E := RealModel) (F := Plane) (M := locus a)
      (α := fun _ : ℝ => α) (g := infinityDiffeomorph a ε) (p := (0,y)) hα
      ((infinityDiffeomorph a ε).contMDiffOn.contMDiffAt
        ((infinityDiffeomorph a ε).open_source.mem_nhds hy))
    exact (ha.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hκα : (fun z => curveEndCutoff a g (infinityDiffeomorph a ε z) • A z)=ᶠ[𝓝 y]
      fun z => (1-g (radiusSq z)) • A z := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy] with z hz
    rw [curveEndCutoff_infinity a g ε hz]
  rw [spatialCutoffDefect_coefficient _ (curveEndCutoff_smooth a hg hc) hα hy,
    planarCurl_congr_of_eventuallyEq hκα,curveEndCutoff_infinity a g ε hy]
  have hgs := (hg.differentiable (by simp) (radiusSq y)).comp y
    (radiusSq_hasFDerivAt y).differentiableAt
  change DifferentiableAt ℝ (fun z => g (radiusSq z)) y at hgs
  have hrs := (differentiableAt_const (c := (1:ℝ))).sub hgs
  change DifferentiableAt ℝ (fun z => 1-g (radiusSq z)) y at hrs
  rw [planarCurl_spatial_smul hrs hA,add_sub_cancel_right]
  have hd := (hasFDerivAt_const (1:ℝ) y).sub hgs.hasFDerivAt
  change HasFDerivAt (fun z => 1-g (radiusSq z)) _ y at hd
  have ha : A y=β y-(d y/2) • angularOneForm y := he
  have hw : cutoffWedge (fun z => 1-g (radiusSq z)) A y=
      -cutoffWedge (fun z => g (radiusSq z)) β y+
        (d y/2)*cutoffWedge (fun z => g (radiusSq z)) angularOneForm y := by
    unfold cutoffWedge
    rw [hd.fderiv,ha]
    simp only [sub_apply,smul_apply,zero_apply,smul_eq_mul]
    ring
  rw [hw,cutoffWedge_radial_angular (hg.differentiable (by simp) _) hz]
  ring

 theorem curveCutoff_variable_flux_partition
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {I : Type*} [Fintype I] {K : Set (locus a)} (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκK : tsupport (curveEndCutoff a g)⊆K)
    (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K)
    (d : (Fin m → Bool) → Plane → ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (he : ∀ ε, ∀ y∈radialAnnulus r R,
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,y)=
        β ε y-(d ε y/2) • angularOneForm y) :
    partitionFormMass B ρ (fun x => curveEndCutoff a g x • manifoldExteriorOneForm α x)=
      ∑ ε : Fin m → Bool,∫ z in radialAnnulus r R,
        cutoffWedge (fun y => g (radiusSq y)) (β ε) z-d ε z*deriv g (radiusSq z) := by
  have hκ := curveEndCutoff_smooth a hg hc
  have hzκ (x : locus a) (hx : x∉K) : curveEndCutoff a g x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hκK hh))
  rw [partitionFormMass_cutoff_defect (positivePlaneTransitions a) hK B ρ hρ hκ hα hzκ]
  have hd := partitionFormMass_finite_disjoint_charts hK (infinityDiffeomorph a)
    (infinityDiffeomorph_positive a)
    (fun i j hij => by simpa only [infinityDiffeomorph_target] using infinityBranch_disjoint a hij)
    (fun ε => curveEndAnnulus a ε r R) (curveEndAnnulus_compact a hr hR) hSK
    (curveEndAnnulus_subset_target a hr hR) B ρ hρ
    (spatialCutoffDefect_smooth hκ hα) (spatialCutoffDefect_skew _ _)
    (fun x hx => by
      obtain ⟨b,hb⟩ := curveEndCutoff_locally_constant_off_annuli a hc hr hR h1 h0 hx
      exact spatialCutoffDefect_zero_of_locally_constant hα hb)
  rw [hd,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ε _
  rw [curveEndAnnulus_coordinates a hr hR ε,←integral_neg]
  apply setIntegral_congr_fun (radialAnnulus_compact r R).measurableSet
  intro y hy
  dsimp only
  rw [curveCutoffDefect_variable_coefficient a α hα hg hc ε
    (radialAnnulus_in_end a hr hR ε hy) (he ε y hy)]
  ring

 theorem curveCutoff_variable_flux_mass
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hd : manifoldExteriorOneForm α=Ω)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκc : HasCompactSupport (curveEndCutoff a g))
    (d : (Fin m → Bool) → Plane → ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (he : ∀ ε, ∀ y∈radialAnnulus r R,
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,y)=
        β ε y-(d ε y/2) • angularOneForm y) :
    surfaceCutoffMass hκc Ω=
      ∑ ε : Fin m → Bool,∫ z in radialAnnulus r R,
        cutoffWedge (fun y => g (radiusSq y)) (β ε) z-d ε z*deriv g (radiusSq z) := by
  let K := tsupport (curveEndCutoff a g)∪⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R
  have hK : IsCompact K := hκc.union (isCompact_iUnion (curveEndAnnulus_compact a hr hR))
  let B := fun b : compactSurfaceBoxes hK => b.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  rw [surfaceCutoffMass_eq (positivePlaneTransitions a) B ρ hρ hκc subset_union_left
    (curveEndCutoff_smooth a hg hc) hΩ hsk,←hd]
  exact curveCutoff_variable_flux_partition a α hα hK B ρ hρ hg hc hr hR h1 h0
    subset_union_left (fun ε => (subset_iUnion (curveEndAnnulus a · r R) ε).trans subset_union_right)
    d β he

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem integral_annular_radial_derivative {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    (∫ z in radialAnnulus r R,c*deriv g (radiusSq z))= -c*Real.pi := by
  have h := integral_planar_residue_annulus hg hc hr h1 h0
    (β := fun _ : Plane => (0 : Plane →L[ℝ] ℝ)) contDiff_const c
  simpa [cutoffWedge,planarCurl] using h

 theorem continuousOn_cutoffWedge_radial {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {U : Set Plane} (hg : ContDiff ℝ ∞ g) (hβ : ContinuousOn β U) :
    ContinuousOn (cutoffWedge (fun y => g (radiusSq y)) β) U := by
  have hs : ContDiff ℝ ∞ (fun y => g (radiusSq y)) := hg.comp radiusSq_smooth
  unfold cutoffWedge
  exact (((hs.fderiv_right (m := ∞) (by simp)).continuous.continuousOn.clm_apply continuousOn_const).mul
    (hβ.clm_apply continuousOn_const)).sub
    (((hs.fderiv_right (m := ∞) (by simp)).continuous.continuousOn.clm_apply continuousOn_const).mul
    (hβ.clm_apply continuousOn_const))

 theorem variable_flux_error_bound {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hβc : ContinuousOn β (radialAnnulus r R)) (hdc : ContinuousOn d (radialAnnulus r R))
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ z∈radialAnnulus r R,|deriv g (radiusSq z)|≤K)
    (hβ : ∀ z∈radialAnnulus r R,‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus r R,|d z-c|≤e) :
    |(∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      d z*deriv g (radiusSq z))-c*Real.pi|≤(4*K*Real.sqrt R*M+e*K)*(4*R) := by
  have hder : ContinuousOn (fun z => deriv g (radiusSq z)) (radialAnnulus r R) :=
    ((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).continuousOn
  have hi1 : IntegrableOn (fun z => cutoffWedge (fun y => g (radiusSq y)) β z-
      d z*deriv g (radiusSq z)) (radialAnnulus r R) volume :=
    ((continuousOn_cutoffWedge_radial hg hβc).sub (hdc.mul hder)).integrableOn_compact
    (radialAnnulus_compact r R)
  have hi2 : IntegrableOn (fun z => c*deriv g (radiusSq z)) (radialAnnulus r R) volume :=
    (continuousOn_const.mul hder).integrableOn_compact (radialAnnulus_compact r R)
  have heq : (∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      (d z-c)*deriv g (radiusSq z))=
      (∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
        d z*deriv g (radiusSq z))-c*Real.pi := by
    have hf : (fun z => cutoffWedge (fun y => g (radiusSq y)) β z-(d z-c)*deriv g (radiusSq z))=
      fun z => (cutoffWedge (fun y => g (radiusSq y)) β z-d z*deriv g (radiusSq z))+
        c*deriv g (radiusSq z) := by funext z; ring
    rw [hf,integral_add hi1 hi2,integral_annular_radial_derivative hg hgc hr h1 h0]
    ring
  rw [←heq]
  exact bounded_residue_error_integral (fun z _ => hg.differentiable (by simp) _) hR hK hM he hd hβ hc

 theorem shrinkingCutoff_tsupport_scaled {g : ℝ → ℝ} {R : ℝ}
    (h0 : tsupport g⊆Iic R) (n : ℕ) :
    tsupport (shrinkingCutoff g n)⊆Iic (R/((n:ℝ)+1)) := by
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have htR : R<((n:ℝ)+1)*t := by
    have h := (div_lt_iff₀ (by positivity : 0<(n:ℝ)+1)).mp (lt_of_not_ge hn)
    linarith
  change g (((n:ℝ)+1)*t)≠0 at ht
  exact ht (image_eq_zero_of_notMem_tsupport (f := g) (fun hx => not_le_of_gt htR (h0 hx)))

 theorem shrinkingCutoff_deriv {g : ℝ → ℝ} (hg : Differentiable ℝ g) (n : ℕ) (t : ℝ) :
    deriv (shrinkingCutoff g n) t=((n:ℝ)+1)*deriv g (((n:ℝ)+1)*t) := by
  have h := (hg _).hasDerivAt.comp t ((hasDerivAt_id t).const_mul ((n:ℝ)+1))
  change deriv (fun y => g (((n:ℝ)+1)*y)) t=_
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using h.deriv

 theorem shrinking_variable_flux_error {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ t : ℝ,|deriv g t|≤K) (n : ℕ)
    (hβc : ContinuousOn β (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ContinuousOn d (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),|d z-c|≤e) :
    |(∫ z in radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),
      cutoffWedge (fun y => shrinkingCutoff g n (radiusSq y)) β z-
        d z*deriv (shrinkingCutoff g n) (radiusSq z))-c*Real.pi|≤
      16*K*R*M*Real.sqrt (R/((n:ℝ)+1))+4*e*K*R := by
  have hn : 0<(n:ℝ)+1 := by positivity
  have hb := variable_flux_error_bound (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n)
    (div_pos hr hn) (shrinkingCutoff_one h1 n) (shrinkingCutoff_tsupport_scaled h0 n)
    hβc hdc (div_nonneg hR hn.le) (mul_nonneg hn.le hK) hM he
    (K := ((n:ℝ)+1)*K)
    (fun z _ => by
      rw [shrinkingCutoff_deriv (hg.differentiable (by simp)),abs_mul,abs_of_pos hn]
      exact mul_le_mul_of_nonneg_left (hd _) hn.le) hβ hc
  convert hb using 1
  field_simp [hn.ne']
  ring

 theorem tendsto_shrinking_variable_flux {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M c : ℝ} {e : ℕ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : ∀ n,0≤e n)
    (het : Tendsto e atTop (𝓝 0)) (hd : ∀ t : ℝ,|deriv g t|≤K)
    (hβc : ∀ n : ℕ,ContinuousOn β (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ∀ n : ℕ,ContinuousOn d (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → ‖β z‖≤M)
    (hc : ∀ (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → |d z-c|≤e n) :
    Tendsto (fun n : ℕ => ∫ z in radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),
      cutoffWedge (fun y => shrinkingCutoff g n (radiusSq y)) β z-
        d z*deriv (shrinkingCutoff g n) (radiusSq z)) atTop (𝓝 (c*Real.pi)) := by
  have hRt : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n : ℕ => 16*K*R*M*Real.sqrt (R/((n:ℝ)+1))+4*e n*K*R)
      atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := 16*K*R*M)).mul hRt.sqrt).add
      (((tendsto_const_nhds (x := (4:ℝ))).mul het).mul_const K |>.mul_const R)
    simpa only [Real.sqrt_zero,mul_zero,zero_mul,add_zero] using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [Real.norm_eq_abs]
  exact shrinking_variable_flux_error hg hgc hr h1 h0 hR hK hM (he n) hd n
    (hβc n) (hdc n) (hβ n) (hc n)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance boundedResidueLimitSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

 theorem tendsto_curveCutoff_bounded_residue
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hαΩ : manifoldExteriorOneForm α=Ω)
    {g : ℝ → ℝ} {r R K M : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hK : 0≤K) (hM : 0≤M) (hdg : ∀ t : ℝ,|deriv g t|≤K)
    (c : (Fin m → Bool) → ℝ) (e : ℕ → ℝ) (he : ∀ n,0≤e n) (het : Tendsto e atTop (𝓝 0))
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (d : (Fin m → Bool) → Plane → ℝ)
    (hβc : ∀ ε (n : ℕ),ContinuousOn (β ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ∀ ε (n : ℕ),ContinuousOn (d ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → ‖β ε z‖≤M)
    (hd : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → |d ε z-c ε|≤e n)
    (hdecomp : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) →
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z)=
        β ε z-(d ε z/2) • angularOneForm z) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω)
      atTop (𝓝 ((∑ ε : Fin m → Bool,c ε)*Real.pi)) := by
  have hmass (n : ℕ) : surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω=
      ∑ ε : Fin m → Bool,∫ z in radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),
        cutoffWedge (fun y => shrinkingCutoff g n (radiusSq y)) (β ε) z-
          d ε z*deriv (shrinkingCutoff g n) (radiusSq z) := by
    have hRn : {s : ℂ | Complex.normSq s≤R/((n:ℝ)+1)}⊆infinityRegion a := by
      intro s hs
      apply hR
      exact hs.trans (div_le_self hRp (by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith))
    exact curveCutoff_variable_flux_mass a α hα Ω hΩ hsk hαΩ
      (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n)
      (div_pos hr (by positivity)) hRn (shrinkingCutoff_one h1 n)
      (shrinkingCutoff_tsupport_scaled h0 n) _ d β (fun ε z hz => hdecomp ε n z hz)
  simp_rw [hmass]
  rw [Finset.sum_mul]
  apply tendsto_finsetSum
  intro ε _
  exact tendsto_shrinking_variable_flux hg hgc hr h1 h0 hRp hK hM he het hdg
    (hβc ε) (hdc ε) (hβ ε) (hd ε)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open Set Filter
open scoped Topology

 def logarithmicError (C R : ℝ) (n : ℕ) : ℝ := C/(-Real.log (R/((n:ℝ)+1)))

 theorem logarithmicError_nonneg {C R : ℝ} (hC : 0≤C) (hR : 0<R) (hR1 : R<1) (n : ℕ) :
    0≤logarithmicError C R n := by
  have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact div_nonneg hC (neg_pos.mpr (Real.log_neg (div_pos hR (by positivity))
    ((div_le_self hR.le hn).trans_lt hR1))).le

 theorem logarithmicError_bound {C R t : ℝ} (hC : 0≤C) (hR : 0<R) (hR1 : R<1)
    (n : ℕ) (ht : 0<t) (htR : t≤R/((n:ℝ)+1)) :
    C/(-Real.log t)≤logarithmicError C R n := by
  have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hb : 0< -Real.log (R/((n:ℝ)+1)) := neg_pos.mpr (Real.log_neg
    (div_pos hR (by positivity)) ((div_le_self hR.le hn).trans_lt hR1))
  exact div_le_div_of_nonneg_left hC hb (neg_le_neg (Real.log_le_log ht htR))

 theorem tendsto_logarithmicError {R : ℝ} (hR : 0<R) (C : ℝ) :
    Tendsto (logarithmicError C R) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have htp : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun n => div_pos hR (by positivity))⟩
  exact tendsto_const_nhds.div_atTop (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp htp))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

local instance boundedPlanarResidueBaseCurveSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

 theorem sum_limitingEndOrder (D S : ℝ) (p : MomentPlane) :
    (∑ ε : EndIndex,limitingEndOrder D S p ε)=3*(D-3*(p 0+p 1))-2*markedHeight S p := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp (fun ε => limitingEndOrder D S p ε)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,limitingEndOrder,
    finTwoArrowEquiv_symm_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Bool.false_eq_true,↓reduceIte]
  ring

 theorem tendsto_reduced_cubic_cutoff_mass {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : MomentPlane} (hp : p∈openTrapezoid A B)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0<R) (hR1 : R<1)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
      (reducedForm (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p 0+p 1))-2*markedHeight S p)*Real.pi)) := by
  obtain ⟨Mlog,hMlog,hlog⟩ := exists_regularCoefficient_log_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) hR
  obtain ⟨M,hM,hbound⟩ := exists_regularPrimitive_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) c hR
  obtain ⟨K,hK⟩ := (hg.continuous_deriv (by simp)).bounded_above_of_compact_support hgc.deriv
  have hK0 : 0≤K := (norm_nonneg (deriv g 0)).trans (hK 0)
  have hKg (t : ℝ) : |deriv g t|≤K := by simpa only [Real.norm_eq_abs] using hK t
  have hs := trapezoidWeight_surrounds hAB hp
  have hpoint (ε : EndIndex) (n : ℕ) (y : Plane)
      (hy : y∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))) :
      y∈(infinityDiffeomorph (parameters 0) ε).source ∧
      Complex.equivRealProdCLM.symm y∈endRegularRegion ∧
      y∈radialAnnulus 0 R ∧ 0<radiusSq y ∧ radiusSq y<1 := by
    have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hys : y∈radialAnnulus 0 R := ⟨radiusSq_nonneg _,hy.2.trans (div_le_self hRp.le hn)⟩
    have hxR : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hys.2
    have hRI : {s : ℂ | Complex.normSq s≤R/((n:ℝ)+1)}⊆infinityRegion (parameters 0) :=
      fun s hs => (hR (hs.trans (div_le_self hRp.le hn))).1
    exact ⟨radialAnnulus_in_end (parameters 0) (div_pos hr (by positivity)) hRI ε hy,
      hxR,hys,(div_pos hr (by positivity)).trans_le hy.1,hys.2.trans_lt hR1⟩
  have ht := tendsto_curveCutoff_bounded_residue (parameters 0)
    (reducedPrimitive (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)
    (reducedPrimitive_smooth _ _ c hs)
    (reducedForm (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)
    (reducedForm_smooth _ _ c hs) (reducedForm_skew _ _ _ c p) rfl
    hg hgc hr hRp.le (fun s hs => (hR hs).1) h1 h0 hK0 hM hKg
    (fun ε => c*limitingEndOrder D S p ε)
    (logarithmicError (|c| * (2*Mlog+Fintype.card (TrapezoidWeight A B))) R)
    (fun n => logarithmicError_nonneg (by positivity) hRp hR1 n)
    (tendsto_logarithmicError hRp _)
    (reducedEndRegularPrimitive (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)
    (reducedEndResidue (trapezoidWeight A B) (cubicDegree D) (cubicMarkedOrder S) c p)
    (fun ε n y hy => (reducedEndRegularPrimitive_contDiffAt _ _ c hs ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1).continuousAt.continuousWithinAt)
    (fun ε n y hy => (reducedEndResidue_contDiffAt _ _ c hs ε
      (hpoint ε n y hy).1).continuousAt.continuousWithinAt)
    (fun ε n y hy => reducedEndRegularPrimitive_norm_le _ _ _ c p ε y
      (fun k => hbound k ε y (hpoint ε n y hy).2.2.1))
    (fun ε n y hy => by
      have hh := reducedEndResidue_error hA hS0 hAB hSB hB hS hp ε
        (hpoint ε n y hy).1 (hpoint ε n y hy).2.1
        (hpoint ε n y hy).2.2.2.1 (hpoint ε n y hy).2.2.2.2 hMlog
        (fun k => hlog k ε y (hpoint ε n y hy).2.2.1) c
      apply hh.trans
      rw [←mul_div_assoc]
      exact logarithmicError_bound (by positivity) hRp hR1 n (hpoint ε n y hy).2.2.2.1 hy.2)
    (fun ε n y hy => reducedPrimitive_infinity
      (trapezoidWeight A B) (fun k => (cubicMarked_lt_degree hB hS k).le)
      (fun k => cubicMarked_twice_complement hB hS k) c p ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1)
  rw [←Finset.mul_sum] at ht
  rw [sum_limitingEndOrder] at ht
  exact ht

end PackingSufficiencySupport.CubicModel
end

end OAI
