import OAI.Analysis.NodalLength.InteriorMass

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace

namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.plain_upper {Ω : Set Plane} {S : ℕ → ℝ} {U : ℕ → Plane → ℝ} {W : Plane → EReal}
    (h : WeightedProfileBounds Ω S 0 U 1 W) {F : Set Plane} (hF : IsCompact F) (hFΩ : F⊆Ω) :
    limsup (fun j=>logRate (S j) (plainMass (U j) F)) atTop≤⨆x∈F,W x := by
  simpa only [Pi.zero_apply,Pi.one_apply,EReal.coe_zero,add_zero,←plainMass_tilted] using
    h.upper 0 continuousOn_const F hF hFΩ
lemma WeightedProfileBounds.plain_lower {Ω : Set Plane} {S : ℕ → ℝ} {U : ℕ → Plane → ℝ} {W : Plane → EReal}
    (h : WeightedProfileBounds Ω S 0 U 1 W) {G : Set Plane} (hG : IsOpen G) (hGΩ : G⊆Ω) :
    (⨆x∈G,W x)≤liminf (fun j=>logRate (S j) (plainMass (U j) G)) atTop := by
  simpa only [Pi.zero_apply,Pi.one_apply,EReal.coe_zero,add_zero,←plainMass_tilted] using
    h.lower 0 continuousOn_const G hG hGΩ

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
lemma local_profile_le_sup {Ω : Set Plane} (hΩ : IsOpen Ω)
    {e : OpenPartialHomeomorph X Plane} (hΩe : Ω⊆e.target)
    {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal} {W : Plane → EReal}
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    (hprofile : WeightedProfileBounds Ω S 0 (fun j=>u j ∘ e.symm) 1 W)
    {y : Plane} (hy : y∈Ω) : W y≤basisProfile ell (e.symm y) := by
  by_contra hn
  obtain ⟨a,hVa,haW⟩:=EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨b,hab,hbW⟩:=EReal.lt_iff_exists_real_btwn.mp haW
  obtain ⟨G,hG,hxG,hbound⟩:=supProfile_lt_local hSpos hlim hVa
  have hopen : IsOpen (Ω∩(e.target∩e.symm ⁻¹' G)):=hΩ.inter (e.isOpen_inter_preimage_symm hG)
  have hyH : y∈Ω∩(e.target∩e.symm ⁻¹' G):=⟨hy,hΩe hy,hxG⟩
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hopen y hyH
  have hlower:=hprofile.plain_lower isOpen_ball (fun z hz=>(hball hz).1)
  have hbmass := eventually_lt_of_lt_liminf (hbW.trans_le ((le_iSup₂_of_le y (mem_ball_self hr) le_rfl).trans hlower))
  let C:=1+volume.real (ball y r)
  have hC : 0<C:=by dsimp [C]; positivity
  have hvol : volume (ball y r)≤ENNReal.ofReal C := by
    rw [←ENNReal.ofReal_toReal (measure_ball_ne_top (μ:=volume) (x:=y) (r:=r))]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C,measureReal_def]; linarith
  have hcomp : ∀j,plainMass (u j ∘ e.symm) (ball y r)≤ENNReal.ofReal C*supMass (u j) G := by
    intro j
    calc
      _ ≤ ∫⁻z in ball y r,supMass (u j) G := setLIntegral_mono' measurableSet_ball (fun z hz=>le_iSup₂_of_le (e.symm z) (hball hz).2.2 le_rfl)
      _ = volume (ball y r)*supMass (u j) G := by simp [mul_comm]
      _ ≤ _ := mul_le_mul' hvol le_rfl
  apply no_exponential_gap hS (EReal.coe_lt_coe_iff.mp hab) hC hbound _ (Eventually.of_forall hcomp)
  filter_upwards [hbmass] with j hj
  exact ((lt_logRate_iff (hSpos j) _).mp hj).le

lemma sup_profile_le_local {Ω : Set Plane} (hΩ : IsOpen Ω)
    {e : OpenPartialHomeomorph X Plane} (hΩe : Ω⊆e.target)
    {u : ℕ → X → ℝ} {p : ℕ → Plane → ℝ} {S K : ℕ → ℝ} {Cp : ℝ}
    {ell : countableBasis X → EReal} {W : Plane → EReal}
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop) (hK : ∀ᶠj in atTop,|K j|≤S j)
    (hCp : 0≤Cp)
    (hU : ∀j,ContDiffOn ℝ ∞ (u j ∘ e.symm) Ω) (hp : ∀j,ContDiffOn ℝ ∞ (p j) Ω)
    (he : ∀j x,x∈Ω → euclideanLaplacian (u j ∘ e.symm) x+(K j)^2*p j x*u j (e.symm x)=0)
    (hb : ∀j x,x∈Ω → |p j x|≤Cp)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    (hW : UpperSemicontinuous W)
    (hprofile : WeightedProfileBounds Ω S 0 (fun j=>u j ∘ e.symm) 1 W)
    {y : Plane} (hy : y∈Ω) : basisProfile ell (e.symm y)≤W y := by
  by_contra hn
  obtain ⟨a,hWa,haV⟩:=EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨b,hab,hbV⟩:=EReal.lt_iff_exists_real_btwn.mp haV
  have hab' : a<b:=EReal.coe_lt_coe_iff.mp hab
  obtain ⟨t,ht,htH⟩:=Metric.isOpen_iff.mp (hΩ.inter (hW.isOpen_preimage (a:EReal))) y ⟨hy,hWa⟩
  let r:=t/4
  have hr : 0<r:=by dsimp [r]; positivity
  have hF : closedBall y (3*r)⊆Ω∩W ⁻¹' Iio (a:EReal) :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans htH
  obtain ⟨C,hC,hCb⟩:=local_sup_mass hΩ hr hCp (ball_subset_closedBall.trans (fun z hz=>(hF hz).1))
  let a':=(a+b)/2
  have haa' : a<a':=by dsimp [a']; linarith
  have ha'b : a'<b:=by dsimp [a']; linarith
  have hupper:=hprofile.plain_upper (isCompact_closedBall y (3*r)) (fun z hz=>(hF hz).1)
  have hsup : (⨆z∈closedBall y (3*r),W z)≤(a:EReal):=iSup_le fun z=>iSup_le fun hz=>(hF hz).2.le
  have hevmass:=eventually_lt_of_limsup_lt (hupper.trans_lt (hsup.trans_lt (EReal.coe_lt_coe_iff.mpr haa')))
  let D:=C*(1+r^2*Cp)^2
  have hD : 0<D:=by dsimp [D]; positivity
  have hpoly:=polynomial_exponential_gap hS ha'b hD 4
  have hsbound : ∀ᶠj in atTop,supMass (u j ∘ e.symm) (ball y (2*r))≤ENNReal.ofReal (Real.exp (2*S j*b)) := by
    filter_upwards [hevmass,hpoly,hK,hS.eventually (eventually_ge_atTop 1)] with j hj hpj hKj hSj
    have hSj0 : 0≤S j:=by linarith
    have hK2 : (K j)^2≤(S j)^2:=by nlinarith [sq_abs (K j),abs_nonneg (K j)]
    have hcoeff : 1+r^2*(K j)^2*Cp≤(1+r^2*Cp)*(S j)^2 := by
      have hh:=mul_le_mul_of_nonneg_left hK2 (by positivity : 0≤r^2*Cp)
      nlinarith [sq_nonneg (S j-1)]
    have hcoeff0 : 0≤1+r^2*(K j)^2*Cp:=by positivity
    have hc2 : C*(1+r^2*(K j)^2*Cp)^2≤D*(S j)^4 := by
      have hh:=(sq_le_sq₀ hcoeff0 (by positivity)).mpr hcoeff
      have hh':=mul_le_mul_of_nonneg_left hh hC.le
      dsimp [D]; nlinarith only [hh']
    calc
      _ ≤ ENNReal.ofReal (C*(1+r^2*(K j)^2*Cp)^2)*plainMass (u j ∘ e.symm) (closedBall y (3*r)):=hCb _ _ _ (hU j) (hp j) (he j) (hb j)
      _ ≤ ENNReal.ofReal (D*(S j)^4)*ENNReal.ofReal (Real.exp (2*S j*a')):=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc2) ((logRate_lt_iff (hSpos j) _).mp hj).le
      _ ≤ _ := by rw [←ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_le_ofReal hpj
  have hlocal : SupLocalBound u S (e.symm y) b := by
    refine ⟨e.source∩e ⁻¹' ball y (2*r),e.isOpen_inter_preimage isOpen_ball,?_,?_⟩
    · exact ⟨e.map_target (hΩe hy),by rw [mem_preimage,e.right_inv (hΩe hy)]; exact mem_ball_self (by positivity)⟩
    · filter_upwards [hsbound] with j hj
      apply (supMass_le.mpr ?_).trans hj
      intro x hx
      have hv : u j x=(u j ∘ e.symm) (e x):=by rw [Function.comp_apply,e.left_inv hx.1]
      rw [hv]
      exact le_iSup₂_of_le (e x) hx.2 le_rfl
  exact (not_le_of_gt hbV) (supProfile_le_of_local hSpos hlim hlocal)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma IsConformal.exists_profile_ball {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} (hy : y∈e.target) : ∃r Cp : ℝ,0<r ∧ 0≤Cp ∧
      closedBall y r⊆e.target ∧ volume (ball y r)≤1 ∧
      (∀z∈ball y r,|conformalFactor e z|≤Cp) ∧
      (∀i z,z∈ball y r → |coordPartial (conformalFactor e) i z|≤Cp) := by
  obtain ⟨t,ht,hball⟩:=Metric.isOpen_iff.mp e.open_target y hy
  let r:=min (t/2) (1/4)
  have hr : 0<r:=lt_min (by positivity) (by norm_num)
  have hrt : r<t:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr4 : r≤1/4:=min_le_right _ _
  have hc : closedBall y r⊆e.target:=(closedBall_subset_ball hrt).trans hball
  have hp:=he.factor_smooth
  have hpi (i : Fin 2) : ContinuousOn (coordPartial (conformalFactor e) i) e.target := by
    intro z hz
    exact (smoothAt_partial (hp.contDiffAt (e.open_target.mem_nhds hz)) i).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn (hp.continuousOn.mono hc)
  obtain ⟨B0,hB0⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 0).mono hc)
  obtain ⟨B1,hB1⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 1).mono hc)
  let Cp:=|B|+|B0|+|B1|
  refine ⟨r,Cp,hr,by dsimp [Cp]; positivity,hc,?_,?_,?_⟩
  · rw [EuclideanSpace.volume_ball_fin_two,←ENNReal.ofReal_pow hr.le,←ENNReal.ofReal_mul (sq_nonneg r)]
    apply ENNReal.ofReal_le_one.mpr
    have hh:=Real.pi_lt_four
    nlinarith
  · intro z hz
    have hb:=hB z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at hb
    dsimp [Cp]; linarith [le_abs_self B,abs_nonneg B0,abs_nonneg B1]
  · intro i z hz
    fin_cases i
    · have hb:=hB0 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B0,abs_nonneg B,abs_nonneg B1]
    · have hb:=hB1 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B1,abs_nonneg B,abs_nonneg B0]

variable [SecondCountableTopology M]
lemma sup_profile_local_zero {u : ℕ → M → ℝ} {K S : ℕ → ℝ}
    {ell : TopologicalSpace.countableBasis M → EReal}
    (hu : ∀j,ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ (u j))
    (hPDE : ∀j x,-laplaceBeltrami (u j) x=(K j)^2*u j x)
    (hnorm : ∀j x,|u j x|≤1)
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hKS : Tendsto (fun j=>K j/S j) atTop (𝓝 0))
    (hlim : ∀i : TopologicalSpace.countableBasis M,
      Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {x : M} (hx : basisProfile ell x=0) :
    ∃G : Set M,IsOpen G ∧ x∈G ∧ ∀z∈G,basisProfile ell z=0 := by
  obtain ⟨e,hxE,he⟩:=exists_isothermal_chart x
  let y:=e x
  have hy : y∈e.target:=e.map_source hxE
  obtain ⟨r,Cp,hr,hCp,hclose,hvol,hpbound,hgrad⟩:=he.exists_profile_ball hy
  let Ω:=ball y r
  have hΩe : Ω⊆e.target:=ball_subset_closedBall.trans hclose
  let U:=fun j=>u j ∘ e.symm
  let p:=conformalFactor e
  have hU (j : ℕ) : ContDiffOn ℝ ∞ (U j) Ω:= (he.eigenfunction (hu j) (hPDE j)).1.mono hΩe
  have hp : ContDiffOn ℝ ∞ p Ω:=he.factor_smooth.mono hΩe
  have heq (j : ℕ) (z : Plane) (hz:z∈Ω) : euclideanLaplacian (U j) z+(K j)^2*p z*U j z=0 :=
    (he.eigenfunction (hu j) (hPDE j)).2 z (hΩe hz)
  have hnorm' (j : ℕ) : tiltedMass (S j) 0 (U j) 1 0 Ω≤1 := by
    rw [←plainMass_tilted]
    apply (plainMass_le_sup _ _ measurableSet_ball).trans
    have hs : supMass (U j) Ω≤1 := supMass_le.mpr (fun z _=>
      (ENNReal.ofReal_le_ofReal ((sq_le_one_iff_abs_le_one _).mpr (hnorm j (e.symm z)))).trans_eq ENNReal.ofReal_one)
    simpa only [mul_one] using mul_le_mul' hvol hs
  obtain ⟨W,φ,hφ,hW,hWneg,hprofile⟩:=extract_tilted_profile isOpen_ball S 0 U 1 hSpos hS
    (fun j=>(hU j).continuousOn) hnorm'
  have hprofile' : WeightedProfileBounds Ω (S∘φ) 0 (U∘φ) 1 W := by
    convert hprofile using 1 <;> funext j <;> rfl
  have hφSpos (j : ℕ) : 0<(S∘φ) j:=hSpos (φ j)
  have hφS : Tendsto (S∘φ) atTop atTop:=hS.comp hφ.tendsto_atTop
  have hφlim (i : TopologicalSpace.countableBasis M) :
      Tendsto (fun j=>logRate ((S∘φ) j) (supMass (u (φ j)) i.val)) atTop (𝓝 (ell i)) :=
    (hlim i).comp hφ.tendsto_atTop
  have hKle : ∀ᶠj in atTop,|K (φ j)|≤S (φ j) := by
    have hh:=((hKS.abs).comp hφ.tendsto_atTop).eventually_le_const (by norm_num : |(0:ℝ)|<1)
    filter_upwards [hh] with j hj
    change |K (φ j)/S (φ j)|≤1 at hj
    rw [abs_div,abs_of_pos (hSpos (φ j)),div_le_one (hSpos (φ j))] at hj
    exact hj
  have hEq (z : Plane) (hz:z∈Ω) : W z=basisProfile ell (e.symm z) := by
    apply le_antisymm
    · exact local_profile_le_sup isOpen_ball hΩe hφSpos hφS hφlim hprofile' hz
    · exact sup_profile_le_local isOpen_ball hΩe hφSpos hφS hKle hCp
        (fun j=>hU (φ j)) (fun _=>hp) (fun j=>heq (φ j)) (fun _=>hpbound)
        hφlim hW hprofile' hz
  have herror : Tendsto (fun j=>Cp*(K (φ j)/S (φ j))^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((hKS.comp hφ.tendsto_atTop).pow 2))
  have htest : FullTestProperty Ω W := by
    apply full_test_of_profile (B:=0) (c:=1) isOpen_ball (fun _=>hp) (fun j=>hU (φ j)) hφSpos hφS (fun _=>by norm_num)
      (K:=K∘φ) (e:=fun j=>Cp*(K (φ j)/S (φ j))^2)
    · simp only [Pi.zero_apply,norm_zero,add_zero]
      exact hKS.comp hφ.tendsto_atTop
    · exact fun _=>hpbound
    · exact herror
    · intro j i z hz
      simp only [Pi.zero_apply,norm_zero,add_zero,Function.comp_apply]
      rw [abs_div,abs_mul,abs_sq,abs_of_pos (mul_pos (hSpos (φ j)) (hSpos (φ j)))]
      have hg:=hgrad i z hz
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (sq_nonneg _)) (mul_nonneg (hSpos (φ j)).le (hSpos (φ j)).le)).trans_eq
      ring
    · exact fun j=>heq (φ j)
    · exact hW.upperSemicontinuousOn _
    · exact hprofile'
  have hWy : W y=0:=by rw [hEq y (mem_ball_self hr),e.left_inv hxE,hx]
  have hzero:=profile_strong_maximum isOpen_ball (convex_ball y r).isPreconnected hW (fun z _=>hWneg z)
    htest (mem_ball_self hr) hWy
  refine ⟨e.source∩e ⁻¹' Ω,e.isOpen_inter_preimage isOpen_ball,⟨hxE,mem_ball_self hr⟩,?_⟩
  intro z hz
  have ht:=hzero (e z) hz.2
  rw [hEq (e z) hz.2,e.left_inv hz.1] at ht
  exact ht

lemma global_sup_profile_zero [CompactSpace M] [ConnectedSpace M]
    {u : ℕ → M → ℝ} {K S : ℕ → ℝ} {ell : TopologicalSpace.countableBasis M → EReal}
    (hu : ∀j,ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ (u j))
    (hPDE : ∀j x,-laplaceBeltrami (u j) x=(K j)^2*u j x)
    (hnorm : ∀j x,|u j x|≤1) (hmax : ∀j,∃x,|u j x|=1)
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hKS : Tendsto (fun j=>K j/S j) atTop (𝓝 0))
    (hlim : ∀i : TopologicalSpace.countableBasis M,
      Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i))) :
    ∀x,basisProfile ell x=0 := by
  let Z:={x:M|basisProfile ell x=0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨G,hG,hxG,hzero⟩:=sup_profile_local_zero hu hPDE hnorm hSpos hS hKS hlim hx
    exact ⟨G,hzero,hG,hxG⟩
  have hneg:=normalized_supProfile hSpos hnorm hlim
  have hcomp : Zᶜ=(basisProfile ell) ⁻¹' Iio 0 := by
    ext x
    simp only [Z,mem_compl_iff,mem_ofPred_eq,mem_preimage,mem_Iio]
    exact ⟨fun h=>(hneg x).lt_of_ne h,ne_of_lt⟩
  have hclosed : IsClosed Z:=isOpen_compl_iff.mp (hcomp ▸ (upperSemicontinuous_basisProfile ell).isOpen_preimage 0)
  obtain ⟨x,hx⟩:=normalized_supProfile_max hSpos hnorm hmax hlim
  have hUniv : Z=univ:=IsClopen.eq_univ ⟨hclosed,hZ⟩ ⟨x,hx⟩
  intro z
  have : z∈Z:=hUniv ▸ mem_univ z
  exact this

end SharpNodal.Geometry

end
end

end OAI
