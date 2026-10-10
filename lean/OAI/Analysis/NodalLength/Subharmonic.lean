import OAI.Analysis.NodalLength.ProfileExtraction

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

namespace SharpNodal.Profiles
open Carleman

lemma full_test_local {Ω O : Set Plane} {V : Plane → EReal} {f : Plane → ℝ} {x₀ : Plane}
    (htest : FullTestProperty Ω V) (hO : IsOpen O) (hxO : x₀∈O) (hxΩ : x₀∈Ω)
    (hf : ContDiffOn ℝ ∞ f O) (ht : IsUpperTest V f x₀) :
    0≤euclideanLaplacian f x₀ := by
  obtain ⟨g,r,hg,hr,_,heq⟩ := smooth_extension_near hO hxO hf
  have hevent : g =ᶠ[𝓝 x₀] f := Filter.Eventually.mono (Metric.ball_mem_nhds x₀ hr) fun _ hx => heq _ hx
  have htg : IsUpperTest V g x₀ := by
    constructor
    · rw [hevent.eq_of_nhds]; exact ht.1
    · filter_upwards [ht.2,hevent] with x hx he
      rwa [he]
  have hh := htest g hg x₀ hxΩ htg
  rwa [(laplacian_eventuallyEq hevent).eq_of_nhds] at hh

lemma laplacian_add_local {O : Set Plane} {f g : Plane → ℝ} {x : Plane}
    (hO : IsOpen O) (hx : x∈O) (hf : ContDiffOn ℝ ∞ f O) (hg : Smooth g) :
    euclideanLaplacian (fun y => f y+g y) x=euclideanLaplacian f x+euclideanLaplacian g x := by
  obtain ⟨f',r,hf',hr,_,heq⟩ := smooth_extension_near hO hx hf
  have hevent : f'=ᶠ[𝓝 x] f := Filter.Eventually.mono (Metric.ball_mem_nhds x hr) fun _ hz => heq _ hz
  have hevent' : (fun y => f' y+g y)=ᶠ[𝓝 x] (fun y => f y+g y) := by
    filter_upwards [hevent] with y hy; rw [hy]
  rw [← (laplacian_eventuallyEq hevent').eq_of_nhds,laplacian_add hf' hg,
    (laplacian_eventuallyEq hevent).eq_of_nhds]

lemma laplacian_radiusSquare (x₀ x : Plane) : euclideanLaplacian (radiusSquare x₀) x=4 := by
  have heq : radiusSquare x₀=centeredQuadratic ((2:ℝ) • innerForm) x₀ := by
    ext y
    simpa only [radiusSquare,mul_one,one_mul] using (centeredQuadratic_inner_smul 1 x₀ y).symm
  have hs : SymmetricForm ((2:ℝ) • innerForm) := by
    intro y z
    simp only [smul_apply,smul_eq_mul,symmetric_innerForm y z]
  rw [heq,laplacian_centeredQuadratic hs]
  change formTrace ((2:ℝ) • innerForm)=4
  rw [formTrace_smul,formTrace_innerForm]
  norm_num

lemma laplacian_quadraticBarrier (a : Plane) (r ε m : ℝ) (x : Plane) :
    euclideanLaplacian (fun y => ε*(r^2-radiusSquare a y)+m) x= -4*ε := by
  have heq : (fun y => ε*(r^2-radiusSquare a y)+m)=
      (fun y => (ε*r^2+m)+(-ε)*radiusSquare a y) := by ext y; ring
  rw [heq,laplacian_add contDiff_const (contDiff_const.mul (smooth_radiusSquare a)),
    laplacian_const,laplacian_const_mul (smooth_radiusSquare a)]
  dsimp only
  rw [laplacian_radiusSquare]
  ring

theorem harmonic_comparison_of_full_test {Ω : Set Plane} {V : Plane → EReal}
    {h : Plane → ℝ} {a : Plane} {r : ℝ}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) (hr : 0<r) (hball : Metric.closedBall a r⊆Ω)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball a r))
    (hc : ContinuousOn h (Metric.closedBall a r))
    (hΔ : ∀ x∈Metric.ball a r, euclideanLaplacian h x=0)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(h x:EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(h x:EReal) := by
  intro x hx
  by_contra hn
  have hgap : (0:EReal)<V x+((-h x:ℝ):EReal) := by
    have hhx := EReal.add_lt_add_right_coe (lt_of_not_ge hn) (-h x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhx
  obtain ⟨δ,hδ0,hδgap⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have hδ : 0<δ := by exact_mod_cast hδ0
  let ε := δ/(r^2+1)
  have hε : 0<ε := div_pos hδ (by positivity)
  have hεmul : ε*(r^2+1)=δ := by dsimp [ε];field_simp
  let q : Plane → ℝ := fun y => h y+ε*(r^2-radiusSquare a y)
  have hbar : Smooth (fun y => ε*(r^2-radiusSquare a y)) :=
    contDiff_const.mul (contDiff_const.sub (smooth_radiusSquare a))
  have hq : ContinuousOn q (Metric.closedBall a r) := hc.add hbar.continuous.continuousOn
  have hqvalue : (0:EReal)<V x+((-q x:ℝ):EReal) := by
    have hle : ε*(r^2-radiusSquare a x)≤δ := by
      rw [← hεmul]
      apply mul_le_mul_of_nonneg_left _ hε.le
      have := sq_nonneg ‖x-a‖
      dsimp [radiusSquare]
      linarith
    have hhx := EReal.add_lt_add_right_coe hδgap (h x)
    have hlower : ((δ+h x:ℝ):EReal)<V x := by
      simpa only [← EReal.coe_add,add_assoc,neg_add_cancel,EReal.coe_zero,add_zero] using hhx
    have hqle : (q x:EReal)≤((δ+h x:ℝ):EReal) := by
      apply EReal.coe_le_coe_iff.mpr
      dsimp [q]; linarith
    have hhq := EReal.add_lt_add_right_coe (hqle.trans_lt hlower) (-q x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhq
  obtain ⟨y,hy,hmax⟩ := (upperSemicontinuousOn_add_real (hV.mono hball) hq.neg).exists_isMaxOn
    ⟨a,Metric.mem_closedBall_self hr.le⟩ (isCompact_closedBall a r)
  have hpos : (0:EReal)<V y+((-q y:ℝ):EReal) := hqvalue.trans_le (hmax hx)
  have hyint : y∈Metric.ball a r := by
    apply Metric.mem_ball.mpr
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hy)
    intro he
    have hybd : y∈Metric.sphere a r := Metric.mem_sphere.mpr he
    have hqbd : q y=h y := by
      have hdist : ‖y-a‖=r := by simpa only [Metric.mem_sphere,dist_eq_norm] using hybd
      simp only [q,radiusSquare,hdist,sub_self,mul_zero,add_zero]
    have hb := add_le_add (hbdry y hybd) (le_refl ((-q y:ℝ):EReal))
    rw [hqbd,← EReal.coe_add,add_neg_cancel,EReal.coe_zero] at hb
    apply (not_le_of_gt hpos)
    simpa only [hqbd] using hb
  have hfinite : V y≠⊤ ∧ V y≠⊥ := by
    refine ⟨htop y (hball hy),?_⟩
    intro he
    rw [he,EReal.bot_add] at hpos
    exact (not_lt_of_ge bot_le) hpos
  let m := (V y).toReal-q y
  have ht := upper_test_of_maximum (Metric.ball_subset_interior_closedBall hyint) hfinite hmax
  have ht' : IsUpperTest V (fun z => h z+(ε*(r^2-radiusSquare a z)+m)) y := by
    convert! ht using 1
    ext z
    dsimp [q,m]
    ring
  have hs := full_test_local htest Metric.isOpen_ball hyint (hball hy)
    (hh.add (hbar.add contDiff_const).contDiffOn) ht'
  rw [laplacian_add_local Metric.isOpen_ball hyint hh (hbar.add contDiff_const),
    hΔ y hyint,laplacian_quadraticBarrier,zero_add] at hs
  linarith
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem extract_normalized_parameters (S : ℕ → ℝ) (B : ℕ → Plane)
    (hS : ∀ j, 0 < S j) :
    ∃ (φ : ℕ → ℕ) (d : ℝ) (b : Plane), StrictMono φ ∧ 0 ≤ d ∧ d + ‖b‖ = 1 ∧
      Tendsto (fun j => S (φ j) / (S (φ j) + ‖B (φ j)‖)) atTop (𝓝 d) ∧
      Tendsto (fun j => (S (φ j) + ‖B (φ j)‖)⁻¹ • B (φ j)) atTop (𝓝 b) := by
  let x : ℕ → ℝ × Plane := fun j =>
    (S j / (S j + ‖B j‖), (S j + ‖B j‖)⁻¹ • B j)
  have hD (j : ℕ) : 0 < S j + ‖B j‖ := add_pos_of_pos_of_nonneg (hS j) (norm_nonneg _)
  have hxnorm (j : ℕ) : ‖(x j).2‖ = ‖B j‖ / (S j + ‖B j‖) := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hD j))]
    ring
  have hxpos (j : ℕ) : 0 ≤ (x j).1 := (div_pos (hS j) (hD j)).le
  have hxunit (j : ℕ) : (x j).1 + ‖(x j).2‖ = 1 := by
    rw [hxnorm]
    change S j / (S j + ‖B j‖) + ‖B j‖ / (S j + ‖B j‖) = 1
    rw [← add_div,div_self (hD j).ne']
  have hx (j : ℕ) : x j ∈ Metric.closedBall (0 : ℝ × Plane) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_prod_le_iff]
    constructor
    · rw [Real.norm_eq_abs,abs_of_nonneg (hxpos j)]
      nlinarith [hxunit j,norm_nonneg (x j).2]
    · nlinarith [hxunit j,hxpos j]
  obtain ⟨a,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ℝ × Plane) 1).tendsto_subseq hx
  have hd : Tendsto (fun j => (x (φ j)).1) atTop (𝓝 a.1) :=
    continuous_fst.tendsto a |>.comp hlim
  have hb : Tendsto (fun j => (x (φ j)).2) atTop (𝓝 a.2) :=
    continuous_snd.tendsto a |>.comp hlim
  refine ⟨φ,a.1,a.2,hφ,?_,?_,hd,hb⟩
  · exact ge_of_tendsto hd (Eventually.of_forall fun j => hxpos (φ j))
  · have hsum := hd.add hb.norm
    have hconst : (fun j => (x (φ j)).1 + ‖(x (φ j)).2‖) = fun _ => (1:ℝ) :=
      funext fun j => hxunit (φ j)
    rw [hconst] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.subseq {Ω : Set Plane} {S c : ℕ → ℝ} {B : ℕ → Plane}
    {U : ℕ → Plane → ℝ} {V : Plane → EReal}
    (h : WeightedProfileBounds Ω S B U c V) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    WeightedProfileBounds Ω (S∘φ) (B∘φ) (U∘φ) (c∘φ) V := by
  constructor
  · intro f hf F hF hFΩ
    exact hφ.limsup_comp_le_limsup.trans (h.upper f hf F hF hFΩ)
  · intro f hf G hG hGΩ
    exact (h.lower f hf G hG hGΩ).trans hφ.liminf_le_liminf_comp

theorem full_test_of_profile
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S K e c : ℕ → ℝ} {Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0<c j)
    (hK : Tendsto (fun j => K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
    FullTestProperty Ω V := by
  obtain ⟨φ,d,b,hφ,hd,hdb,hSd,hBb⟩ := extract_normalized_parameters S B hSpos
  apply full_test_of_shifted hΩ hV hd hdb
  apply shifted_test_of_profile (S:=S∘φ) (B:=B∘φ) (p:=p∘φ) (U:=U∘φ)
    (D:=fun j => S (φ j)+‖B (φ j)‖) (K:=K∘φ) (e:=e∘φ) (c:=c∘φ)
    hΩ (fun j => hp (φ j)) (fun j => hU (φ j)) (fun j => hSpos (φ j))
    (hS.comp hφ.tendsto_atTop) (fun j => hc (φ j)) (fun _ => rfl)
    hBb hSd (hK.comp hφ.tendsto_atTop) (fun j => hpbound (φ j))
    (he.comp hφ.tendsto_atTop) (fun j => hpgrad (φ j)) (fun j => hPDE (φ j))
    hV (hprofile.subseq hφ.tendsto_atTop)

theorem harmonic_comparison_of_profile
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S K e c : ℕ → ℝ} {Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0<c j)
    (hK : Tendsto (fun j => K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hVtop : ∀ x∈Ω, V x≠⊤)
    (hprofile : WeightedProfileBounds Ω S B U c V)
    {h : Plane → ℝ} {a : Plane} {r : ℝ} (hr : 0<r) (hball : Metric.closedBall a r⊆Ω)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball a r)) (hc' : ContinuousOn h (Metric.closedBall a r))
    (hΔ : ∀ x∈Metric.ball a r, euclideanLaplacian h x=0)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(h x:EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(h x:EReal) :=
  harmonic_comparison_of_full_test hV hVtop
    (full_test_of_profile hΩ hp hU hSpos hS hc hK hpbound he hpgrad hPDE hV hprofile)
    hr hball hh hc' hΔ hbdry
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

def planeComplex : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

lemma plane_laplacian_eq_mathlib {f : Plane → ℝ} (hf : Smooth f) :
    euclideanLaplacian f = Δ f := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  exact (hessian_on_basis hf x i i).symm

lemma laplacian_comp_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ (f∘e) = (Δ f)∘e := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f∘e) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  have hh := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
    hf x (i:=2) (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))
  rw [show (f∘e)=(f∘e.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  ext k
  fin_cases k <;> rfl

lemma plane_laplacian_comp_complex {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x : Plane) :
    euclideanLaplacian (f∘planeComplex) x = (Δ f) (planeComplex x) := by
  have hf' : Smooth (f∘planeComplex) := by
    convert! hf.comp planeComplex.toContinuousLinearEquiv.contDiff using 1
  rw [plane_laplacian_eq_mathlib hf', laplacian_comp_isometry planeComplex hf]
  rfl

lemma compare_complex_harmonic {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hΔ : ∀ z, (Δ f) z=0) {a : Plane} {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall a r⊆Ω)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(f (planeComplex x):EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(f (planeComplex x):EReal) := by
  apply harmonic_comparison_of_full_test hV htop htest hr hball
    (hf.comp planeComplex.toContinuousLinearEquiv.contDiff).contDiffOn
    (hf.continuous.comp planeComplex.continuous).continuousOn _ hbdry
  intro x _
  exact (plane_laplacian_comp_complex hf x).trans (hΔ _)
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma harmonic_extension_fourier_span {c : ℂ} {r : ℝ} (hr : r ≠ 0)
    {f : C(AddCircle (1:ℝ),ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
    ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=f t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n,rfl⟩ := hf
      have hbase (n : ℕ) : ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
          ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=fourier (n:ℤ) t := by
        refine ⟨fun z => ((z-c)/(r:ℂ))^n, ?_, ?_, ?_⟩
        · fun_prop
        · intro z _
          apply AnalyticAt.harmonicAt
          fun_prop
        · intro t
          simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr),
            fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]
      cases n with
      | ofNat n => exact hbase n
      | negSucc n =>
          obtain ⟨P,hP,hH,hf⟩ := hbase (n+1)
          refine ⟨fun z => conj (P z), ?_, ?_, ?_⟩
          · exact Complex.conjCLE.contDiff.comp hP
          · exact hH.comp_CLM Complex.conjCLE.toContinuousLinearMap
          · intro t
            change conj (P _) = fourier (-(↑(n+1):ℤ)) t
            rw [hf,fourier_neg]
  | zero =>
      exact ⟨0,contDiff_const,fun _ _ => harmonicAt_const 0,fun _ => rfl⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨P,hP,hH,hf⟩ := ihf
      obtain ⟨Q,hQ,hJ,hg⟩ := ihg
      exact ⟨P+Q,hP.add hQ,hH.add hJ,fun t => by simpa only [Pi.add_apply,ContinuousMap.add_apply] using congrArg₂ (·+·) (hf t) (hg t)⟩
  | smul a f hf ih =>
      obtain ⟨P,hP,hH,hf⟩ := ih
      exact ⟨a • P,hP.const_smul a,hH.comp_CLM (ContinuousLinearMap.mul ℝ ℂ a),fun t => by simpa only [Pi.smul_apply,ContinuousMap.smul_apply] using congrArg (a • ·) (hf t)⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma exists_circle_param {c z : ℂ} {r : ℝ} (hr : 0<r)
    (hz : z∈Metric.sphere c r) :
    ∃ t : AddCircle (1:ℝ), z=c+(r:ℂ)*AddCircle.toCircle t := by
  have hnorm : ‖(z-c)/(r:ℂ)‖=1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    rw [← dist_eq_norm,Metric.mem_sphere.mp hz,div_self hr.ne']
  let w : Circle := ⟨(z-c)/(r:ℂ),mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨t,ht⟩ := (AddCircle.homeomorphCircle (T:=(1:ℝ)) one_ne_zero).surjective w
  refine ⟨t,?_⟩
  have ht' : (AddCircle.toCircle t : ℂ)=(z-c)/(r:ℂ) := by
    simpa only [AddCircle.homeomorphCircle_apply] using congrArg (fun z : Circle => (z:ℂ)) ht
  rw [ht',mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  exact (add_sub_cancel c z).symm

lemma approximate_circle_by_harmonic {c : ℂ} {r ε : ℝ} (hr : 0<r) (hε : 0<ε)
    {g : ℂ → ℝ} (hg : Continuous g) :
    ∃ P : ℂ → ℝ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ z∈Metric.sphere c r, |P z-g z|<ε := by
  let f : C(AddCircle (1:ℝ),ℂ) := ⟨fun t => (g (c+(r:ℂ)*AddCircle.toCircle t):ℂ),by fun_prop⟩
  have hcl : f ∈ closure (Submodule.span ℂ (Set.range (@fourier (1:ℝ))) : Set C(AddCircle (1:ℝ),ℂ)) := by
    change f ∈ (Submodule.span ℂ (Set.range (@fourier (1:ℝ)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨q,hq,hfq⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨P,hP,hH,hbdry⟩ := harmonic_extension_fourier_span (c:=c) hr.ne' hq
  refine ⟨fun z => (P z).re, Complex.reCLM.contDiff.comp hP,hH.comp_CLM Complex.reCLM,?_⟩
  intro z hz
  obtain ⟨t,rfl⟩ := exists_circle_param hr hz
  change |(P (c+(r:ℂ)*AddCircle.toCircle t)).re-g (c+(r:ℂ)*AddCircle.toCircle t)|<ε
  rw [hbdry]
  have hqt := (ContinuousMap.dist_apply_le_dist (f:=f) (g:=q) t).trans_lt hfq
  have h := (Complex.abs_re_le_norm (q t-f t)).trans_lt (by
    simpa only [dist_eq_norm,norm_sub_rev] using hqt)
  simpa only [Complex.sub_re,ContinuousMap.coe_mk, f,Complex.ofReal_re] using h

theorem submean_continuous_majorant {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀x∈Ω,V x≠⊤)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall a r⊆Ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hbdry : ∀ x∈Metric.sphere a r,V x≤(g (planeComplex x):EReal)) :
    V a≤((Real.circleAverage g (planeComplex a) r:ℝ):EReal) := by
  have ha : a∈Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  by_cases hbot : V a=⊥
  · simp [hbot]
  have hcoe := EReal.coe_toReal (htop a (hball ha)) hbot
  rw [← hcoe,EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P,hP,hH,happrox⟩ := approximate_circle_by_harmonic (c:=planeComplex a) hr (half_pos hε) hg
  let H : ℂ → ℝ := fun z => P z+ε/2
  have hHs : ContDiff ℝ ∞ H := hP.add contDiff_const
  have hHh : HarmonicOnNhd H univ := hH.add (fun _ _ => harmonicAt_const (ε/2))
  have hle : V a≤(H (planeComplex a):EReal) := by
    apply compare_complex_harmonic hV htop htest hHs (fun z => (hHh z (mem_univ _)).2.self_of_nhds) hr hball _ a ha
    intro x hx
    have hx' : planeComplex x∈Metric.sphere (planeComplex a) r := by
      simpa only [Metric.mem_sphere,planeComplex.isometry.dist_eq] using hx
    apply (hbdry x hx).trans
    apply EReal.coe_le_coe_iff.mpr
    exact le_of_lt (by have := (abs_lt.mp (happrox _ hx')).1; dsimp [H]; linarith)
  have hmean : H (planeComplex a)≤Real.circleAverage g (planeComplex a) r+ε := by
    rw [← hHh.mono (subset_univ _) |>.circleAverage_eq]
    have hcomp := Real.circleAverage_mono (c:=planeComplex a) (R:=r) hHs.continuous.continuousOn.circleIntegrable'
      (hg.add continuous_const).continuousOn.circleIntegrable' (f₂:=fun z => g z+ε) ?_
    · simpa only [show (fun z => g z+ε)=g+(fun _ => ε) from rfl,
        Real.circleAverage_add hg.continuousOn.circleIntegrable' continuous_const.continuousOn.circleIntegrable',
        Real.circleAverage_const] using hcomp
    · intro z hz
      have := (abs_lt.mp (happrox z (by simpa [abs_of_pos hr] using hz))).2
      dsimp [H]
      linarith
  exact (EReal.coe_le_coe_iff.mp (hcoe ▸ hle)).trans hmean
end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
