import OAI.Analysis.NodalLength.LogGradients

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

namespace SharpNodal.Profiles
open Carleman
theorem local_potential_profile_affine_sup_bound {R : ℝ} (hR : 1≤R) : ∃Ck : ℝ,0≤Ck ∧
    ∀(ν : Measure Plane) [IsFiniteMeasure ν], (∀ᵐz ∂ν,‖z‖<4) →
    ∀(V : Plane → EReal) (h : Plane → ℝ),
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) → FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    Smooth h →
    (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x) →
    ∀Ch : ℝ,0≤Ch → (∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial h i) j z|≤Ch) →
    ∀ρ : ℝ,0<ρ → ∀y : Plane,‖y‖+2*R*ρ<3 →
    let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
    let e : ℝ := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
    (⨆x∈Metric.closedBall y (R*ρ),V x-(L (x-y):EReal))≤
      (⨆x∈Metric.ball y ρ,V x-(L (x-y):EReal))+(e:EReal) := by
  obtain ⟨Ck,hCk,hpot⟩ := ae_potential_affine_comparison (show 1≤2*R by linarith)
  refine ⟨Ck,hCk,?_⟩
  intro ν _ hs V h hV hneg htest hanchor hh heq Ch hCh hhess ρ hρ y hsmall
  dsimp only
  let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
  let a := diskAverage h y ρ+∫z,logDiskAverage y ρ z ∂ν
  let e := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
  let U := Metric.ball y (2*R*ρ)
  have hRpos : 0<R := by linarith
  have hU3 : U⊆Metric.ball (0:Plane) 3 := by
    intro x hx
    have hx' : ‖x-y‖<2*R*ρ := by simpa only [U,Metric.mem_ball,dist_eq_norm] using hx
    have hn := norm_add_le (x-y) y
    rw [sub_add_cancel] at hn
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  have hUΩ := hU3.trans (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000))
  have hupper : ∀x∈U,V x≤((a+L (x-y)+e:ℝ):EReal) := by
    apply profile_le_continuous_of_toReal_ae hV hneg htest Metric.isOpen_ball hUΩ
      ((continuous_const.add (L.continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hU3 (hpot ν hs ρ hρ y),
      ae_restrict_of_ae heq,self_mem_ae_restrict measurableSet_ball] with x hpx hex hmem
    have hx : ‖x-y‖≤(2*R)*ρ := (show ‖x-y‖<2*R*ρ by simpa only [U,Metric.mem_ball,dist_eq_norm] using hmem).le
    have hp := hpx hx
    have hh' := harmonic_outer_minus_average hh hCh (show 0≤2*R by positivity) hρ hhess hx
    rw [hex (hU3 hmem)]
    dsimp [a,L,e]
    change h x+aeLogPotential ν x≤diskAverage h y ρ+(∫z,logDiskAverage y ρ z ∂ν)+
      ((fderiv ℝ h y) (x-y)+inner ℝ (∫z,farGradient (2*R) ρ y z ∂ν) (x-y))+
      (4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν))
    linarith
  let w := fun x => h x+aeLogPotential ν x
  have hwi : IntegrableOn (fun ξ : Plane => w (y+ρ • ξ)) (Metric.ball 0 1) :=
    (scaled_continuous_integrable hh.continuous y ρ).add (scaled_aeLogPotential_integrableOn ν hs hρ y)
  have hfinite := profile_finite_ae_D3 hV hneg htest hanchor
  have hwV : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),V (y+ρ • ξ)=(w (y+ρ • ξ):EReal) := by
    filter_upwards [ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae heq),
      ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae hfinite),
      self_mem_ae_restrict measurableSet_ball] with ξ hξ hfξ hmem
    have hnorm : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hmem
    have h3 : y+ρ • ξ∈Metric.ball (0:Plane) 3 := by
      have hm := norm_add_le y (ρ • ξ)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hm
      simp only [Metric.mem_ball,dist_zero_right]
      nlinarith
    rw [← EReal.coe_toReal (hfξ h3).2 (hfξ h3).1,hξ h3]
  have hav : diskAverage w y ρ=a := by
    dsimp [diskAverage,w,a]
    rw [integral_add (scaled_continuous_integrable hh.continuous y ρ) (scaled_aeLogPotential_integrableOn ν hs hρ y),
      integral_logDiskAverage ν hs hρ y]
    ring
  have hinner := diskAverage_le_profileSup (L:=L) hρ hwi hwV
  rw [hav] at hinner
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hxU : x∈U := by
    have hx' : ‖x-y‖≤R*ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    simp only [U,Metric.mem_ball,dist_eq_norm]
    nlinarith
  have hhx : V x-(L (x-y):EReal)≤((a+e:ℝ):EReal) := by
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
    simpa only [← EReal.coe_add,add_assoc,add_comm,add_left_comm] using hupper x hxU
  exact hhx.trans (by simpa only [L,e,EReal.coe_add] using add_le_add hinner (le_refl (e:EReal)))

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

def extendedGridCenter (r : ℝ) (p : Fin 2 → ℤ) : Plane :=
  WithLp.toLp 2 (fun i => -1/2+((p i:ℝ)+1/2)*r)

lemma exists_extendedGridCenter {r : ℝ} (hr : 0<r) (x : Plane) :
    ∃p : Fin 2 → ℤ,‖extendedGridCenter r p-x‖≤r := by
  let p : Fin 2 → ℤ := fun i => ⌊(x i+1/2)/r⌋
  refine ⟨p,?_⟩
  have hd (i : Fin 2) : |(extendedGridCenter r p-x) i|≤r/2 := by
    have hl := Int.floor_le ((x i+1/2)/r)
    have hu := Int.lt_floor_add_one ((x i+1/2)/r)
    have hl' := (le_div_iff₀ hr).mp hl
    have hu' := (div_lt_iff₀ hr).mp hu
    change |-1/2+((p i:ℝ)+1/2)*r-x i|≤r/2
    change (p i:ℝ)*r≤x i+1/2 at hl'
    change x i+1/2<((p i:ℝ)+1)*r at hu'
    rw [abs_le]
    constructor <;> nlinarith
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hd 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hd 1) 2
  rw [sq_abs] at h0 h1
  have hn := EuclideanSpace.real_norm_sq_eq (extendedGridCenter r p-x)
  rw [Fin.sum_univ_two] at hn
  nlinarith [norm_nonneg (extendedGridCenter r p-x)]

lemma tendsto_gridScale {A : ℕ} (hA : 1<A) :
    Tendsto (fun m : ℕ => ((A:ℝ)⁻¹)^m) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · positivity
  · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hA)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma potential_affine_coefficient_limits (ν : Measure Plane) {R Ch Ck : ℝ} (hR : 1≤R)
    {h : Plane → ℝ} (hh : Smooth h) {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) (hsep : ∀ᵐz ∂ν,x≠z)
    (hi : Integrable (fun z => ‖x-z‖⁻¹) ν) :
    Tendsto (fun n =>fderiv ℝ h (y n)+innerSL ℝ (∫z,farGradient (2*R) (ρ n) (y n) z ∂ν))
      atTop (𝓝 (fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x))) ∧
    Tendsto (fun n => (4*Ch*((2*R)^2+1)*(ρ n)^2+Ck*(∫z,farWeight (2*R) (ρ n) (y n) z ∂ν))/ρ n)
      atTop (𝓝 0) := by
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n =>norm_nonneg _) hy hρlim
  obtain ⟨hg,he⟩ := truncated_potential_limits ν (by linarith : 1≤2*R) hρ hρlim hy hsep hi
  refine ⟨?_,?_⟩
  · exact ((hh.continuous_fderiv (by simp)).tendsto x |>.comp hylim).add
      ((innerSL ℝ).continuous.tendsto _ |>.comp hg)
  · have ht := (hρlim.const_mul (4*Ch*((2*R)^2+1))).add (he.const_mul Ck)
    have heq : (fun n =>4*Ch*((2*R)^2+1)*ρ n+Ck*((∫z,farWeight (2*R) (ρ n) (y n) z ∂ν)/ρ n))=
        (fun n =>(4*Ch*((2*R)^2+1)*(ρ n)^2+Ck*(∫z,farWeight (2*R) (ρ n) (y n) z ∂ν))/ρ n) := by
      funext n
      field_simp
    simpa only [zero_mul,mul_zero,add_zero,heq] using ht

theorem profile_small_affine_grid_gap {A : ℕ} (hA : 1<A) {R σ : ℝ} (hR : 1≤R) (hσ : 0<σ)
    {V : Plane → EReal} (hV : UpperSemicontinuous V)
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    (hnonconstant : ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y)
    (m₀ : ℕ) :
    ∃m≥m₀,∃p : Fin 2 → ℤ,∃c : Plane,∃e : ℝ,
      let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      0<‖c‖ ∧ ‖y‖+2*R*r<3 ∧ R*r<1/4 ∧ e<σ*r*‖c‖ ∧
      (⨆x∈Metric.closedBall y (R*r),V x-(inner ℝ c (x-y):EReal))≤
        (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))+(e:EReal) := by
  obtain ⟨Ch,hCh,hdec⟩ := profile_ae_decomposition_uniform
  obtain ⟨ν,hν,hs,_hm,h,hh,_hharm,hrep,hder⟩ := hdec V (hV.upperSemicontinuousOn _) hneg htest hanchor
  let := hν
  obtain ⟨x,hx,hsep,hi,hnz⟩ := profile_nonzero_gradient ν hs hV hneg htest hanchor hh hrep hnonconstant
  let ρ : ℕ → ℝ := fun m =>((A:ℝ)⁻¹)^m
  have hρ (m : ℕ) : 0<ρ m := by dsimp [ρ]; positivity
  have hρlim : Tendsto ρ atTop (𝓝 0) := tendsto_gridScale hA
  choose p hp using fun m =>exists_extendedGridCenter (hρ m) x
  let y : ℕ → Plane := fun m =>extendedGridCenter (ρ m) (p m)
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m =>norm_nonneg _) hp hρlim
  obtain ⟨Ck,_hCk,hbound⟩ := local_potential_profile_affine_sup_bound hR
  let L := fun m =>fderiv ℝ h (y m)+innerSL ℝ (∫z,farGradient (2*R) (ρ m) (y m) z ∂ν)
  let e := fun m =>4*Ch*((2*R)^2+1)*(ρ m)^2+Ck*(∫z,farWeight (2*R) (ρ m) (y m) z ∂ν)
  let L₀ := fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)
  have hL₀ : 0<‖L₀‖ := norm_pos_iff.mpr hnz
  obtain ⟨hL,he⟩ := potential_affine_coefficient_limits (Ch:=Ch) (Ck:=Ck) ν hR hh hρ hρlim hp hsep hi
  have hnonzero : ∀ᶠm in atTop,0<‖L m‖ := hL.norm.eventually (lt_mem_nhds hL₀)
  have hgap : ∀ᶠm in atTop,e m/ρ m<σ*‖L m‖ := he.eventually_lt (hL.norm.const_mul σ) (mul_pos hσ hL₀)
  have hsmall : ∀ᶠm in atTop,‖y m‖+2*R*ρ m<3 := by
    have ht : Tendsto (fun m =>‖y m‖+2*R*ρ m) atTop (𝓝 ‖x‖) := by
      simpa only [mul_zero,add_zero] using hylim.norm.add (hρlim.const_mul (2*R))
    apply ht.eventually (gt_mem_nhds _)
    have hx' : ‖x‖<2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    linarith
  have hmargin : ∀ᶠm in atTop,R*ρ m<1/4 := by
    have ht : Tendsto (fun m =>R*ρ m) atTop (𝓝 0) := by simpa using hρlim.const_mul R
    exact ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))
  obtain ⟨m,hm,hn,he',hs',hr'⟩ := ((eventually_ge_atTop m₀).and (hnonzero.and (hgap.and (hsmall.and hmargin)))).exists
  let c := (toDual ℝ Plane).symm (L m)
  have hc (v : Plane) : inner ℝ c v=L m v :=
    congrArg (fun f : Plane →L[ℝ] ℝ =>f v) ((toDual ℝ Plane).apply_symm_apply (L m))
  have hcn : ‖c‖=‖L m‖ := (toDual ℝ Plane).symm.norm_map _
  refine ⟨m,hm,p m,c,e m,?_,hs',hr',?_,?_⟩
  · rwa [hcn]
  · change e m<σ*ρ m*‖c‖
    rw [hcn]
    have ht := (div_lt_iff₀ (hρ m)).mp he'
    nlinarith
  · simpa only [hc] using hbound ν hs V h (hV.upperSemicontinuousOn _) hneg htest hanchor hh hrep Ch hCh
      (fun z i j =>(hder z).2 i j) (ρ m) (hρ m) (y m) hs'

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_nonconstant_of_positive_gap {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (_hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤ V a)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0< S j) {F G E : Set Plane}
    (hF : IsCompact F) (hF2 : F⊆Metric.ball (0:Plane) 2)
    (hG : IsOpen G) (hGn : G.Nonempty) (hGE : G⊆E) (hEF : E⊆F)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀j,δ≤ massExcess (tiltedMass (S j) (B j) (U j) (d j) 0 E)
      (tiltedMass (S j) (B j) (U j) (d j) 0 G)/S j) :
    ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y := by
  by_contra hn
  push Not at hn
  obtain ⟨a,ha,hVa⟩ := hanchor
  have ha2 : a∈Metric.ball (0:Plane) 2 := Metric.closedBall_subset_ball (by norm_num) ha
  have h21000 : Metric.ball (0:Plane) 2⊆Metric.ball 0 1000 := Metric.ball_subset_ball (by norm_num)
  have hfin : V a≠⊤ ∧ V a≠⊥ := ⟨ne_top_of_le_ne_top (by simp) (hneg a (h21000 ha2)),
    ne_bot_of_le_ne_bot (by exact EReal.coe_ne_bot (-1)) hVa⟩
  let c := (V a).toReal
  have hea : V a=(c:EReal) := (EReal.coe_toReal hfin.1 hfin.2).symm
  have he (x : Plane) (hx : x∈Metric.ball (0:Plane) 2) : V x=(c:EReal) := (hn x hx a ha2).trans hea
  have hG2 := (hGE.trans hEF).trans hF2
  have hsup : (⨆x∈G,V x+((0:ℝ):EReal))=(c:EReal) := by
    apply le_antisymm
    · exact iSup₂_le (fun x hx => by simp only [he x (hG2 hx),EReal.coe_zero,add_zero,le_refl])
    · obtain ⟨x,hx⟩ := hGn
      exact le_iSup₂_of_le x hx (by simp only [he x (hG2 hx),EReal.coe_zero,add_zero,le_refl])
  have hsupF : (⨆x∈F,V x+((0:ℝ):EReal))≤((c+(0:ℝ):ℝ):EReal) :=
    iSup₂_le (fun x hx => by simp only [he x (hF2 hx),EReal.coe_zero,add_zero,le_refl])
  have ht := profile_massExcess_transfer hp hS continuousOn_const hF (hF2.trans h21000)
    hG (hG2.trans h21000) hGE hEF (half_pos hδ) hsup hsupF
  obtain ⟨j,hj⟩ := ht.exists
  have hlow := hgap j
  have hupper := hj.2.2
  change massExcess (tiltedMass (S j) (B j) (U j) (d j) 0 E)
    (tiltedMass (S j) (B j) (U j) (d j) 0 G)/S j<0+δ/2 at hupper
  linarith

lemma local_affine_profile_transfer {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤ V a)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0< S j) (hd : ∀j,0< d j)
    {R r σ e : ℝ} {y c : Plane} (hR : 1≤ R) (hr : 0< r) (hc : 0<‖c‖)
    (hsmall : ‖y‖+2*R*r<3) (he : e<σ*r*‖c‖)
    (hgap : (⨆x∈Metric.closedBall y (R*r),V x-(inner ℝ c (x-y):EReal))≤
      (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))+(e:EReal)) :
    ∀ᶠj in atTop,
      centeredMass (B j+S j • c) (U j) y r≠0 ∧
      centeredMass (B j+S j • c) (U j) y (R*r)≠⊤ ∧
      massExcess (centeredMass (B j+S j • c) (U j) y (R*r))
        (centeredMass (B j+S j • c) (U j) y r)/(S j*r*‖c‖)<σ := by
  have hrR : r≤ R*r := by nlinarith
  have hF3 : Metric.closedBall y (R*r)⊆Metric.ball (0:Plane) 3 := by
    intro x hx
    have hx' : ‖x-y‖≤ R*r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith
  have hG3 := ((Metric.ball_subset_ball hrR).trans Metric.ball_subset_closedBall).trans hF3
  have h3R : Metric.ball (0:Plane) 3⊆Metric.ball 0 1000 := Metric.ball_subset_ball (by norm_num)
  let f : Plane → ℝ := fun x =>-inner ℝ c (x-y)
  have hf : Continuous f := (continuous_const.inner (continuous_id.sub continuous_const)).neg
  have hfbd : ∀x∈Metric.ball y r,f x≤‖c‖*r := by
    intro x hx
    have hh : ‖x-y‖< r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hh.le (norm_nonneg _)))
  obtain ⟨a,ha⟩ := profile_weighted_sup_real hV hneg htest hanchor hG3
    (ne_of_gt (Metric.measure_ball_pos volume y hr)) hfbd
  have ha' : (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))=(a:EReal) := by
    simpa only [f,EReal.coe_neg,← sub_eq_add_neg] using ha
  have hgap' : (⨆x∈Metric.closedBall y (R*r),V x+(f x:EReal))≤((a+e:ℝ):EReal) := by
    simpa only [f,EReal.coe_neg,← sub_eq_add_neg,ha',← EReal.coe_add] using hgap
  have ht := profile_massExcess_transfer hp hS hf.continuousOn (isCompact_closedBall y (R*r))
    (hF3.trans h3R) Metric.isOpen_ball (hG3.trans h3R) (Metric.ball_subset_ball hrR)
    Metric.ball_subset_closedBall (half_pos (sub_pos.mpr he)) ha hgap'
  filter_upwards [ht] with j hj
  obtain ⟨hfin,hfout⟩ := tilted_finite_centered (hd j) hj.1 hj.2.1
  refine ⟨hfin,hfout,?_⟩
  have hratio := hj.2.2
  change massExcess (tiltedMass (S j) (B j) (U j) (d j) (fun x =>-inner ℝ c (x-y)) (Metric.ball y (R*r)))
    (tiltedMass (S j) (B j) (U j) (d j) (fun x =>-inner ℝ c (x-y)) (Metric.ball y r))/S j<_ at hratio
  rw [tilted_excess_centered _ _ _ _ _ (hd j) y (R*r) r] at hratio
  have hless : massExcess (centeredMass (B j+S j • c) (U j) y (R*r))
      (centeredMass (B j+S j • c) (U j) y r)/S j<σ*r*‖c‖ := by
    linarith
  apply (div_lt_iff₀ (mul_pos (mul_pos (hS j) hr) hc)).mpr
  have hmul := (div_lt_iff₀ (hS j)).mp hless
  nlinarith only [hmul]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma zero_tiltedMass_centered (S : ℝ) (U : Plane → ℝ) {d : ℝ} (hd : 0≤ d) (y : Plane) (r : ℝ) :
    tiltedMass S 0 U d 0 (Metric.ball y r)=ENNReal.ofReal d*centeredMass 0 U y r := by
  simpa only [inner_zero_left,neg_zero,smul_zero,add_zero,mul_zero,Real.exp_zero,mul_one,Pi.zero_apply,Pi.zero_def]
    using tiltedMass_centered S 0 0 U d hd y r

lemma zero_tilted_excess_centered (S : ℝ) (U : Plane → ℝ) {d : ℝ} (hd : 0< d) (y : Plane) (R r : ℝ) :
    massExcess (tiltedMass S 0 U d 0 (Metric.ball y R))
      (tiltedMass S 0 U d 0 (Metric.ball y r))=
    massExcess (centeredMass 0 U y R) (centeredMass 0 U y r) := by
  rw [zero_tiltedMass_centered _ _ hd.le,zero_tiltedMass_centered _ _ hd.le]
  exact massExcess_mul_left _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top

lemma grid_child_closedBall_subset_two {A : ℕ} (hA : 10000< A) {y : Plane} (hy : y∈gridCenters A) :
    Metric.closedBall y (1000*(A:ℝ)⁻¹)⊆Metric.ball (0:Plane) 2 := by
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 1000*(A:ℝ)⁻¹<1 := by
    rw [← div_eq_mul_inv,div_lt_one hAr]
    exact_mod_cast (show 1000< A by omega)
  intro x hx
  rw [Metric.mem_ball,dist_zero_right]
  have hd : ‖x-y‖≤1000*(A:ℝ)⁻¹ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  have hn := gridCenters_norm (by omega : 0< A) y hy
  have ht : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
  linarith

theorem sequence_persistence_square {Cp a₀ : ℝ} (_hCp : 0≤ Cp) (ha₀ : 0< a₀)
    {A : ℕ} (hA : 10000< A) {yₑ : Plane} (hyₑ : yₑ∈gridCenters A)
    (D : ℕ → UnitWave Cp a₀) (H : ℕ → ℝ) (hH : ∀j,0< H j) (hHlim : Tendsto H atTop atTop)
    (hparent : ∀j,(D j).growth 0≤ H j)
    (hchild : ∀j,H j< massExcess (centeredMass 0 (D j).U yₑ (1000*(A:ℝ)⁻¹))
      (centeredMass 0 (D j).U yₑ ((A:ℝ)⁻¹))/((D j).K*(A:ℝ)⁻¹))
    {σ : ℝ} (hσ : 0<σ) (P : ℝ) (m₀ : ℕ) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∃m≥ m₀,∃p : Fin 2 → ℤ,∃c : Plane,
      let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      0<‖c‖ ∧ ‖y‖+2000*r<3 ∧ 1000*r<1/4 ∧
      ∀ᶠj in atTop,P≤‖H (φ j) • c‖ ∧
        centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y r≠0 ∧
        centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y (1000*r)≠⊤ ∧
        massExcess (centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y (1000*r))
          (centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y r)/
          ((D (φ j)).K*r)<σ*‖H (φ j) • c‖ := by
  have hK (j : ℕ) : 0<(D j).K := ha₀.trans_le (D j).frequency_lower
  let S : ℕ → ℝ := fun j =>(D j).K*H j
  have hS (j : ℕ) : 0< S j := mul_pos (hK j) (hH j)
  have hSinf : Tendsto S atTop atTop := by
    apply tendsto_atTop_mono (fun j => mul_le_mul_of_nonneg_right (D j).frequency_lower (hH j).le)
    exact hHlim.const_mul_atTop ha₀
  let d : ℕ → ℝ := fun j =>(tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1000)).toReal⁻¹
  have hmass (j : ℕ) (r : ℝ) : tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 r)=centeredMass 0 (D j).U 0 r := by
    simpa using zero_tiltedMass_centered (S j) (D j).U (by norm_num : (0:ℝ)≤1) 0 r
  have hnorm (j : ℕ) : 0< d j ∧ tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1000)=1 := by
    apply tiltedMass_normalized
    · rw [hmass]
      exact ne_of_gt ((pos_iff_ne_zero.mpr (D j).inner_nonzero).trans_le
        (centeredMass_mono _ _ _ (by norm_num : (1:ℝ)≤1000)))
    · rw [hmass]
      exact (D j).outer_finite
  have hinner (j : ℕ) : (-1:EReal)≤ logRate (S j)
      (tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1)) := by
    have heq := normalized_inner_rate_eq (S:=S j) (B:=0) (U:=(D j).U)
      (Metric.ball_subset_ball (x:=(0:Plane)) (by norm_num : (1:ℝ)≤1000))
      (by simpa only [hmass] using (D j).inner_nonzero) (by simpa only [hmass] using (D j).outer_finite)
    change (-1:EReal)≤_
    change logRate (S j) (tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1))=
      ((-massExcess (tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1000))
        (tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1))/S j:ℝ):EReal) at heq
    rw [heq,hmass,hmass]
    apply EReal.coe_le_coe_iff.mpr
    have hp := hparent j
    simp only [UnitWave.growth,UnitWave.excess,smul_zero] at hp
    have hp' := (div_le_iff₀ (hK j)).mp hp
    apply (le_div_iff₀ (hS j)).mpr
    dsimp only [S]
    nlinarith only [hp']
  have hinv : Tendsto (fun j =>(H j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hHlim
  have hratio : Tendsto (fun j =>(D j).K/(S j+‖(0:Plane)‖)) atTop (𝓝 0) := by
    have he (j : ℕ) : (D j).K/(S j+‖(0:Plane)‖)=(H j)⁻¹ := by
      dsimp only [S]
      rw [norm_zero,add_zero]
      field_simp [(hK j).ne', (hH j).ne']
    simpa only [he] using hinv
  let err : ℕ → ℝ := fun j => Cp*((H j)⁻¹)^2
  have herr : Tendsto err atTop (𝓝 0) := by simpa [err] using (hinv.pow 2).const_mul Cp
  have hpd (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball (0:Plane) 1000) :
      |(D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖(0:Plane)‖))|≤ err j := by
    have he : (D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖(0:Plane)‖))=
        coordPartial (D j).p i x*((H j)⁻¹)^2 := by
      dsimp only [S]
      rw [norm_zero,add_zero]
      field_simp [(hK j).ne', (hH j).ne']
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ((H j)⁻¹))]
    exact mul_le_mul_of_nonneg_right ((D j).derivative_bound i x hx) (sq_nonneg _)
  obtain ⟨V,φ,hφ,hV,hneg,hprof⟩ := extract_tilted_profile Metric.isOpen_ball S (fun _ =>0)
    (fun j =>(D j).U) d hS hSinf (fun j =>(D j).smooth_U.continuousOn) (fun j =>(hnorm j).2.le)
  have htest := full_test_of_profile Metric.isOpen_ball (fun j =>(D (φ j)).smooth_p)
    (fun j =>(D (φ j)).smooth_U) (fun j => hS (φ j)) (hSinf.comp hφ.tendsto_atTop)
    (fun j =>(hnorm (φ j)).1) (hratio.comp hφ.tendsto_atTop) (fun j =>(D (φ j)).coefficient_bound)
    (herr.comp hφ.tendsto_atTop) (fun j => hpd (φ j)) (fun j =>(D (φ j)).equation)
    (hV.upperSemicontinuousOn _) hprof
  have hanchor := profile_anchor_from_mass (hV.upperSemicontinuousOn _) hprof
    (fun j => hS (φ j)) (fun j => hinner (φ j))
  have hrA : 0<(A:ℝ)⁻¹ := by positivity
  have hnonconstant := profile_nonconstant_of_positive_gap hV (fun x _ => hneg x) hanchor hprof
    (fun j => hS (φ j)) (isCompact_closedBall yₑ (1000*(A:ℝ)⁻¹))
    (grid_child_closedBall_subset_two hA hyₑ) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hrA) (Metric.ball_subset_ball (by nlinarith : (A:ℝ)⁻¹≤1000*(A:ℝ)⁻¹))
    Metric.ball_subset_closedBall hrA (fun j =>?_)
  · obtain ⟨m,hm,p,c,e,hc,hsmall,hmargin,herr',hgap⟩ := profile_small_affine_grid_gap
      (by omega : 1< A) (by norm_num : (1:ℝ)≤1000) hσ hV (fun x _ => hneg x) htest hanchor hnonconstant m₀
    refine ⟨φ,hφ,m,hm,p,c,hc,?_,hmargin,?_⟩
    · simpa only [show (2:ℝ)*1000=2000 by norm_num] using hsmall
    · let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      have hr : 0< r := pow_pos hrA m
      have ht := local_affine_profile_transfer (hV.upperSemicontinuousOn _) (fun x _ => hneg x) htest hanchor
        hprof (fun j => hS (φ j)) (fun j =>(hnorm (φ j)).1) (by norm_num : (1:ℝ)≤1000) hr hc hsmall herr' hgap
      have hlarge : ∀ᶠj in atTop,P≤‖H (φ j) • c‖ := by
        have ht : Tendsto (fun j => H (φ j)*‖c‖) atTop atTop :=
          (hHlim.comp hφ.tendsto_atTop).atTop_mul_const hc
        have he (j : ℕ) : ‖H (φ j) • c‖=H (φ j)*‖c‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hH (φ j))]
        simpa only [he] using ht.eventually_ge_atTop P
      filter_upwards [ht,hlarge] with j hj hbig
      simp only [Function.comp_apply,zero_add] at hj
      refine ⟨hbig,hj.1,hj.2.1,?_⟩
      have hh := (div_lt_iff₀ (mul_pos (mul_pos (hS (φ j)) hr) hc)).mp hj.2.2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hH (φ j))]
      apply (div_lt_iff₀ (mul_pos (hK (φ j)) hr)).mpr
      dsimp only [S] at hh
      nlinarith only [hh]
  · simp only [Function.comp_apply]
    rw [zero_tilted_excess_centered _ _ (hnorm (φ j)).1]
    apply (le_div_iff₀ (hS (φ j))).mpr
    have hh := (lt_div_iff₀ (mul_pos (hK (φ j)) hrA)).mp (hchild (φ j))
    dsimp only [S]
    nlinarith only [hh]

end SharpNodal.Profiles

end
end
end
end
end

end OAI
