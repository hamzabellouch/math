import Mathlib
import OAI.Geometry.CubicTorus.Profiles.CMCSecantSymbol

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeSupport_local_mono {E F U : Set Torus} (hU : IsOpen U)
    (hEF : E∩U⊆F∩U) {a : Torus} (haU : a∈U) (haE : a∈volumeSupport E) :
    a∈volumeSupport F := by
  have hh := Measure.interior_inter_support (μ := torusVolume.restrict E) (s := U)
  rw [hU.interior_eq] at hh
  have hh' := hh ⟨haU,haE⟩
  have he : (torusVolume.restrict E).restrict U=torusVolume.restrict (E∩U) := by
    rw [Measure.restrict_restrict hU.measurableSet,inter_comm]
  rw [he] at hh'
  exact (Measure.support_mono (Measure.restrict_mono (hEF.trans inter_subset_left) le_rfl)) hh'

lemma volumeSupport_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    volumeSupport E∩U=volumeSupport F∩U := by
  ext a
  constructor
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.subset ha.2 ha.1,ha.2⟩
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.symm.subset ha.2 ha.1,ha.2⟩

lemma openRepresentative_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    openRepresentative E∩U=openRepresentative F∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp hEF a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hs := volumeSupport_local_eq hU hec
  ext a
  have hh := Set.ext_iff.mp hs a
  simp only [openRepresentative,mem_inter_iff,mem_compl_iff] at *
  tauto

lemma isMinimizerAt_frontier_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U) :
    frontier (openRepresentative E)∩U=frontier (openRepresentative F)∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp he a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hh := volumeSupport_local_eq hU he
  have hc := volumeSupport_local_eq hU hec
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmE,
    isMinimizerAt_frontier_openRepresentative hW hF hmF]
  ext a
  have hh' := Set.ext_iff.mp hh a
  have hc' := Set.ext_iff.mp hc a
  simp only [mem_inter_iff] at *
  tauto

lemma local_region_flux_eq {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (he : E∩U=F∩U) {X : Cover → Cover}
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,X y=0) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence X x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,divergence X x := by
  classical
  rw [← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)),
    ← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hF))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : quotientMap x∈U
  · have hh := Set.ext_iff.mp he (quotientMap x)
    simp only [mem_inter_iff,hx,and_true] at hh
    simp only [Set.indicator_apply,mem_inter_iff,mem_preimage,hh]
  · have he0 : X=ᶠ[𝓝 x] (fun _ => 0) := hz x hx
    have hd : divergence X x=0 := by
      have hd0 : fderiv ℝ X x=0 := he0.fderiv_eq.trans (congrFun (fderiv_const (𝕜 := ℝ) (E := Cover) (c := (0 : Cover))) x)
      simp only [divergence,hd0,zero_apply,PiLp.zero_apply,Finset.sum_const_zero]
    simp only [Set.indicator_apply,hd,ite_self]

lemma local_region_weightedPerimeter_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {φ : Cover → ℝ} (hzero : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    weightedPerimeter E φ=weightedPerimeter F φ := by
  unfold weightedPerimeter
  congr 1
  funext X
  congr 1
  funext hX
  rw [local_region_flux_eq hE hF he (X := fun y => φ y • X y) (by
    intro x hx
    filter_upwards [hzero x hx] with y hy
    rw [hy,zero_smul])]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_region_weighted_mass_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ m x,φ (x+latticeVector m)=φ x) (hn : ∀ x,0≤φ x)
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
  have hh := local_region_weightedPerimeter_eq hE hF he hz
  rw [normalMeasure_weightedPerimeter hμ hφ hp hn,
    normalMeasure_weightedPerimeter hν hφ hp hn] at hh
  have hh' := congrArg ENNReal.toReal hh
  have hm0 : 0≤∫ z,φ z.1 ∂(μ : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  have hn0 : 0≤∫ z,φ z.1 ∂(ν : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  simpa only [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal hn0] using hh'

theorem isMinimizerAt_normal_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  obtain ⟨φ,hφ,hp,hb,⟨T,hT,hxT,hone⟩,hzero⟩ := exists_periodic_local_cutoff (quotientMap x) hU hx.2
  have hbound := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hxF : quotientMap x∈frontier (openRepresentative F) := (hbound ▸ hx).1
  have hunit (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E)) : ‖N y‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hpN]) (fun _ _ => rfl) _ y hy
    filter_upwards [haN] with z hz
    rw [hz,z.2.property]
  have hmass := local_region_weighted_mass_eq hE hF he hμ hν hφ hp (fun y => (hb y).1) hzero
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y • N y) := hφ.smul hN
  have hXp : ∀ k y,φ (y+latticeVector k) • N (y+latticeVector k)=φ y • N y :=
    fun k y => by rw [hp,hpN]
  have hflux : (∫ z,φ z.1*⟪(z.2 : Cover),N z.1⟫ ∂(ν : Measure NormalBundle))=
      ∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
    calc
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(ν : Measure NormalBundle) := by simp only [real_inner_smul_right]
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' F,divergence (fun y => φ y • N y) y := periodic_normal_flux hν hX hXp
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' E,divergence (fun y => φ y • N y) y :=
        (local_region_flux_eq hE hF he (by intro y hy; filter_upwards [hzero y hy] with z hz; rw [hz,zero_smul])).symm
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(μ : Measure NormalBundle) := (periodic_normal_flux hμ hX hXp).symm
      _ = ∫ z,φ z.1 ∂(μ : Measure NormalBundle) := by
        apply integral_congr_ae
        filter_upwards [haN] with z hz
        rw [real_inner_smul_right,hz,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
      _ = _ := hmass
  have hbF := normalMeasure_frontier_ae (E := openRepresentative F) (isOpen_openRepresentative F).measurableSet
    (hν.congr_ae (isMinimizerAt_openRepresentative_ae hW hF hmF).symm)
  have hid : (fun z : NormalBundle => φ z.1*‖N z.1-M z.1‖^2) =ᵐ[(ν : Measure NormalBundle)]
      (fun z => 2*(φ z.1-φ z.1*⟪(z.2 : Cover),N z.1⟫)) := by
    filter_upwards [haM,hbF] with z hz hzF
    by_cases hp0 : φ z.1=0
    · simp only [hp0,zero_mul,sub_self,mul_zero]
    · have hzU : quotientMap z.1∈U := by
        by_contra hh
        exact hp0 (hzero z.1 hh).self_of_nhds
      have hzE : quotientMap z.1∈frontier (openRepresentative E) := (hbound.symm.subset ⟨hzF,hzU⟩).1
      rw [hz,norm_sub_sq_real,hunit z.1 hzE,z.2.property,real_inner_comm]
      ring
  have hiφ := integrable_normal_base hφ.continuous ν
  have hiX : Integrable (fun z : NormalBundle => φ z.1*⟪(z.2 : Cover),N z.1⟫) (ν : Measure NormalBundle) := by
    simpa only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right] using
      (normalTest _ hX.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integrable_normal_base
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) ν
  have hiz : (∫ z,φ z.1*‖N z.1-M z.1‖^2 ∂(ν : Measure NormalBundle))=0 := by
    rw [integral_congr_ae hid,integral_const_mul,integral_sub hiφ hiX,hflux,sub_self,mul_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle =>
    mul_nonneg (hb z.1).1 (sq_nonneg _)) hi).mp hiz
  have hxzero := isMinimizerAt_periodic_ae_eq_boundary hW hF hmF hν
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) continuous_const
    (fun k y => by
      change φ (y+latticeVector k)*‖N (y+latticeVector k)-M (y+latticeVector k)‖^2=φ y*‖N y-M y‖^2
      rw [hp,hpN,hpM]) (fun _ _ => rfl) hae x hxF
  change φ x*‖N x-M x‖^2=0 at hxzero
  rw [(hone x hxT).self_of_nhds,one_mul] at hxzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hxzero))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) :
    IsPreconnected (frontier (openRepresentative F)) := by
  obtain ⟨μ,H,N,hμ,haN,hchart⟩ := isMinimizerAt_oriented_CMC_charts hV hE hmE
  obtain ⟨ν,K,M,hν,hM,hpM,haM,hgeom,_,hc|hq⟩ :=
    Periodic.isMinimizerAt_connected_or_zero_curvature hW hF hmF
  · exact hc
  · exfalso
    obtain ⟨a,ha,haU⟩ := hpatch
    let x := representative a
    have hxa : quotientMap x=a := quotientMap_representative a
    have hb := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
    have hxF : quotientMap x∈frontier (openRepresentative F) := by rw [hxa]; exact (hb ▸ (show a∈frontier (openRepresentative E)∩U from ⟨ha,haU⟩)).1
    have hloc := (isMinimizerAt_zero_curvature_local_normal hW hF hmF hν hM hpM haM
      (fun z hz => (hgeom z hz).1) hq x hxF).2
    have hxU : quotientMap x∈U := by rwa [hxa]
    have hnb : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈U := by
      have hh : Tendsto (fun v : Cover => quotientMap (x+v)) (𝓝 0) (𝓝 (quotientMap (x+0))) :=
        (continuous_quotientMap.comp (continuous_const.add continuous_id)).tendsto (0 : Cover)
      apply hh.eventually_mem
      simpa only [add_zero] using hU.mem_nhds hxU
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hloc.and hnb)
    let T := quotientMap '' Metric.ball x r
    have hT : IsOpen T := by
      dsimp only [T]
      rw [quotientMap_image_ball]
      exact Metric.isOpen_ball
    have haT : a∈T := ⟨x,Metric.mem_ball_self hr,hxa⟩
    have hTU : T⊆U := by
      rintro b ⟨z,hz,rfl⟩
      have hz' : z-x∈Metric.ball (0 : Cover) r := by simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
      simpa only [add_sub_cancel] using (hball hz').2
    have hnorm (b : Torus) (hbt : b∈frontier (openRepresentative E)∩T) :
        N (representative b)=M x := by
      obtain ⟨z,hz,hzb⟩ := hbt.2
      have hz' : z-x∈Metric.ball (0 : Cover) r := by simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
      have hzE : quotientMap z∈frontier (openRepresentative E)∩U := by rw [hzb]; exact ⟨hbt.1,hTU hbt.2⟩
      have hzF : quotientMap z∈frontier (openRepresentative F) := (hb ▸ hzE).1
      have hh : M z=M x := by
        simpa only [add_sub_cancel] using (hball hz').1.2 (by simpa only [add_sub_cancel] using hzF)
      rw [← hzb,periodic_representative hchart.normal_periodic]
      exact (isMinimizerAt_normal_local_eq hV hW hE hF hmE hmF hU he hμ hν
        hchart.normal_smooth hM hchart.normal_periodic hpM haN haM z hzE).trans hh
    exact isMinimizerAt_no_constant_normal_patch hV hE hmE hconn hμ hchart.normal_smooth
      hchart.normal_periodic haN hT ⟨a,ha,haT⟩ (M x) hnorm

theorem isMinimizerAt_boundary_eq_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) :
    frontier (openRepresentative E)=frontier (openRepresentative F) ∧
      ∃ (μ ν : FiniteMeasure NormalBundle) (N M : Cover → Cover),
        IsNormalMeasure E μ ∧ IsNormalMeasure F ν ∧
        ContDiff ℝ (⊤ : ℕ∞) N ∧ ContDiff ℝ (⊤ : ℕ∞) M ∧
        (∀ k x,N (x+latticeVector k)=N x) ∧ (∀ k x,M (x+latticeVector k)=M x) ∧
        (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
        (∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover)) ∧
        ∀ x,quotientMap x∈frontier (openRepresentative E) → N x=M x := by
  have hcF := isMinimizerAt_connected_of_shared_patch hV hW hE hF hmE hmF hconn hU he hpatch
  obtain ⟨μ,H,N,hμ,haN,hN⟩ := isMinimizerAt_oriented_CMC_charts hV hE hmE
  obtain ⟨ν,K,M,hν,haM,hM⟩ := isMinimizerAt_oriented_CMC_charts hW hF hmF
  have hb := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hnloc (a : Torus) (ha : a∈frontier (openRepresentative E)∩U) : N (representative a)=M (representative a) :=
    isMinimizerAt_normal_local_eq hV hW hE hF hmE hmF hU he hμ hν hN.normal_smooth hM.normal_smooth
      hN.normal_periodic hM.normal_periodic haN haM (representative a) (by simpa only [quotientMap_representative] using ha)
  have hh := hN.eq_of_patch isClosed_frontier isClosed_frontier hconn hcF hM hU hpatch hb hnloc
  refine ⟨hh.1,μ,ν,N,M,hμ,hν,hN.normal_smooth,hM.normal_smooth,hN.normal_periodic,hM.normal_periodic,haN,haM,?_⟩
  intro x hx
  simpa only [periodic_representative hN.normal_periodic,periodic_representative hM.normal_periodic] using hh.2 (quotientMap x) hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_replace_ae {E F U : Set Torus} (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    ((F\U)∪(E∩U) : Set Torus) =ᵐ[torusVolume] F := by
  filter_upwards [he] with a ha
  have hh : (a∈E ∧ a∈U) ↔ (a∈F ∧ a∈U) := Iff.of_eq ha
  change (a∈(F\U)∪(E∩U))=(a∈F)
  apply propext
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma local_replace_inter (E F U : Set Torus) : ((F\U)∪(E∩U))∩U=E∩U := by
  ext a
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma openRepresentative_local_ae_eq {E F U : Set Torus} (hU : IsOpen U)
    (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    openRepresentative E∩U=openRepresentative F∩U := by
  have hh := openRepresentative_local_eq hU (local_replace_inter E F U).symm
  rwa [openRepresentative_congr_ae (local_replace_ae he)] at hh

lemma isMinimizerAt_normal_local_ae_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  let F' := (F\U)∪(E∩U)
  have hF' : MeasurableSet F' := (hF.diff hU.measurableSet).union (hE.inter hU.measurableSet)
  have hrep : F' =ᵐ[torusVolume] F := local_replace_ae he
  exact isMinimizerAt_normal_local_eq hV hW hE hF' hmE ((isMinimizerAt_congr_ae hrep).mpr hmF)
    hU (local_replace_inter E F U).symm hμ (hν.congr_ae hrep.symm) hN hM hpN hpM haN haM x hx

lemma quotient_chart_ae {A : Set Cover} (hc : A⊆fundamentalCube)
    {P : Torus → Prop} (hP : MeasurableSet {a | a∈quotientMap '' A → P a})
    (he : ∀ᵐ x : Cover ∂volume,x∈A → P (quotientMap x)) :
    ∀ᵐ a ∂torusVolume,a∈quotientMap '' A → P a := by
  change ∀ᵐ a ∂Measure.map quotientMap (volume.restrict fundamentalCube),_
  apply (ae_map_iff measurable_quotientMap.aemeasurable hP).mpr
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_fundamentalCube] with x hx hxc hxa
  have hz : representative (quotientMap x)∈A := by
    change quotientMap x∈representative ⁻¹' A
    rw [← image_quotientMap_eq_preimage_representative hc]
    exact hxa
  rw [representative_quotientMap_of_mem hxc] at hz
  exact hx hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_common_boundary_phases {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    (ha : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ quotientMap cubeCenter∈U ∧
      ((E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) ∨
       (E∩U : Set Torus) =ᵐ[torusVolume] (Fᶜ∩U : Set Torus)) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,_,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmE (quotientMap cubeCenter) ha
  have hcov (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x (Metric.ball_subset_ball (by linarith) hx)
  have hgr : ContDiffOn ℝ 1 g (Metric.ball 0 (r/2)) :=
    (hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))
  obtain ⟨R,ρ,A,_,_,_,_,_,hρ,_,hA,hρA,_,hAc,_,hphaseE⟩ :=
    actual_centered_graph_phase_patch hV hE hmE ha hn (by linarith : 0<r/2) hg hg0 hgr hcov
  obtain ⟨S,σ,B,_,_,_,_,_,hσ,_,hB,hσB,_,_,_,hphaseF⟩ :=
    actual_centered_graph_phase_patch hW hF hmF (hb ▸ ha) hn (by linarith : 0<r/2) hg hg0 hgr (by rwa [← hb])
  let ε := min ρ σ
  have hε : 0<ε := lt_min hρ hσ
  let C := Metric.ball cubeCenter ε
  let U := quotientMap '' C
  have hCA : C⊆A := (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by
    have hh : ε≤ρ := min_le_left _ _; linarith))).trans hρA
  have hCB : C⊆B := (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by
    have hh : ε≤σ := min_le_right _ _; linarith))).trans hσB
  have hCc : C⊆fundamentalCube := fun x hx i => ⟨(hAc (hCA hx) i).1.le,(hAc (hCA hx) i).2⟩
  have hU : IsOpen U := by dsimp [U,C]; rw [quotientMap_image_ball]; exact Metric.isOpen_ball
  have hnz : ∀ᵐ x : Cover ∂volume,graphSignedHeight cubeCenter n g x≠0 := by
    rw [ae_iff]
    simpa only [graphSignedHeight,not_not,sub_eq_zero] using graph_trace_volume_zero cubeCenter hn hg.continuous
  have htransfer (G : Set Torus) (hG : MeasurableSet G)
      (he : ∀ᵐ x : Cover ∂volume,x∈C → (quotientMap x∈E ↔ quotientMap x∈G)) :
      (E∩U : Set Torus) =ᵐ[torusVolume] (G∩U : Set Torus) := by
    have hh := quotient_chart_ae hCc
      (show MeasurableSet {a : Torus | a∈U → (a∈E ↔ a∈G)} from
        hU.measurableSet.imp (hE.iff hG)) he
    filter_upwards [hh] with a ha
    simp only [mem_inter_iff]
    by_cases hu : a∈U
    · exact propext (and_congr_left (fun _ => ha hu))
    · simp only [hu,and_false]
  refine ⟨U,hU,⟨cubeCenter,Metric.mem_ball_self hε,rfl⟩,?_⟩
  rcases hphaseE with he|he <;> rcases hphaseF with hf|hf
  · left
    apply htransfer F hF
    filter_upwards [he,hf] with x hx hy hxc
    exact (hx (hCA hxc)).trans (hy (hCB hxc)).symm
  · right
    apply htransfer Fᶜ hF.compl
    filter_upwards [he,hf,hnz] with x hx hy hz hxc
    rw [mem_compl_iff,hy (hCB hxc),not_lt,hx (hCA hxc)]
    exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h hz⟩
  · right
    apply htransfer Fᶜ hF.compl
    filter_upwards [he,hf,hnz] with x hx hy hz hxc
    rw [mem_compl_iff,hy (hCB hxc),not_lt,hx (hCA hxc)]
    exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hz)⟩
  · left
    apply htransfer F hF
    filter_upwards [he,hf] with x hx hy hxc
    exact (hx (hCA hxc)).trans (hy (hCB hxc)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_common_boundary_phases {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ a∈U ∧
      ((E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) ∨
       (E∩U : Set Torus) =ᵐ[torusVolume] (Fᶜ∩U : Set Torus)) := by
  let b := a-quotientMap cubeCenter
  let E' := (fun z : Torus => z+b) ⁻¹' E
  let F' := (fun z : Torus => z+b) ⁻¹' F
  have hE' : MeasurableSet E' := (continuous_add_const b).measurable hE
  have hF' : MeasurableSet F' := (continuous_add_const b).measurable hF
  have hmE' : IsMinimizerAt V E' := isMinimizerAt_translation hmE b
  have hmF' : IsMinimizerAt W F' := isMinimizerAt_translation hmF b
  have hbd : frontier (openRepresentative E')=frontier (openRepresentative F') := by
    rw [frontier_openRepresentative_translation hE,frontier_openRepresentative_translation hF,hb]
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+b∈frontier (openRepresentative E)
    have he : quotientMap cubeCenter+b=a := by dsimp [b]; abel
    rw [he]
    exact ha
  obtain ⟨U,hU,haU,hph⟩ := isMinimizerAt_centered_common_boundary_phases hV hW hE' hF' hmE' hmF' hbd hcenter
  let T := (fun z : Torus => z-b) ⁻¹' U
  have hT : IsOpen T := hU.preimage (continuous_id.sub continuous_const)
  have haT : a∈T := by
    change a-b∈U
    simpa only [b,sub_sub_cancel] using haU
  have hback (G : Set Torus)
      (hh : (E'∩U : Set Torus) =ᵐ[torusVolume] (((fun z : Torus => z+b) ⁻¹' G)∩U : Set Torus)) :
      (E∩T : Set Torus) =ᵐ[torusVolume] (G∩T : Set Torus) := by
    have hmp := (measurePreserving_add_right torusVolume (-b)).quasiMeasurePreserving.preimage_ae_eq hh
    filter_upwards [hmp] with z hz
    change ((z + -b + b∈E) ∧ z + -b∈U)=((z + -b + b∈G) ∧ z + -b∈U) at hz
    change (z∈E ∧ z-b∈U)=(z∈G ∧ z-b∈U)
    simpa only [sub_eq_add_neg,add_assoc,neg_add_cancel,add_zero] using hz
  refine ⟨T,hT,haT,?_⟩
  rcases hph with h|h
  · exact Or.inl (hback F h)
  · exact Or.inr (hback Fᶜ h)

lemma normal_reverse_ae {ν : FiniteMeasure NormalBundle} {M : Cover → Cover}
    (hM : Continuous M) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂(ν.map reverseNormal : Measure NormalBundle),-M z.1=(z.2 : Cover) := by
  have hh := polar_reverse_normal (continuous_periodic_descent hM hpM).measurable (μ := ν) (N := fun a => M (representative a)) (by
    simpa only [periodic_representative hpM] using haM)
  simpa only [periodic_representative hpM] using hh

theorem isMinimizerAt_oriented_boundary_local_ae {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hb : frontier (openRepresentative E)=frontier (openRepresentative F))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (he : ∀ x,quotientMap x∈frontier (openRepresentative E) → N x=M x)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ U : Set Torus,IsOpen U ∧ a∈U ∧ (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus) := by
  obtain ⟨U,hU,haU,hph⟩ := isMinimizerAt_common_boundary_phases hV hW hE hF hmE hmF hb a ha
  rcases hph with hh|hh
  · exact ⟨U,hU,haU,hh⟩
  · exfalso
    let x := representative a
    have hx : quotientMap x∈frontier (openRepresentative E)∩U := by
      dsimp only [x]
      simpa only [quotientMap_representative,mem_inter_iff] using And.intro ha haU
    have hneg := isMinimizerAt_normal_local_ae_eq hV (by constructor <;> linarith [hW.1,hW.2] : 1-W∈Ioo 0 1)
      hE hF.compl hmE ((isMinimizerAt_compl ⟨hW.1.le,hW.2.le⟩).mpr hmF) hU hh hμ (isNormalMeasure_compl hF hν)
      hN hM.neg hpN (fun k y => by rw [hpM]) haN (normal_reverse_ae hM.continuous hpM haM) x hx
    have hxzero : N x=0 := by
      have hn := he x hx.1
      have hsum : (2:ℝ) • N x=0 := by
        rw [two_smul]
        calc N x+N x = -M x+M x := congrArg₂ (·+·) hneg hn
             _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)
    have hunit : ‖N x‖=1 := by
      apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
        (fun k y => by rw [hpN]) (fun _ _ => rfl) _ x hx.1
      filter_upwards [haN] with z hz
      rw [hz,z.2.property]
    norm_num [hxzero] at hunit

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sets_eq_of_common_frontier_local_eq {E F : Set Torus}
    (hb : frontier E=frontier F) (hne : (frontier E).Nonempty)
    (hloc : ∀ a∈frontier E,∃ U : Set Torus,IsOpen U ∧ a∈U ∧ E∩U=F∩U) : E=F := by
  let : ConnectedSpace Torus := quotientMap_surjective.connectedSpace continuous_quotientMap
  let D := (E∩Fᶜ)∪(F∩Eᶜ)
  have hfront : frontier D⊆frontier E := by
    intro a ha
    rcases frontier_union_subset (E∩Fᶜ) (F∩Eᶜ) ha with hh|hh
    · rcases frontier_inter_subset E Fᶜ hh.1 with hz|hz
      · exact hz.1
      · rw [frontier_compl,← hb] at hz
        exact hz.2
    · rcases frontier_inter_subset F Eᶜ hh.2 with hz|hz
      · exact hb.symm ▸ hz.1
      · rw [frontier_compl] at hz
        exact hz.2
  have havoid (a : Torus) (ha : a∈frontier E) : a∉closure D := by
    obtain ⟨U,hU,haU,he⟩ := hloc a ha
    intro hc
    obtain ⟨b,hbU,hbD⟩ := mem_closure_iff.mp hc U hU haU
    have hh := Set.ext_iff.mp he b
    simp only [mem_inter_iff,hbU,and_true] at hh
    change (b∈E ∧ b∉F) ∨ (b∈F ∧ b∉E) at hbD
    tauto
  have hcl : IsClopen D := isClopen_iff_frontier_eq_empty.mpr (eq_empty_iff_forall_notMem.mpr (by
    intro a ha
    exact havoid a (hfront ha) (frontier_subset_closure ha)))
  have hD : D=∅ := by
    by_contra hn
    have hdall := hcl.eq_univ (nonempty_iff_ne_empty.mpr hn)
    obtain ⟨a,ha⟩ := hne
    exact havoid a ha (subset_closure (by rw [hdall]; exact mem_univ a))
  ext a
  have hh : a∉D := by rw [hD]; exact notMem_empty a
  change ¬((a∈E ∧ a∉F) ∨ (a∈F ∧ a∉E)) at hh
  tauto

theorem isMinimizerAt_region_eq_of_shared_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hU : IsOpen U) (he : E∩U=F∩U)
    (hpatch : (frontier (openRepresentative E)∩U).Nonempty) : E =ᵐ[torusVolume] F := by
  obtain ⟨hb,μ,ν,N,M,hμ,hν,hN,hM,hpN,hpM,haN,haM,heN⟩ :=
    isMinimizerAt_boundary_eq_of_shared_patch hV hW hE hF hmE hmF hconn hU he hpatch
  have hop : openRepresentative E=openRepresentative F := by
    apply sets_eq_of_common_frontier_local_eq hb (hpatch.mono inter_subset_left)
    intro a ha
    obtain ⟨T,hT,haT,hh⟩ := isMinimizerAt_oriented_boundary_local_ae hV hW hE hF hmE hmF hb
      hμ hν hN hM hpN hpM haN haM heN a ha
    exact ⟨T,hT,haT,openRepresentative_local_ae_eq hT hh⟩
  apply (isMinimizerAt_openRepresentative_ae hV hE hmE).symm.trans
  rw [hop]
  exact isMinimizerAt_openRepresentative_ae hW hF hmF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_two_phase_frontier {V : ℝ} (hV : V∈Ioo 0 1)
    {E U : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected U)
    (h₁ : 0<torusVolume.real (E∩U)) (h₂ : 0<torusVolume.real (Eᶜ∩U)) :
    (frontier (openRepresentative E)∩U).Nonempty := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hmE
  have hp₁ : 0<torusVolume.real (openRepresentative E∩U) := by
    convert h₁ using 1
    exact congrArg ENNReal.toReal (measure_congr (hae.inter EventuallyEq.rfl))
  have hp₂ : 0<torusVolume.real ((openRepresentative E)ᶜ∩U) := by
    convert h₂ using 1
    exact congrArg ENNReal.toReal (measure_congr (hae.compl.inter EventuallyEq.rfl))
  simpa only [inter_comm] using preconnected_crosses_frontier hconn (isOpen_openRepresentative E)
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₁.ne')
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₂.ne')

theorem isMinimizerAt_reflection_symmetry_of_competitor {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hmF : IsMinimizerAt V (reflectionCompetitor i E (coordinateHalf i 0))) :
    coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E := by
  let B := coordinateHalf i 0
  let F := reflectionCompetitor i E B
  have hB : IsOpen B := coordinateHalf_open i
  have hd : Disjoint B (coordinateReflection i ⁻¹' B) := by
    dsimp only [B]
    rw [coordinateHalf_zero]
    exact reflection_sublevel_disjoint (coordinateSine_periodic i) (coordinateSine_reflection i)
  have hF : MeasurableSet F := reflectionCompetitor_measurable i hE hB.measurableSet
  have hvF : torusVolume.real F=V := by
    rw [Measure.real_def,hmF.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hv : torusVolume.real (E∩B)=V/2 := by
    have hh := reflectionCompetitor_realVolume i hE hB.measurableSet hd
    change torusVolume.real F=2*torusVolume.real (E∩B) at hh
    linarith
  have hsum : torusVolume.real (E∩B)+torusVolume.real (Eᶜ∩B)=1/2 := by
    rw [← measureReal_union (Disjoint.mono inter_subset_left inter_subset_left disjoint_compl_right)
      (hE.compl.inter hB.measurableSet)]
    have he : (E∩B)∪(Eᶜ∩B)=B := by ext z; simp only [mem_union,mem_inter_iff,mem_compl_iff]; tauto
    rw [he]
    exact coordinateHalf_realVolume i
  have hpatch := isMinimizerAt_two_phase_frontier hV hE hmE (coordinateHalf_preconnected i)
    (by rw [hv]; linarith [hV.1]) (by linarith [hV.2])
  have he : E =ᵐ[torusVolume] F := isMinimizerAt_region_eq_of_shared_patch hV hV hE hF hmE hmF
    hconn hB (reflectionCompetitor_retained i E hd) hpatch
  have hh := (coordinateReflection_measurePreserving i).quasiMeasurePreserving.preimage_ae_eq he
  rw [reflectionCompetitor_invariant] at hh
  exact hh.trans he.symm

theorem isMinimizerAt_exists_coordinate_reflection_measurable {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3) :
    ∃ a∈Icc (0 : ℝ) (1/2),let F := (fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E
      coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F := by
  obtain ⟨a,ha,hF,hmF,μ,hμ,hmR,hmS,hseam⟩ := isMinimizerAt_exists_bisecting_reflection_measurable hV hE hmE i
  refine ⟨a,ha,?_⟩
  have hcF : IsPreconnected (frontier (openRepresentative ((fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E))) := by
    rw [frontier_openRepresentative_translation hE]
    exact (Homeomorph.addRight _).isPreconnected_preimage.mpr hconn
  exact isMinimizerAt_reflection_symmetry_of_competitor hV hF hmF hcF i
    (by simpa only [coordinateHalf_zero] using hmR)

theorem isMinimizerAt_exists_coordinate_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3) :
    ∃ a∈Icc (0 : ℝ) (1/2),let F := (fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E
      coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F := by
  let E' := toMeasurable torusVolume E
  have hae : E' =ᵐ[torusVolume] E := hmE.1.1.toMeasurable_ae_eq
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hmE' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae hae).mpr hmE
  have hc' : IsPreconnected (frontier (openRepresentative E')) := by
    rw [openRepresentative_congr_ae hae]
    exact hconn
  obtain ⟨a,ha,hs⟩ := isMinimizerAt_exists_coordinate_reflection_measurable hV hE' hmE' hc' i
  refine ⟨a,ha,?_⟩
  have hf := (measurePreserving_add_right torusVolume (quotientMap (a • EuclideanSpace.single i 1))).quasiMeasurePreserving.preimage_ae_eq hae
  have hr := (coordinateReflection_measurePreserving i).quasiMeasurePreserving.preimage_ae_eq hf
  exact hr.symm.trans (hs.trans hf)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateReflection_add (i : Fin 3) (x y : Torus) :
    coordinateReflection i (x+y)=coordinateReflection i x+coordinateReflection i y := by
  ext j
  by_cases hj : j=i <;> simp [hj,add_comm]

lemma coordinateReflection_coordinate_shift {i j : Fin 3} (hji : j≠i) (a : ℝ) :
    coordinateReflection j (quotientMap (a • EuclideanSpace.single i 1))=
      quotientMap (a • EuclideanSpace.single i 1) := by
  rw [← quotientMap_coordinateReflection]
  congr 1
  ext k
  by_cases hk : k=j
  · subst k
    simp [hji]
  · simp [hk]

lemma reflection_invariance_translation {E : Set Torus} {i : Fin 3}
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) {b : Torus}
    (hb : coordinateReflection i b=b) :
    coordinateReflection i ⁻¹' ((fun z => z+b) ⁻¹' E) =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) := by
  have hh := (measurePreserving_add_right torusVolume b).quasiMeasurePreserving.preimage_ae_eq hs
  filter_upwards [hh] with z hz
  change (coordinateReflection i (z+b)∈E)=(z+b∈E) at hz
  change (coordinateReflection i z+b∈E)=(z+b∈E)
  simpa only [coordinateReflection_add,hb] using hz

theorem isMinimizerAt_exists_coordinate_symmetries_measurable {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ b : Torus,∀ i : Fin 3,coordinateReflection i ⁻¹' ((fun z => z+b) ⁻¹' E) =ᵐ[torusVolume]
      ((fun z => z+b) ⁻¹' E) := by
  classical
  have hfin (s : Finset (Fin 3)) : ∃ b : Torus,∀ i∈s,
      coordinateReflection i ⁻¹' ((fun z => z+b) ⁻¹' E) =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0,fun _ h => False.elim (Finset.notMem_empty _ h)⟩
    | @insert i s hi ih =>
      obtain ⟨b,hb⟩ := ih
      let F := (fun z : Torus => z+b) ⁻¹' E
      have hF : MeasurableSet F := (continuous_add_const b).measurable hE
      have hmF : IsMinimizerAt V F := isMinimizerAt_translation hmE b
      have hcF : IsPreconnected (frontier (openRepresentative F)) := by
        rw [frontier_openRepresentative_translation hE]
        exact (Homeomorph.addRight b).isPreconnected_preimage.mpr hc
      obtain ⟨a,ha,hs⟩ := isMinimizerAt_exists_coordinate_reflection_measurable hV hF hmF hcF i
      let c := quotientMap (a • EuclideanSpace.single i 1)
      have he : (fun z : Torus => z+c+b) ⁻¹' E=(fun z => z+(c+b)) ⁻¹' E := by
        simp only [add_assoc]
      refine ⟨c+b,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji|hjs
      · subst j
        simpa only [F,preimage_preimage,Function.comp_def,← add_assoc] using hs
      · have hji : j≠i := by intro h; subst j; exact hi hjs
        have hh := reflection_invariance_translation (hb j hjs) (coordinateReflection_coordinate_shift hji a)
        simpa only [preimage_preimage,Function.comp_def,add_assoc] using hh
  obtain ⟨b,hb⟩ := hfin Finset.univ
  exact ⟨b,fun i => hb i (Finset.mem_univ i)⟩

theorem isMinimizerAt_slab_or_coordinate_symmetries {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E) :
    (perimeter E=2 ∧ 1/Real.pi ≤ min V (1-V) ∧ StandardRegionAt V E) ∨
    (IsPreconnected (frontier (openRepresentative E)) ∧ ∃ b : Torus,∀ i : Fin 3,
      coordinateReflection i ⁻¹' ((fun z => z+b) ⁻¹' E) =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E)) := by
  rcases Periodic.isMinimizerAt_connected_or_standard_slab hV hmE with hc|hs
  · right
    refine ⟨hc,?_⟩
    let E' := toMeasurable torusVolume E
    have hae : E' =ᵐ[torusVolume] E := hmE.1.1.toMeasurable_ae_eq
    have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
    have hmE' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae hae).mpr hmE
    have hc' : IsPreconnected (frontier (openRepresentative E')) := by
      rwa [openRepresentative_congr_ae hae]
    obtain ⟨b,hb⟩ := isMinimizerAt_exists_coordinate_symmetries_measurable hV hE' hmE' hc'
    refine ⟨b,fun i => ?_⟩
    have hf := (measurePreserving_add_right torusVolume b).quasiMeasurePreserving.preimage_ae_eq hae
    have hr := (coordinateReflection_measurePreserving i).quasiMeasurePreserving.preimage_ae_eq hf
    exact hr.symm.trans ((hb i).trans hf)
  · exact Or.inl hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def reflectNormal (i : Fin 3) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (coordinateReflection i (quotientMap z.1)),
    ⟨coverCoordinateReflection i z.2,by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

lemma measurable_reflectNormal (i : Fin 3) : Measurable (reflectNormal i) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((coordinateReflection_continuous i).measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinateReflection i).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma reflectNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (i : Fin 3) (z : NormalBundle) :
    F (reflectNormal i z).1=F (coverCoordinateReflection i z.1) := by
  change F (representative (coordinateReflection i (quotientMap z.1)))=_
  rw [← quotientMap_coordinateReflection]
  exact periodic_representative hp _

lemma coverCoordinateReflection_inner (i : Fin 3) (x y : Cover) :
    ⟪coverCoordinateReflection i x,y⟫=⟪x,coverCoordinateReflection i y⟫ := by
  rw [← (coverCoordinateReflection i).inner_map_map x (coverCoordinateReflection i y),
    coverCoordinateReflection_involutive]

theorem isNormalMeasure_coordinateReflection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3) :
    IsNormalMeasure (coordinateReflection i ⁻¹' E) (μ.map (reflectNormal i)) := by
  constructor
  · have hm : ((μ.map (reflectNormal i)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_reflectNormal i)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_coordinateReflection_measurable i hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_reflectNormal i).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinateReflection i hF hE,← hμ.2 _ (coordinateReflectedField_admissible i hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinateReflection i z.2,F (reflectNormal i z).1⟫=
        ⟪(z.2 : Cover),coverCoordinateReflection i (F (coverCoordinateReflection i z.1))⟫
      rw [reflectNormal_periodic_eval hF.2.1,coverCoordinateReflection_inner]

lemma reflected_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    ∀ᵐ z ∂(μ.map (reflectNormal i) : Measure NormalBundle),
      coordinateReflectedField i N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_reflectNormal i).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinateReflection i).continuous.comp (hN.comp (coverCoordinateReflection i).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change coordinateReflectedField i N (reflectNormal i z).1=((reflectNormal i z).2 : Cover)
  rw [reflectNormal_periodic_eval (coordinateReflectedField_periodic i hp)]
  change coverCoordinateReflection i (N (coverCoordinateReflection i (coverCoordinateReflection i z.1)))=_
  rw [coverCoordinateReflection_involutive,hz]
  rfl

theorem isMinimizerAt_normal_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N x=coverCoordinateReflection i (N (coverCoordinateReflection i x)) := by
  have hmR := (isMinimizerAt_congr_ae hs).mpr hmE
  have hh : (E∩univ : Set Torus) =ᵐ[torusVolume] ((coordinateReflection i ⁻¹' E)∩univ : Set Torus) := by
    simpa only [inter_univ] using hs.symm
  exact isMinimizerAt_normal_local_ae_eq hV hV hE ((coordinateReflection_continuous i).measurable hE)
    hmE hmR isOpen_univ hh hμ (isNormalMeasure_coordinateReflection hE hμ i)
    hN (coordinateReflectedField_contDiff i hN) hp (coordinateReflectedField_periodic i hp)
    hae (reflected_normal_ae hN.continuous hp hae i) x ⟨hx,mem_univ _⟩

end CubicTorus

end
end

end OAI
