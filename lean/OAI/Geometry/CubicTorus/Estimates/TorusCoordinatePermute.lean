import Mathlib
import OAI.Geometry.CubicTorus.Estimates.TubeCalibration
import OAI.Geometry.CubicTorus.Estimates.CirclePeriodize

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem circle_equality_phase_interval {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    (hpos : volume K≠0) (hneg : volume Kᶜ≠0)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    ∃ z a b : ℝ,z≤a ∧ a<b ∧ b≤z+1 ∧
      (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1) : Set ℝ) =ᵐ[volume] Ioo a b ∧
      volume K=ENNReal.ofReal (b-a) := by
  classical
  have hzpos : volume ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' Kᶜ ∩ Ioc 0 1)≠0 := by
    have hh := hneg
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hK.compl] at hh
    simpa only [zero_add] using hh
  obtain ⟨z,hz,hgz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hzpos
    (ae_restrict_of_ae (circlePhaseGood_ae hK))
  have hz0 : (z : AddCircle (1 : ℝ))∉K := hz.1
  have hcpos : volume (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1))≠0 := by
    rwa [← AddCircle.add_projection_respects_measure (1 : ℝ) z hK]
  have hg : ∀ᵐ t : ℝ ∂volume,circlePhaseGood K t ∧ t≠z+1 :=
    (circlePhaseGood_ae hK).and (volume.ae_ne (z+1))
  obtain ⟨w,hw,hgw,hwne⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcpos (ae_restrict_of_ae hg)
  have hwi : w∈Ioo z (z+1) := ⟨hw.2.1,lt_of_le_of_ne hw.2.2 hwne⟩
  let S : Set ℝ := {t | t∈Ioo z (z+1) ∧ circlePhaseGood K t ∧ (t : AddCircle (1 : ℝ))∈K}
  have hSne : S.Nonempty := ⟨w,hwi,hgw,hw.1⟩
  have hlower : BddBelow S := ⟨z,fun _ ht ↦ ht.1.1.le⟩
  have hupper : BddAbove S := ⟨z+1,fun _ ht ↦ ht.1.2.le⟩
  let a := sInf S
  let b := sSup S
  have hza : z≤a := le_csInf hSne (fun _ ht ↦ ht.1.1.le)
  have hbz : b≤z+1 := csSup_le hSne (fun _ ht ↦ ht.1.2.le)
  have hab : a≤b := csInf_le_csSup hSne hlower hupper
  have hmid (x : ℝ) (hx : x∈Ioo a b) (hgx : circlePhaseGood K x) :
      (x : AddCircle (1 : ℝ))∈K := by
    obtain ⟨u,hu,hux⟩ := exists_lt_of_csInf_lt hSne hx.1
    obtain ⟨v,hv,hxv⟩ := exists_lt_of_lt_csSup hSne hx.2
    by_contra h0
    exact circle_no_four_alternations hm hK hn hP hu.1.1.le hux.le hxv.le
      (by linarith [hv.1.2]) hgz hu.2.1 hgx hv.2.1 hz0 hu.2.2 h0 hv.2.2
  have hae : (((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K) ∩ Ioc z (z+1) : Set ℝ) =ᵐ[volume]
      Ioo a b := by
    filter_upwards [hg,volume.ae_ne a,volume.ae_ne b] with x hx hxa hxb
    apply propext
    constructor
    · intro h
      have hxS : x∈S := ⟨⟨h.2.1,lt_of_le_of_ne h.2.2 hx.2⟩,hx.1,h.1⟩
      exact ⟨lt_of_le_of_ne (csInf_le hlower hxS) (Ne.symm hxa),
        lt_of_le_of_ne (le_csSup hupper hxS) hxb⟩
    · intro h
      exact ⟨hmid x h hx.1,lt_of_le_of_lt hza h.1,h.2.le.trans hbz⟩
  have hvol : volume K=ENNReal.ofReal (b-a) := by
    rw [AddCircle.add_projection_respects_measure (1 : ℝ) z hK,measure_congr hae,
      Real.volume_Ioo]
  have hab' : a<b := by
    by_contra hh
    have he : b=a := le_antisymm (le_of_not_gt hh) hab
    rw [hvol,he,sub_self,ENNReal.ofReal_zero] at hpos
    exact hpos rfl
  exact ⟨z,a,b,hza,hab',hbz,hae,hvol⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_coe_integer_zero (n : ℤ) : ((n : ℝ) : AddCircle (1 : ℝ))=0 := by
  have he : (n : ℝ)=n • (1 : ℝ) := by simp
  rw [he,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]

lemma circle_image_interval_eq_ball {a b : ℝ} (hab : a≤b) (hw : b-a≤1) :
    (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Ioo a b =
      Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2) := by
  rcases hab.eq_or_lt with rfl | _
  · simp
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    rw [Metric.mem_ball,dist_eq_norm,← AddCircle.coe_sub]
    have ht' : |t-(a+b)/2|<(b-a)/2 := abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by
      simpa only [abs_one] using (show |t-(a+b)/2|≤1/2 by linarith only [hw,ht']))]
    exact ht'
  · intro hx
    obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [Metric.mem_ball,dist_eq_norm,← AddCircle.coe_sub,AddCircle.norm_eq] at hx
    simp only [inv_one,one_mul,mul_one] at hx
    refine ⟨t-round (t-(a+b)/2),?_,?_⟩
    · have hh := abs_lt.mp hx
      constructor <;> linarith [hh.1,hh.2]
    · change ((t-(round (t-(a+b)/2) : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
      rw [AddCircle.coe_sub,circle_coe_integer_zero,sub_zero]

lemma circle_interval_ae_ball {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {z a b : ℝ} (hza : z≤a) (hab : a≤b) (hbz : b≤z+1)
    (hae : ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc z (z+1) : Set ℝ)
      =ᵐ[volume] Ioo a b) :
    K =ᵐ[volume] Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2) := by
  have he := circle_image_interval_eq_ball hab (show b-a≤1 by linarith)
  have hi (t : ℝ) (ht : t∈Ioc z (z+1)) :
      (t : AddCircle (1 : ℝ))∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2)
        ↔ t∈Ioo a b := by
    rw [← he]
    constructor
    · rintro ⟨u,hu,heq⟩
      have hui : u∈Ioc z (z+1) := ⟨lt_of_le_of_lt hza hu.1,hu.2.le.trans hbz⟩
      have hut : u=t := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hui ht).mp heq
      exact hut ▸ hu
    · intro ht'
      exact ⟨t,ht',rfl⟩
  have hp := AddCircle.measurePreserving_mk (1 : ℝ) z
  rw [← hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable ?_).mpr
  · apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hae] with t ht hti
    apply propext
    change ((t : AddCircle (1 : ℝ))∈K ↔ (t : AddCircle (1 : ℝ))∈Metric.ball _ _)
    rw [hi t hti]
    have hh := congrArg (fun p : Prop ↦ p) ht
    exact (and_iff_left hti).symm.trans
      (show ((t : AddCircle (1 : ℝ))∈K ∧ t∈Ioc z (z+1)) ↔ t∈Ioo a b from Iff.of_eq hh)
  · change MeasurableSet {x | (x∈K) = (x∈Metric.ball _ _)}
    have heq : {x : AddCircle (1 : ℝ) | (x∈K) =
        (x∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2))} =
        {x : AddCircle (1 : ℝ) | x∈K ↔
          x∈Metric.ball (((a+b)/2 : ℝ) : AddCircle (1 : ℝ)) ((b-a)/2)} := by
      ext x
      exact propext_iff
    rw [heq]
    exact hK.iff Metric.isOpen_ball.measurableSet

theorem circle_equality_phase_ball {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {V : ℝ} (hV : V∈Ioo 0 1) (hvol : volume K=ENNReal.ofReal V)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    ∃ c : AddCircle (1 : ℝ),K =ᵐ[volume] Metric.ball c (V/2) := by
  have hpos : volume K≠0 := by rw [hvol]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hV.1)
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl hK (measure_ne_top _ _),hvol]
    have hu : volume (univ : Set (AddCircle (1 : ℝ)))=1 := by simp
    rw [hu]
    exact ne_of_gt (tsub_pos_iff_lt.mpr ((ENNReal.ofReal_lt_one).mpr hV.2))
  obtain ⟨z,a,b,hza,hab,hbz,hae,hv⟩ := circle_equality_phase_interval hm hK hpos hneg hn hP
  have hw : b-a=V := by
    have hh := congrArg ENNReal.toReal (hv.symm.trans hvol)
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),ENNReal.toReal_ofReal hV.1.le] using hh
  refine ⟨(((a+b)/2 : ℝ) : AddCircle (1 : ℝ)),?_⟩
  rw [← hw]
  exact circle_interval_ae_ball hK hza hab.le hbz hae

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def torusCoordinatePermute (e : Fin 3 ≃ Fin 3) : Torus ≃ᵢ Torus where
  toFun x := WithLp.toLp 2 (fun i ↦ x (e i))
  invFun x := WithLp.toLp 2 (fun i ↦ x (e.symm i))
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  isometry_toFun x y := by
    rw [PiLp.edist_eq_of_L2,PiLp.edist_eq_of_L2]
    exact congrArg (fun s : ℝ≥0∞ ↦ s^(1/2 : ℝ))
      (e.sum_comp (fun i ↦ edist (x i) (y i)^2))

lemma coordinate_ball_isometric_slab (V : ℝ) (i : Fin 3) (c : AddCircle (1 : ℝ)) :
    ∃ φ : Torus ≃ᵢ Torus,φ '' canonicalSlab V =
      (fun x : Torus ↦ x i) ⁻¹' Metric.ball c (V/2) := by
  classical
  let q : Torus := WithLp.toLp 2 (Pi.single i c)
  let φ := (torusCoordinatePermute (Equiv.swap (0 : Fin 3) i)).trans (IsometryEquiv.addRight q)
  have he (y : Torus) : (φ y) i=y 0+c := by
    change y (Equiv.swap (0 : Fin 3) i i)+q i=y 0+c
    simp [q]
  refine ⟨φ,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change dist ((φ y) i) c<V/2
    rw [he]
    change ‖y 0‖ < V/2 at hy
    simpa only [dist_eq_norm,add_sub_cancel_right] using hy
  · intro hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    change ‖(φ.symm x) 0‖<V/2
    have hg := he (φ.symm x)
    rw [φ.apply_symm_apply] at hg
    change dist (x i) c<V/2 at hx
    rw [hg] at hx
    simpa only [dist_eq_norm,add_sub_cancel_right] using hx

lemma integerCharacter_single (i : Fin 3) (n : ℤ) (x : Torus) :
    integerCharacter (Pi.single i n) x=n • x i := by
  classical
  simp [integerCharacter,Pi.single_apply]

theorem unit_character_equality_congruent_slab {m : Fin 3 → ℤ} (hm : m≠0)
    {K : Set (AddCircle (1 : ℝ))} (hK : MeasurableSet K)
    {V : ℝ} (hV : V∈Ioo 0 1) (hvol : volume K=ENNReal.ofReal V)
    (hn : ‖latticeVector m‖=1) (hP : perimeter ((integerCharacter m) ⁻¹' K)=2) :
    CongruentAE ((integerCharacter m) ⁻¹' K) (canonicalSlab V) := by
  obtain ⟨c,hc⟩ := circle_equality_phase_ball hm hK hV hvol hn hP
  have hpre : (integerCharacter m) ⁻¹' K =ᵐ[torusVolume]
      (integerCharacter m) ⁻¹' Metric.ball c (V/2) :=
    (integerCharacter_measurePreserving hm).quasiMeasurePreserving.ae_eq_comp hc
  obtain ⟨i,hi⟩ := integer_lattice_norm_one_coordinate hn
  rcases hi with hi|hi
  · obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V i c
    refine ⟨φ,?_⟩
    rw [hφ]
    have he : (integerCharacter m) ⁻¹' Metric.ball c (V/2)=
        (fun x : Torus ↦ x i) ⁻¹' Metric.ball c (V/2) := by
      subst m
      ext x
      simp only [mem_preimage,integerCharacter_single,one_zsmul]
    exact hpre.trans (Eventually.of_forall (congrFun (congrArg (fun s : Set Torus ↦ (s : Torus → Prop)) he)))
  · obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V i (-c)
    refine ⟨φ,?_⟩
    rw [hφ]
    have he : (integerCharacter m) ⁻¹' Metric.ball c (V/2)=
        (fun x : Torus ↦ x i) ⁻¹' Metric.ball (-c) (V/2) := by
      subst m
      ext x
      simp only [mem_preimage,integerCharacter_single,neg_one_zsmul,Metric.mem_ball]
      rw [← dist_neg_neg (x i) (-c),neg_neg]
    exact hpre.trans (Eventually.of_forall (congrFun (congrArg (fun s : Set Torus ↦ (s : Torus → Prop)) he)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem Periodic.isMinimizerAt_connected_or_coordinate_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ CongruentAE E (canonicalSlab V)) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hrep : openRepresentative F=openRepresentative E := by
    unfold openRepresentative
    have hc : Fᶜ =ᵐ[torusVolume] Eᶜ := by
      filter_upwards [hae] with z hz
      exact congrArg Not hz
    exact congrArg (fun A : Set Torus ↦ Aᶜ) (volumeSupport_congr_ae hc)
  rcases Periodic.isMinimizerAt_connected_or_unit_integer_phase hV hF hmF with hc|
    ⟨hper,m,K,hm,hn,hK,he,hvol⟩
  · exact Or.inl (hrep ▸ hc)
  have hc : (integerCharacter m) ⁻¹' K =ᵐ[torusVolume] E := by
    rw [← he]
    exact (isMinimizerAt_openRepresentative_ae hV hF hmF).trans hae
  have hpE : perimeter E=2 := (perimeter_congr_ae hae).symm.trans hper
  have hpK : perimeter ((integerCharacter m) ⁻¹' K)=2 :=
    (perimeter_congr_ae hc).trans hpE
  obtain ⟨φ,hφ⟩ := unit_character_equality_congruent_slab hm hK.measurableSet hV hvol hn hpK
  refine Or.inr ⟨hpE,?_,φ,hc.symm.trans hφ⟩
  have hup := isMinimizerAt_perimeter_le_candidateProfile hV hmin
  rw [hpE] at hup
  have hvnon : 0≤ min V (1-V) := le_min hV.1.le (by linarith [hV.2])
  have hcand : 0≤candidateProfile V := by
    unfold candidateProfile
    exact le_min (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))
      (le_min (by positivity) (by positivity))
  have h2 : (2 : ℝ)≤candidateProfile V := by
    simpa only [ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hcand] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
  have ht : candidateProfile V≤2*Real.sqrt (Real.pi*min V (1-V)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrt : 1≤Real.sqrt (Real.pi*min V (1-V)) := by linarith
  have hpiv : 1≤Real.pi*min V (1-V) := by
    have hs := Real.sq_sqrt (show 0≤Real.pi*min V (1-V) by positivity)
    nlinarith [Real.sqrt_nonneg (Real.pi*min V (1-V))]
  exact (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

lemma isMinimizerAt_frontier_compl {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative Eᶜ)=frontier (openRepresentative E) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have haec : Fᶜ =ᵐ[torusVolume] Eᶜ := by
    filter_upwards [hae] with z hz
    exact congrArg Not hz
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  calc
    frontier (openRepresentative Eᶜ)=frontier (openRepresentative Fᶜ) :=
      congrArg frontier (openRepresentative_congr_ae haec).symm
    _=frontier (openRepresentative F) := by
      rw [isMinimizerAt_frontier_openRepresentative hV hF hmF,
        isMinimizerAt_frontier_openRepresentative hVc hF.compl
          ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmF),compl_compl,inter_comm]
    _=frontier (openRepresentative E) := congrArg frontier (openRepresentative_congr_ae hae)

theorem Periodic.isMinimizerAt_connected_or_standard_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E) := by
  by_cases hc : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hc
  obtain ⟨hp,hr,hsl⟩ := (isMinimizerAt_connected_or_coordinate_slab hV hmin).resolve_left hc
  refine Or.inr ⟨hp,hr,?_⟩
  unfold StandardRegionAt
  split_ifs with hhalf
  · exact Or.inr (Or.inr ⟨hr.trans (min_le_left _ _),hsl⟩)
  · have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
    have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
    have hnc : ¬IsPreconnected (frontier (openRepresentative Eᶜ)) := by
      rwa [isMinimizerAt_frontier_compl hV hmin]
    obtain ⟨_,_,hslc⟩ := (isMinimizerAt_connected_or_coordinate_slab hVc hmc).resolve_left hnc
    exact Or.inr (Or.inr ⟨hr.trans (min_le_right _ _),hslc⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_integral_curvature_zero_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1))
    (hz : (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle))=0) :
    ¬IsPreconnected (frontier (openRepresentative E)) ∧
      perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E := by
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hnn : ∀ᵐ z ∂(μ : Measure NormalBundle),
      0≤coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) := by
    filter_upwards [hbd,hae] with z hzb hzu
    exact isMinimizerAt_normal_curvature_nonnegative hV hE hmin hμ hN hp
      (hae.mono fun _ h ↦ h.1) z.1 hzb hzu.2
  have hq0 := (integral_eq_zero_iff_of_nonneg_ae hnn
    (integrable_normal_base (normal_curvature_continuous hN) μ)).mp hz
  have hunit : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ‖N x‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
      continuous_const (fun m x ↦ by rw [hp]) (fun _ _ ↦ rfl)
    filter_upwards [hae] with z hzn
    rw [hzn.1,z.2.property]
  let R := regularizedNormal N
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := regularizedNormal_contDiff hN
  have hRp : ∀ m x,R (x+latticeVector m)=R x := regularizedNormal_periodic hp
  have heq : ∀ᵐ z ∂(μ : Measure NormalBundle),R=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hae] with z hzn
    exact regularizedNormal_eventuallyEq hzn.2
  have hRa : ∀ᵐ z ∂(μ : Measure NormalBundle),R z.1=(z.2 : Cover) := by
    filter_upwards [hae,heq] with z hzn hze
    exact hze.eq_of_nhds.trans hzn.1
  have hRu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖R y‖=1 := by
    intro x hx
    exact regularizedNormal_unit_near hN.continuous (by rw [hunit x hx]; norm_num)
  have hR0 : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      coverTrace ((fderiv ℝ R x).comp (fderiv ℝ R x))=0 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (normal_curvature_continuous hR) continuous_const
      (fun m x ↦ by simp only [fderiv_periodic hRp]) (fun _ _ ↦ rfl)
    filter_upwards [hq0,heq] with z hqz hze
    simpa only [hze.fderiv_eq,Pi.zero_apply] using hqz
  have hdisc := isMinimizerAt_zero_curvature_not_preconnected hV hE hmin hμ hR hRp hRa hRu hR0
  exact ⟨hdisc,(Periodic.isMinimizerAt_connected_or_standard_slab hV hmin).resolve_left hdisc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_curvature_integral_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    0<(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle)) := by
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hn : 0≤(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
      ∂(μ : Measure NormalBundle)) := by
    apply integral_nonneg_of_ae
    filter_upwards [hbd,hae] with z hzb hzu
    exact isMinimizerAt_normal_curvature_nonnegative hV hE hmin hμ hN hp
      (hae.mono fun _ h ↦ h.1) z.1 hzb hzu.2
  apply lt_of_le_of_ne hn
  intro hz
  exact (isMinimizerAt_integral_curvature_zero_slab hV hE hmin hμ hN hp hae hz.symm).1 hc

namespace Periodic

theorem isMinimizerAt_connected_strict_support {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      deriv (deriv C) V<0 := by
  obtain ⟨μ,H,N,C,hμ,hN,hp,hae,hCMC,hs,hd,hdd⟩ :=
    isMinimizerAt_exact_profile_hessian hV hE hmin
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmin hc hμ hN hp hae
  refine ⟨μ,H,C,hμ,hCMC,hs,hd,?_⟩
  have hprod : (isoperimetricProfile V)^2*deriv (deriv C) V<0 := by
    rw [hdd]; linarith
  by_contra! hnon
  exact (mul_nonneg (sq_nonneg _) hnon).not_gt hprod

theorem isMinimizerAt_profile_local_min_slab {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hloc : IsLocalMin isoperimetricProfile V) :
    perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E := by
  apply (isMinimizerAt_connected_or_standard_slab hV hmin).resolve_left
  intro hc
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rwa [openRepresentative_congr_ae hae]
  obtain ⟨μ,H,C,hμ,hCMC,hs,hd,hdd⟩ := isMinimizerAt_connected_strict_support hV hF hmF hcF
  have hmC : IsLocalMin C V := by
    filter_upwards [hloc,hs.above] with W hW hWa
    change C V≤C W
    rw [hs.contact]
    exact hW.trans hWa
  exact (Reduction.second_deriv_nonneg_of_local_min hmC hs.smooth.continuousAt).not_gt hdd

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Reduction

lemma second_deriv_nonneg_of_right_min {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hd : deriv f x=0)
    (hmin : ∀ᶠ y in 𝓝 x,x<y → f x≤f y) : 0≤deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have he : ∀ᶠ y in 𝓝 x,x<y → f y=f x := by
    filter_upwards [hmin,hmax] with y hy hmy
    exact fun hxy ↦ le_antisymm hmy (hy hxy)
  have hn := deriv_neg_right_of_sign_deriv
    ((eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hd).filter_mono nhdsWithin_le_nhds)
  have hfalse : ∀ᶠ y in 𝓝[>] x,False := by
    filter_upwards [he.eventually_nhds.filter_mono nhdsWithin_le_nhds,
      hn,self_mem_nhdsWithin] with y hy hny hxy
    have heq : f=ᶠ[𝓝 y](fun _ ↦ f x) := by
      filter_upwards [hy,Ioi_mem_nhds hxy] with z hz hxz
      exact hz hxz
    have hz := heq.deriv_eq
    simp only [deriv_const'] at hz
    exact hny.ne hz
  obtain ⟨y,hy⟩ := hfalse.exists
  exact hy

end Reduction
namespace Periodic

theorem isMinimizerAt_connected_positive_CMC {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧ 0<H ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      deriv (deriv C) V<0 := by
  obtain ⟨μ,H,C,hμ,hCMC,hs,hd,hdd⟩ :=
    isMinimizerAt_connected_strict_support ⟨hV.1,by linarith [hV.2]⟩ hE hmin hc
  have hdnon := profile_upper_support_slope_nonneg hV hs
  have hdpos : 0<deriv C V := by
    apply lt_of_le_of_ne hdnon
    intro he
    have hr : ∀ᶠ W in 𝓝 V,V<W → C V≤C W := by
      filter_upwards [hs.above,Iio_mem_nhds hV.2] with W hW hWh hVW
      rw [hs.contact]
      exact (monotoneOn_isoperimetricProfile_half ⟨hV.1.le,hV.2.le⟩
        ⟨hV.1.le.trans hVW.le,hWh.le⟩ hVW.le).trans hW
    exact (Reduction.second_deriv_nonneg_of_right_min hs.smooth.continuousAt he.symm hr).not_gt hdd
  exact ⟨μ,H,C,hμ,by rw [hd] at hdpos; linarith,hCMC,hs,hd,hdd⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Reduction

lemma second_deriv_nonneg_of_left_min {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hd : deriv f x=0)
    (hmin : ∀ᶠ y in 𝓝 x,y<x → f x≤f y) : 0≤deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have he : ∀ᶠ y in 𝓝 x,y<x → f y=f x := by
    filter_upwards [hmin,hmax] with y hy hmy
    exact fun hxy ↦ le_antisymm hmy (hy hxy)
  have hn := deriv_pos_left_of_sign_deriv
    ((eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hd).filter_mono nhdsWithin_le_nhds)
  have hfalse : ∀ᶠ y in 𝓝[<] x,False := by
    filter_upwards [he.eventually_nhds.filter_mono nhdsWithin_le_nhds,
      hn,self_mem_nhdsWithin] with y hy hny hxy
    have heq : f=ᶠ[𝓝 y](fun _ ↦ f x) := by
      filter_upwards [hy,Iio_mem_nhds hxy] with z hz hxz
      exact hz hxz
    have hz := heq.deriv_eq
    simp only [deriv_const'] at hz
    exact hny.ne' hz
  obtain ⟨y,hy⟩ := hfalse.exists
  exact hy

end Reduction
namespace Periodic

theorem connected_support_of_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ C : ℝ → ℝ,Reduction.UpperSupport isoperimetricProfile C V ∧
      deriv C V=H/2 ∧ deriv (deriv C) V<0 := by
  obtain ⟨N,C,hN,hp,hae,hs,hd,hdd⟩ := profile_hessian_of_CMC hV hE hmin hμ hCMC
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmin hc hμ hN hp hae
  refine ⟨C,hs,hd,?_⟩
  have hprod : (isoperimetricProfile V)^2*deriv (deriv C) V<0 := by
    rw [hdd]; linarith
  by_contra! hnon
  exact (mul_nonneg (sq_nonneg _) hnon).not_gt hprod

theorem connected_CMC_strict_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    (V<1/2 → 0<H) ∧ (1/2<V → H<0) := by
  obtain ⟨C,hs,hd,hdd⟩ := connected_support_of_CMC hV hE hmin hc hμ hCMC
  constructor
  · intro hh
    have hn := profile_upper_support_slope_nonneg ⟨hV.1,hh⟩ hs
    have hp : 0<deriv C V := by
      apply lt_of_le_of_ne hn
      intro he
      have hr : ∀ᶠ W in 𝓝 V,V<W → C V≤C W := by
        filter_upwards [hs.above,Iio_mem_nhds hh] with W hW hWh hVW
        rw [hs.contact]
        exact (monotoneOn_isoperimetricProfile_half ⟨hV.1.le,hh.le⟩
          ⟨hV.1.le.trans hVW.le,hWh.le⟩ hVW.le).trans hW
      exact (Reduction.second_deriv_nonneg_of_right_min hs.smooth.continuousAt he.symm hr).not_gt hdd
    rw [hd] at hp
    linarith
  · intro hh
    have hn := profile_upper_support_slope_nonpos ⟨hh,hV.2⟩ hs
    have hp : deriv C V<0 := by
      apply lt_of_le_of_ne hn
      intro he
      have hr : ∀ᶠ W in 𝓝 V,W<V → C V≤C W := by
        filter_upwards [hs.above,Ioi_mem_nhds hh] with W hW hWh hWV
        rw [hs.contact]
        exact (antitoneOn_isoperimetricProfile_half
          ⟨hWh.le,hWV.le.trans hV.2.le⟩ ⟨hh.le,hV.2.le⟩ hWV.le).trans hW
      exact (Reduction.second_deriv_nonneg_of_left_min hs.smooth.continuousAt he hr).not_gt hdd
    rw [hd] at hp
    linarith

theorem isMinimizerAt_zero_CMC_slab {V : ℝ} (hV : V∈Ioo 0 1) (hvhalf : V≠1/2)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=0) :
    perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E := by
  apply (isMinimizerAt_connected_or_standard_slab hV hmin).resolve_left
  intro hc
  have hs := connected_CMC_strict_sign hV hE hmin hc hμ (H := 0)
    (fun F hF hp ↦ by simpa only [zero_mul] using hCMC F hF hp)
  rcases lt_or_gt_of_ne hvhalf with hh|hh
  · exact (lt_irrefl 0) (hs.1 hh)
  · exact (lt_irrefl 0) (hs.2 hh)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTraceSquare_symmetric_equality {L : Plane →L[ℝ] Plane}
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫)
    (he : (planeTrace L)^2=2*planeTraceSquare L) :
    L=(planeTrace L/2) • ContinuousLinearMap.id ℝ Plane := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  simp only [planeTraceSquare,planeTrace,Fin.sum_univ_two,hc] at he
  have ha : L (EuclideanSpace.single 0 1) 0=L (EuclideanSpace.single 1 1) 1 := by
    nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0-L (EuclideanSpace.single 1 1) 1),
      sq_nonneg (L (EuclideanSpace.single 1 1) 0)]
  have hb : L (EuclideanSpace.single 1 1) 0=0 := by
    nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0-L (EuclideanSpace.single 1 1) 1),
      sq_nonneg (L (EuclideanSpace.single 1 1) 0)]
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => rw [plane_decompose v,map_add,map_smul,map_smul]
  ext i
  fin_cases i <;> simp [planeTrace,Fin.sum_univ_two,ha,hb,hc] <;> ring

theorem graph_curvature_equality_umbilic {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    (he : (planeDivergence (fun z ↦ cmcFlux (gradient g z)) y)^2=
      2*graphSquaredSecondFundamentalForm g y) :
    graphShapeOperator g y=
      (planeDivergence (fun z ↦ cmcFlux (gradient g z)) y/2) •
        ContinuousLinearMap.id ℝ Plane := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  let C := cmcCompress p
  let D := (cmcWeight p)⁻¹ • (C.comp L)
  have hS : graphShapeOperator g y=C.comp D := by
    apply ContinuousLinearMap.ext
    intro v
    change cmcJacobian p (L v)=C ((cmcWeight p)⁻¹ • C (L v))
    rw [map_smul]
    exact cmcJacobian_compress p (L v)
  have hB : ∀ v w : Plane,⟪(D.comp C) v,w⟫=⟪v,(D.comp C) w⟫ := by
    intro v w
    change ⟪(cmcWeight p)⁻¹ • C (L (C v)),w⟫=⟪v,(cmcWeight p)⁻¹ • C (L (C w))⟫
    rw [real_inner_smul_left,real_inner_smul_right]
    congr 1
    rw [cmcCompress_symm,plane_hessian_symmetric hg,← cmcCompress_symm]
  have ht : planeDivergence (fun z ↦ cmcFlux (gradient g z)) y=planeTrace (D.comp C) := by
    rw [planeDivergence_eq_trace,cmcFlux_gradient_fderiv hg,hS,planeTrace_comp_comm]
  have hb := planeTraceSquare_symmetric_equality hB (by
    rw [← ht]
    simpa only [graphSquaredSecondFundamentalForm,hS,planeTraceSquare_comp_comm] using he)
  rw [ht,hS]
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : Plane →L[ℝ] Plane ↦ C (A (cmcStretch p v))) hb
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,C,cmcCompress_stretch,map_smul] using hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem graph_umbilic_CMC_center {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r H : ℝ}
    (hr : 0<r) (hH : H≠0)
    (hcmc : ∀ y∈Metric.ball (0 : Plane) r,
      planeDivergence (fun z ↦ cmcFlux (gradient g z)) y=H)
    (he : ∀ y∈Metric.ball (0 : Plane) r,H^2=2*graphSquaredSecondFundamentalForm g y) :
    ∀ y∈Metric.ball (0 : Plane) r,
      normalGraph n g y+(2/H) • graphSlopeNormal n (gradient g y)=
        normalGraph n g 0+(2/H) • graphSlopeNormal n (gradient g 0) := by
  let X := normalGraph n g
  let N := fun y ↦ graphSlopeNormal n (gradient g y)
  have hX : Differentiable ℝ X := fun y ↦
    (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt
  have hN : Differentiable ℝ N :=
    ((graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)).differentiable (by simp)
  have hd : Differentiable ℝ (fun y ↦ X y+(2/H) • N y) := hX.add (hN.const_smul (2/H))
  have hprod : (2/H)*(H/2)=1 := by field_simp
  have hz : ∀ y∈Metric.ball (0 : Plane) r,
      fderiv ℝ (fun y ↦ X y+(2/H) • N y) y=0 := by
    intro y hy
    have hs := graph_curvature_equality_umbilic hg y (by rw [hcmc y hy]; exact he y hy)
    rw [hcmc y hy] at hs
    change fderiv ℝ (X+(2/H) • N) y=0
    rw [fderiv_add (hX y) ((hN y).const_smul (2/H)),fderiv_const_smul (hN y)]
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply,smul_apply,zero_apply]
    change fderiv ℝ X y v+(2/H) • fderiv ℝ N y v=0
    rw [graph_weingarten hn hg,hs]
    simp only [smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_neg,smul_smul,hprod,one_smul,X,add_neg_cancel]
  intro y hy
  exact (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero hd.differentiableOn
    (fun z hz' ↦ by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz']; exact hz z hz')
    hy (Metric.mem_ball_self hr)

theorem graph_umbilic_CMC_sphere {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r H : ℝ}
    (hr : 0<r) (hH : H≠0)
    (hcmc : ∀ y∈Metric.ball (0 : Plane) r,
      planeDivergence (fun z ↦ cmcFlux (gradient g z)) y=H)
    (he : ∀ y∈Metric.ball (0 : Plane) r,H^2=2*graphSquaredSecondFundamentalForm g y) :
    ∃ c : Cover,∀ y∈Metric.ball (0 : Plane) r,
      normalGraph n g y∈Metric.sphere c |2/H| := by
  refine ⟨normalGraph n g 0+(2/H) • graphSlopeNormal n (gradient g 0),?_⟩
  intro y hy
  rw [Metric.mem_sphere,dist_eq_norm,
    ← graph_umbilic_CMC_center hn hg hr hH hcmc he y hy]
  simp only [sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
    graphSlopeNormal_unit hn,mul_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_squared_distance_difference {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (c v : Cover) :
    ‖v-c‖^2-‖normalGraph n g (normalPlaneCoordinates n v)-c‖^2=
      (⟪n,v⟫-g (normalPlaneCoordinates n v))*
        (⟪n,v⟫+g (normalPlaneCoordinates n v)-2*⟪n,c⟫) := by
  let w := normalPlaneEmbedding n (normalPlaneCoordinates n v)
  have hw : ⟪n,w⟫=0 := normalPlaneEmbedding_inner hn _
  have hv : v=w+⟪n,v⟫ • n := (normalPlaneCoordinates_reconstruct hn v).symm
  have hg : normalGraph n g (normalPlaneCoordinates n v)=w+g (normalPlaneCoordinates n v) • n := rfl
  rw [hg]
  conv_lhs => lhs; rw [hv]
  simp only [norm_sub_sq_real,norm_add_sq_real,real_inner_smul_left,
    real_inner_smul_right,inner_add_left,norm_smul,Real.norm_eq_abs,
    sq_abs,hn,mul_one]
  rw [← real_inner_comm w n,hw]
  ring

end CubicTorus
end
end
end

end OAI
