import Mathlib
import OAI.Geometry.CubicTorus.Profiles.TransverseTorus

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace LatticeIsometry

lemma volumeSupport_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    volumeSupport (e.torus ⁻¹' E)=e.torus ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (e.torus ⁻¹' E)∩Metric.ball a r=e.torus ⁻¹' (E∩Metric.ball (e.torus a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,e.torus.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,e.measurePreserving.measure_preimage
    (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    openRepresentative (e.torus ⁻¹' E)=e.torus ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [←preimage_compl,e.volumeSupport_preimage hE.compl]
  rfl

lemma frontier_openRepresentative_preimage (e : LatticeIsometry) {E : Set Torus}
    (hE : MeasurableSet E) :
    frontier (openRepresentative (e.torus ⁻¹' E))=e.torus ⁻¹' frontier (openRepresentative E) := by
  rw [e.openRepresentative_preimage hE]
  exact (e.torus.toHomeomorph.preimage_frontier _).symm

def normalMap (e : LatticeIsometry) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (e.torus (quotientMap z.1)),
    ⟨e.cover (z.2 : Cover),by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

lemma measurable_normalMap (e : LatticeIsometry) : Measurable e.normalMap := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp (e.torus.continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact (e.cover.continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma normalMap_periodic_eval (e : LatticeIsometry) {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (z : NormalBundle) :
    F (e.normalMap z).1=F (e.cover z.1) := by
  change F (representative (e.torus (quotientMap z.1)))=_
  rw [←e.commute,periodic_representative hp]

lemma isNormalMeasure_preimage (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure (e.torus ⁻¹' E) (μ.map e.symm.normalMap) := by
  constructor
  · have hm : ((μ.map e.symm.normalMap).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply e.symm.measurable_normalMap
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,e.perimeter_eq hE.nullMeasurableSet]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map e.symm.normalMap (μ : Measure NormalBundle))=_
    rw [integral_map e.symm.measurable_normalMap.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      e.flux hF hE,←hμ.2 _ (e.symm.pullback_admissible hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪e.cover.symm (z.2 : Cover),F (e.symm.normalMap z).1⟫=
        ⟪(z.2 : Cover),e.cover (F (e.cover.symm z.1))⟫
      rw [e.symm.normalMap_periodic_eval hF.2.1]
      exact (e.cover.inner_map_map (e.cover.symm (z.2 : Cover)) (F (e.cover.symm z.1))).symm.trans
        (by rw [e.cover.apply_symm_apply])

lemma pullback_normal_ae (e : LatticeIsometry) {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map e.symm.normalMap) : Measure NormalBundle),e.pullback N z.1=(z.2 : Cover) := by
  rw [FiniteMeasure.toMeasure_map]
  have hc : Continuous (fun z : NormalBundle ↦ e.pullback N z.1) :=
    (e.pullback_contDiff hN).continuous.comp normalEmbedding_continuous.fst
  apply (ae_map_iff e.symm.measurable_normalMap.aemeasurable
    (isClosed_eq hc continuous_normalUnit).measurableSet).mpr
  filter_upwards [hae] with z hz
  change e.pullback N (e.symm.normalMap z).1=e.cover.symm (z.2 : Cover)
  rw [e.symm.normalMap_periodic_eval (e.pullback_periodic hp)]
  change e.cover.symm (N (e.cover (e.cover.symm z.1)))=_
  rw [e.cover.apply_symm_apply,hz]

theorem normal_equivariant (e : LatticeIsometry) {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (he : E=ᵐ[torusVolume](e.torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N (e.cover x)=e.cover (N x) := by
  have hμ' := (e.isNormalMeasure_preimage hE hμ).congr_ae he.symm
  obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin x hx
  have hh := (hw μ hμ N hN hp hae).trans
    (hw _ hμ' _ (e.pullback_contDiff hN) (e.pullback_periodic hp) (e.pullback_normal_ae hN hp hae)).symm
  change N x=e.cover.symm (N (e.cover x)) at hh
  have hh' := congrArg e.cover hh
  simpa only [e.cover.apply_symm_apply] using hh'.symm

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisReflection (i : Fin 3) : LatticeIsometry where
  cover := ((sibling_coverCoordinatePermute (Equiv.swap 0 i)).trans firstReflection).trans
    (sibling_coverCoordinatePermute (Equiv.swap 0 i))
  torus := ((torusCoordinatePermute (Equiv.swap 0 i)).trans torusFirstReflection).trans
    (torusCoordinatePermute (Equiv.swap 0 i))
  commute x := by
    change quotientMap (sibling_coverCoordinatePermute (Equiv.swap 0 i)
      (firstReflection (sibling_coverCoordinatePermute (Equiv.swap 0 i) x)))=_
    rw [coverCoordinatePermute_quotient,firstReflection_quotient,coverCoordinatePermute_quotient]
    rfl

lemma axisReflection_cover_apply (i j : Fin 3) (x : Cover) :
    (axisReflection i).cover x j=if j=i then -x j else x j := by
  classical
  change (sibling_coverCoordinatePermute (Equiv.swap 0 i)
    (firstReflection (sibling_coverCoordinatePermute (Equiv.swap 0 i) x))) j=_
  simp only [sibling_coverCoordinatePermute_apply,firstReflection_apply,Equiv.swap_apply_self]
  by_cases h : j=i
  · subst j
    simp
  · have : Equiv.swap (0 : Fin 3) i j≠0 := by
      intro he
      have := congrArg (Equiv.swap (0 : Fin 3) i) he
      exact h (by simpa using this)
    simp [h,this]

lemma axisReflection_torus_apply (i j : Fin 3) (x : Torus) :
    (axisReflection i).torus x j=if j=i then -x j else x j := by
  classical
  change (torusCoordinatePermute (Equiv.swap 0 i)
    (torusFirstReflection (torusCoordinatePermute (Equiv.swap 0 i) x))) j=_
  simp only [sibling_torusCoordinatePermute_apply,torusFirstReflection_apply,Equiv.swap_apply_self]
  by_cases h : j=i
  · subst j
    simp
  · have : Equiv.swap (0 : Fin 3) i j≠0 := by
      intro he
      have := congrArg (Equiv.swap (0 : Fin 3) i) he
      exact h (by simpa using this)
    simp [h,this]

lemma axisReflection_conjugate (i : Fin 3) (x : Torus) :
    (axisReflection i).torus (torusCoordinatePermute (Equiv.swap 0 i) x)=
      torusCoordinatePermute (Equiv.swap 0 i) (torusFirstReflection x) := by
  ext j
  simp only [axisReflection_torus_apply,sibling_torusCoordinatePermute_apply,torusFirstReflection_apply]
  have he : (j=i) ↔ Equiv.swap (0 : Fin 3) i j=0 := by
    constructor
    · rintro rfl; simp
    · intro h
      have hh := congrArg (Equiv.swap (0 : Fin 3) i) h
      simpa using hh
  simp only [he]

def centeredAxisReflection (i : Fin 3) (a : Torus) : Torus ≃ᵢ Torus :=
  ((IsometryEquiv.addRight (-a)).trans (axisReflection i).torus).trans
    (IsometryEquiv.addRight a)

lemma centeredAxisReflection_apply (i j : Fin 3) (a x : Torus) :
    centeredAxisReflection i a x j=if j=i then -x j+(a j+a j) else x j := by
  change ((axisReflection i).torus (x+ -a)+a) j=_
  rw [PiLp.add_apply,axisReflection_torus_apply]
  simp only [PiLp.add_apply,PiLp.neg_apply]
  split_ifs <;> abel

lemma centeredAxisReflection_eq (i : Fin 3) {a b : Torus} (h : a i=b i) :
    centeredAxisReflection i a=centeredAxisReflection i b := by
  ext x j
  simp only [centeredAxisReflection_apply]
  split_ifs with hj
  · subst j; rw [h]
  · rfl

lemma translated_axis_symmetry_iff (i : Fin 3) (a : Torus) (E : Set Torus) :
    ((fun z : Torus ↦ z+a) ⁻¹' E)=ᵐ[torusVolume]
      ((axisReflection i).torus ⁻¹' ((fun z : Torus ↦ z+a) ⁻¹' E)) ↔
    E=ᵐ[torusVolume](centeredAxisReflection i a ⁻¹' E) := by
  constructor
  · intro h
    have hh := (measurePreserving_add_right torusVolume (-a)).quasiMeasurePreserving.preimage_ae_eq h
    filter_upwards [hh] with x hx
    change (x∈E)=((axisReflection i).torus (x+ -a)+a∈E)
    change ((x+ -a)+a∈E)=((axisReflection i).torus (x+ -a)+a∈E) at hx
    simpa only [neg_add_cancel_right] using hx
  · intro h
    have hh := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq h
    filter_upwards [hh] with x hx
    change (x+a∈E)=((axisReflection i).torus x+a∈E)
    change (x+a∈E)=((axisReflection i).torus ((x+a)+ -a)+a∈E) at hx
    simpa only [add_neg_cancel_right] using hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_zero_torus : (axisReflection 0).torus=torusFirstReflection := by
  ext x j
  simp only [axisReflection_torus_apply,torusFirstReflection_apply]

lemma torusCoordinateSwap_involutive (i : Fin 3) :
    Function.Involutive (torusCoordinatePermute (Equiv.swap 0 i)) := by
  intro x
  ext j
  simp only [sibling_torusCoordinatePermute_apply,Equiv.swap_apply_self]

lemma centeredAxisReflection_conjugate (i : Fin 3) (a x : Torus) :
    centeredAxisReflection i (torusCoordinatePermute (Equiv.swap 0 i) a)
      (torusCoordinatePermute (Equiv.swap 0 i) x)=
    torusCoordinatePermute (Equiv.swap 0 i) (centeredAxisReflection 0 a x) := by
  ext j
  simp only [centeredAxisReflection_apply,sibling_torusCoordinatePermute_apply]
  have he : (j=i) ↔ Equiv.swap (0 : Fin 3) i j=0 := by
    constructor
    · rintro rfl; simp
    · intro h
      have hh := congrArg (Equiv.swap (0 : Fin 3) i) h
      simpa using hh
  simp only [he]

theorem isMinimizerAt_exists_axis_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3) :
    ∃ a : Torus,E=ᵐ[torusVolume](centeredAxisReflection i a ⁻¹' E) := by
  let P := torusCoordinatePermute (Equiv.swap 0 i)
  let F := P ⁻¹' E
  have hmF : IsMinimizerAt V F := isMinimizerAt_coordinatePermutation hmin _
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    change IsPreconnected (frontier (openRepresentative ((coordinatePermutation (Equiv.swap 0 i)).torus ⁻¹' E)))
    rw [(coordinatePermutation (Equiv.swap 0 i)).frontier_openRepresentative_preimage hE]
    exact P.toHomeomorph.isPreconnected_preimage.mpr hc
  obtain ⟨a,ha⟩ := isMinimizerAt_exists_first_reflection hV hmF hcF
  have ha' : F=ᵐ[torusVolume](centeredAxisReflection 0 a ⁻¹' F) := by
    apply (translated_axis_symmetry_iff 0 a F).mp
    rw [axisReflection_zero_torus]
    exact ha
  have hh := (coordinatePermutation (Equiv.swap 0 i)).measurePreserving.quasiMeasurePreserving.preimage_ae_eq ha'
  refine ⟨P a,?_⟩
  filter_upwards [hh] with x hx
  change (P (P x)∈E)=(P (centeredAxisReflection 0 a (P x))∈E) at hx
  have hleft : P (P x)=x := torusCoordinateSwap_involutive i x
  have hright : P (centeredAxisReflection 0 a (P x))=centeredAxisReflection i (P a) x := by
    rw [←centeredAxisReflection_conjugate i a (P x),hleft]
  change (x∈E)=(centeredAxisReflection i (P a) x∈E)
  rwa [hleft,hright] at hx

theorem isMinimizerAt_common_reflection_origin {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ a : Torus,∀ i : Fin 3,let E' := (fun z : Torus ↦ z+a) ⁻¹' E
      E'=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E') := by
  classical
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hae : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hae).mpr hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rwa [openRepresentative_congr_ae hae]
  choose b hb using isMinimizerAt_exists_axis_reflection hV hF hmF hcF
  let a : Torus := WithLp.toLp 2 (fun i ↦ b i i)
  refine ⟨a,fun i ↦ ?_⟩
  have hf : F=ᵐ[torusVolume](centeredAxisReflection i a ⁻¹' F) := by
    rw [centeredAxisReflection_eq i (a := a) (b := b i) rfl]
    exact hb i
  have hf' := (translated_axis_symmetry_iff i a F).mpr hf
  have htAE := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq hae
  refine htAE.symm.trans (hf'.trans ?_)
  exact (axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq htAE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma representative_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Torus) :
    representative (torusCoordinatePermute e x)=sibling_coverCoordinatePermute e (representative x) := by
  ext j
  rfl

lemma LatticeIsometry.pullback_representative (e : LatticeIsometry) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (x : Torus) :
    e.pullback N (representative x)=e.cover.symm (N (representative (e.torus x))) := by
  have he := periodic_representative hp (e.cover (representative x))
  rw [e.commute,quotientMap_representative] at he
  change e.cover.symm (N (e.cover (representative x)))=_
  rw [he]

lemma coordinateSwap_pullback_scalar (i : Fin 3) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (x : Torus) :
    (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0=N (representative x) i := by
  rw [LatticeIsometry.pullback_representative _ hp]
  change (sibling_coverCoordinatePermute (Equiv.swap 0 i)).symm
    (N (representative (torusCoordinatePermute (Equiv.swap 0 i)
      (torusCoordinatePermute (Equiv.swap 0 i) x)))) 0=_
  rw [torusCoordinateSwap_involutive,coverCoordinatePermute_symm]
  simp only [sibling_coverCoordinatePermute_apply,Equiv.symm_swap,Equiv.swap_apply_left]

theorem isMinimizerAt_axis_strict_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),N (representative x) i=0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      N (representative x) i<0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      0<N (representative x) i) := by
  let e := coordinatePermutation (Equiv.swap 0 i)
  let F := e.torus ⁻¹' E
  have hF : MeasurableSet F := hE.preimage e.torus.continuous.measurable
  have hmF : IsMinimizerAt V F := e.isMinimizerAt hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    change IsPreconnected (frontier (openRepresentative (e.torus ⁻¹' E)))
    rw [e.frontier_openRepresentative_preimage hE]
    exact e.torus.toHomeomorph.isPreconnected_preimage.mpr hc
  have hRF : F=ᵐ[torusVolume](torusFirstReflection ⁻¹' F) := by
    have hh := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq hR
    filter_upwards [hh] with x hx
    change (e.torus x∈E)=((axisReflection i).torus (e.torus x)∈E) at hx
    change (e.torus x∈E)=(e.torus (torusFirstReflection x)∈E)
    change (torusCoordinatePermute (Equiv.swap 0 i) x∈E)=
      ((axisReflection i).torus (torusCoordinatePermute (Equiv.swap 0 i) x)∈E) at hx
    rwa [axisReflection_conjugate] at hx
  have hpoint (x : Torus) (hx : x∈frontier (openRepresentative E)) :
      e.torus x∈frontier (openRepresentative F) := by
    change e.torus x∈frontier (openRepresentative (e.torus ⁻¹' E))
    rw [e.frontier_openRepresentative_preimage hE]
    change e.torus (e.torus x)∈frontier (openRepresentative E)
    change torusCoordinatePermute (Equiv.swap 0 i)
      (torusCoordinatePermute (Equiv.swap 0 i) x)∈frontier (openRepresentative E)
    rwa [torusCoordinateSwap_involutive]
  have hseam (x : Torus) : firstSeamFunction (representative (e.torus x))=
      Real.sin (2*Real.pi*representative x i) := by
    change Real.sin (2*Real.pi*representative (torusCoordinatePermute (Equiv.swap 0 i) x) 0)=_
    rw [representative_coordinatePermute,sibling_coverCoordinatePermute_apply,Equiv.swap_apply_left]
  rcases isMinimizerAt_reflection_strict_normal_sign hV hF hmF hcF hRF
    (e.isNormalMeasure_preimage hE hμ) (e.pullback_contDiff hN) (e.pullback_periodic hp)
    (e.pullback_normal_ae hN hp hae) with hz|hn|hpos
  · left
    intro x hx
    have hh := hz (e.torus x) (hpoint x hx)
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0=0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; left
    intro x hx hs
    have hh := hn (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0<0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; right
    intro x hx hs
    have hh := hpos (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change 0<(coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_zero_axis_standard {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (i : Fin 3)
    (hz : ∀ x∈frontier (openRepresentative E),N (representative x) i=0) :
    4*Real.pi/81≤V ∧ V≤1/Real.pi ∧ CongruentAE E (canonicalTube V) := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have hbd : frontier (openRepresentative F)=frontier (openRepresentative E) :=
    congrArg frontier (openRepresentative_congr_ae hFE)
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [hbd]
  have hμF : IsNormalMeasure F μ := hμ.congr_ae hFE.symm
  have hbF : ∀ x : Cover,quotientMap x∈frontier (openRepresentative F) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := by rwa [hbd]
  have hzF (x : Cover) (hx : quotientMap x∈frontier (openRepresentative F)) : N x i=0 := by
    have hh := hz _ (show quotientMap x∈frontier (openRepresentative E) by rwa [hbd] at hx)
    rwa [periodic_representative hp x] at hh
  obtain ⟨hr0,hr,c,hc,hcyl⟩ := isMinimizerAt_zero_axis_cylindrical_boundary
    ⟨hV.1,by linarith [hV.2]⟩ hF hmF hcF hμF hN hp hae hbF i hzF
  obtain ⟨hlo,hhi,φ,hφ⟩ := isMinimizerAt_coordinate_cylinder_standard hV hF hmF i hc hr0 hr hcyl
  exact ⟨hlo,hhi,φ,hFE.symm.trans hφ⟩

theorem isMinimizerAt_nonstandard_axis_strict_normal_sign {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hstd : ¬StandardRegionAt V E) (i : Fin 3)
    (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) :
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      N (representative x) i<0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      0<N (representative x) i) := by
  rcases isMinimizerAt_axis_strict_normal_sign ⟨hV.1,by linarith [hV.2]⟩ hE hmin hc i hR hμ hN hp hae with hz|hn|hp'
  · exfalso
    obtain ⟨hlo,hhi,hcong⟩ := isMinimizerAt_zero_axis_standard hV hmin hc hμ hN hp hae hb i hz
    apply hstd
    unfold StandardRegionAt SmallStandardRegion
    rw [ite_eq_left hV.2]
    exact Or.inr (Or.inl ⟨hlo,hhi,hcong⟩)
  · exact Or.inl hn
  · exact Or.inr hp'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_signed_translation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) (a : Cover)
    (hsign : ∀ t∈Icc (0 : ℝ) 1,∀ᵐ z ∂(μ : Measure NormalBundle),
      0≤f ((z.1 : Cover)+t • a)*⟪(z.2 : Cover),a⟫) :
    0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x+a)-f x := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ ↦ f (x+s • a))
      (fderiv ℝ f (x+t • a) a) t := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,one_smul,zero_add] using
      (hd (x+t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1,fderiv ℝ f (x+t • a) a)=f (x+a)-f x := by
    rw [←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
    have hc : Continuous (fun t : ℝ ↦ fderiv ℝ f (x+t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M,_,hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover×ℝ ↦ fderiv ℝ f (z.1+z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover×ℝ ↦ fderiv ℝ f (z.1+z.2 • a) a)
      ((volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M*‖a‖)
    exact Eventually.of_forall fun z ↦ ((fderiv ℝ f (z.1+z.2 • a)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have hflux (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,fderiv ℝ f (x+t • a) a := by
    let g := fun x : Cover ↦ f (x+t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ m x,g (x+latticeVector m)=g x := by
      intro m x; dsimp [g]; rw [add_right_comm,hp]
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ g x • a) := hg.smul contDiff_const
    have hFp : ∀ m x,g (x+latticeVector m) • a=g x • a := by simp only [hgp]; simp
    obtain ⟨K,hK,hbd⟩ := periodic_bounded hF.continuous hFp
    have he := normalMeasure_flux hμ hF hFp (show 0<K+1 by linarith)
      (fun x ↦ (hbd x).trans (by linarith))
    simp only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right] at he
    rw [show (fun x ↦ fderiv ℝ f (x+t • a) a)=divergence (fun x ↦ g x • a) from by
      funext x
      rw [divergence_smul_const (hg.differentiable (by simp)).differentiableAt]
      dsimp [g]
      rw [fderiv_comp_add_right]]
    rw [←he]
    exact integral_nonneg_of_ae (hsign t ht)
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1,∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        fderiv ℝ f (x+t • a) a := by
      rw [←integral_integral_swap hi]
      simp_rw [hFTC]
    _ ≥ 0 := integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hflux t ⟨ht.1.le,ht.2⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_descent_translate {f : Cover → ℝ}
    (hp : ∀ m x,f (x+latticeVector m)=f x) (a : Cover) (x : Torus) :
    f (representative x+a)=f (representative (x+quotientMap a)) := by
  have hh := periodic_representative hp (representative x+a)
  rw [quotientMap_add,quotientMap_representative] at hh
  exact hh.symm

theorem isMinimizerAt_test_phase_propagation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) (hf0 : ∀ x,0≤f x)
    (hsupport : ∀ x,f x≠0 → quotientMap x∈openRepresentative E)
    (a : Cover)
    (hsign : ∀ t∈Icc (0 : ℝ) 1,∀ᵐ z ∂(μ : Measure NormalBundle),
      0≤f ((z.1 : Cover)+t • a)*⟪(z.2 : Cover),a⟫)
    (x : Cover) (hx : 0<f (x+a)) : quotientMap x∈openRepresentative E := by
  let g : Torus → ℝ := fun z ↦ f (representative z)
  let k : Torus → ℝ := fun z ↦ f (representative z+a)
  have hfp : ∀ m x,f (x+latticeVector m+a)=f (x+a) := by
    intro m x; rw [add_right_comm,hp]
  have hg : Continuous g := continuous_periodic_descent hf.continuous hp
  have hk : Continuous k := continuous_periodic_descent
    (hf.continuous.comp (continuous_id.add continuous_const)) hfp
  obtain ⟨M,hM,hbd⟩ := periodic_bounded hf.continuous hp
  have hi : Integrable g torusVolume := Integrable.of_bound hg.aestronglyMeasurable M
    (Eventually.of_forall fun z ↦ hbd _)
  have hki : Integrable k torusVolume := Integrable.of_bound hk.aestronglyMeasurable M
    (Eventually.of_forall fun z ↦ hbd _)
  have hgae : g=ᵐ[torusVolume.restrict Eᶜ]0 := by
    filter_upwards [ae_restrict_of_ae (isMinimizerAt_openRepresentative_ae hV hE hmin),
      ae_restrict_mem hE.compl] with z hz hzE
    change g z=0
    by_contra hne
    have hO := hsupport (representative z) hne
    rw [quotientMap_representative] at hO
    exact hzE (hz.mp hO)
  have hgz : (∫ z in Eᶜ,g z ∂torusVolume)=0 := integral_eq_zero_of_ae hgae
  have htotal : (∫ z,k z ∂torusVolume)=∫ z,g z ∂torusVolume := by
    change (∫ z,f (representative z+a) ∂torusVolume)=_
    simp_rw [periodic_descent_translate hp]
    exact integral_add_right_eq_self g (quotientMap a)
  have hdf : Continuous (fun x ↦ f (x+a)-f x) :=
    (hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous
  have hdp : ∀ m x,f (x+latticeVector m+a)-f (x+latticeVector m)=f (x+a)-f x := by
    intro m x; rw [hfp,hp]
  have hm := normalMeasure_signed_translation hμ hf hp a hsign
  rw [←setIntegral_lift hdf hdp hE] at hm
  change 0≤∫ z in E,k z-g z ∂torusVolume at hm
  rw [integral_sub hki.integrableOn hi.integrableOn] at hm
  have hz : (∫ z in Eᶜ,k z ∂torusVolume)=0 := by
    have hk0 : 0≤∫ z in Eᶜ,k z ∂torusVolume := integral_nonneg fun z ↦ hf0 _
    have ha := integral_add_compl hE hi
    have hb := integral_add_compl hE hki
    rw [hgz] at ha
    rw [htotal] at hb
    linarith
  have hkae : k=ᵐ[torusVolume.restrict Eᶜ]0 :=
    (integral_eq_zero_iff_of_nonneg (fun z ↦ hf0 _) hki.integrableOn).mp hz
  have hs : (torusVolume.restrict Eᶜ).support⊆{z | k z=0} :=
    Measure.support_subset_of_isClosed (isClosed_eq hk continuous_const) hkae
  change quotientMap x∉(torusVolume.restrict Eᶜ).support
  intro hmem
  have he := hs hmem
  change f (representative (quotientMap x)+a)=0 at he
  have heq := periodic_representative (f := fun w ↦ f (w+a)) hfp x
  rw [heq] at he
  exact hx.ne' he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma latticePeriodize_ne_zero {f : Cover → ℝ} {x : Cover}
    (h : latticePeriodize f x≠0) : ∃ m : Fin 3 → ℤ,f (x+latticeVector m)≠0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [latticePeriodize,hn,tsum_zero])

theorem isMinimizerAt_convex_phase_monotone {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {U : Set Cover} (hU : IsOpen U) (hc : Convex ℝ U)
    (hcell : U⊆{x | ∀ i,0<x i ∧ x i<1})
    {x y : Cover} (hx : x∈U) (hy : y∈U)
    (hyO : quotientMap y∈openRepresentative E)
    (hsign : ∀ z∈U,quotientMap z∈frontier (openRepresentative E) →
      0≤⟪N z,y-x⟫) : quotientMap x∈openRepresentative E := by
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU x hx
  have hO : IsOpen (U∩quotientMap ⁻¹' openRepresentative E) :=
    hU.inter ((isOpen_openRepresentative E).preimage continuous_quotientMap)
  obtain ⟨s,hs,hsU⟩ := Metric.isOpen_iff.mp hO y ⟨hy,hyO⟩
  let ρ : ℝ := min r s/4
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρr : 2*ρ<r := by
    have hh := min_le_left r s
    have hp := lt_min hr hs
    dsimp [ρ]; linarith
  have hρs : 2*ρ<s := by
    have hh := min_le_right r s
    have hp := lt_min hr hs
    dsimp [ρ]; linarith
  let φ := radialHeightCutoff y ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hφc : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφb (z : Cover) : 0≤φ z := radialDensityWeight_nonneg _ _ _ _
  have hφs : tsupport φ⊆Metric.closedBall y (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU : tsupport φ⊆U := fun z hz ↦ (hsU (by
    exact (Metric.mem_closedBall.mp (hφs hz)).trans_lt hρs)).1
  have hφO : tsupport φ⊆quotientMap ⁻¹' openRepresentative E := fun z hz ↦
    (hsU (by exact (Metric.mem_closedBall.mp (hφs hz)).trans_lt hρs)).2
  let f := latticePeriodize φ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := latticePeriodize_contDiff hφ hφc
  have hfp : ∀ m z,f (z+latticeVector m)=f z := latticePeriodize_periodic φ
  have hf0 : ∀ z,0≤f z := fun z ↦ tsum_nonneg (fun m ↦ hφb _)
  have hfs (z : Cover) (hz : f z≠0) : quotientMap z∈openRepresentative E := by
    obtain ⟨m,hm⟩ := latticePeriodize_ne_zero hz
    have hh := hφO (subset_tsupport φ hm)
    simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hh
  have hfy : f y=1 := by
    change latticePeriodize φ y=1
    rw [(latticePeriodize_eventuallyEq hφc (hφU.trans hcell)
      (fun i ↦ ⟨(hcell hy i).1.le,(hcell hy i).2.le⟩)).eq_of_nhds]
    exact radialHeightCutoff_one hρ (by simpa using hρ.le)
  have hseg (z : Cover) (hz : z∈tsupport φ) (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      z-t • (y-x)∈U := by
    have hzy : dist z y≤2*ρ := hφs hz
    have hzx : dist (z-(y-x)) x=dist z y := by
      simp only [dist_eq_norm]
      congr 1
      abel
    have hx' : z-(y-x)∈U := hrU (by rw [Metric.mem_ball,hzx]; exact hzy.trans_lt hρr)
    have hy' : z∈U := hφU hz
    have hh := hc hx' hy' ht.1 (sub_nonneg.mpr ht.2) (by ring : t+(1-t)=1)
    convert hh using 1
    module
  have hμO : IsNormalMeasure (openRepresentative E) μ :=
    hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hsg (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      ∀ᵐ z ∂(μ : Measure NormalBundle),
        0≤f ((z.1 : Cover)+t • (y-x))*⟪(z.2 : Cover),y-x⟫ := by
    filter_upwards [hae,normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO]
      with z hz hb
    by_cases he : f ((z.1 : Cover)+t • (y-x))=0
    · simp only [he,zero_mul,le_refl]
    obtain ⟨m,hm⟩ := latticePeriodize_ne_zero he
    have hu : (z.1 : Cover)+latticeVector m∈U := by
      have hh := hseg _ (subset_tsupport φ hm) t ht
      convert hh using 1
      module
    have hbound : quotientMap ((z.1 : Cover)+latticeVector m)∈frontier (openRepresentative E) := by
      simpa only [quotientMap_add,quotientMap_latticeVector,add_zero] using hb
    have hn := hsign _ hu hbound
    rw [hp,hz] at hn
    exact mul_nonneg (hf0 _) hn
  apply isMinimizerAt_test_phase_propagation hV hE hmin hμ hf hfp hf0 hfs (y-x) hsg x
  rw [add_sub_cancel,hfy]
  norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def upperOctant : Set Cover := {x | ∀ i : Fin 3,(1/2 : ℝ)<x i ∧ x i<1}

lemma isOpen_upperOctant : IsOpen upperOctant := by
  have he : upperOctant=⋂ i : Fin 3,(fun x : Cover ↦ x i) ⁻¹' Ioo (1/2 : ℝ) 1 := by
    ext x; simp [upperOctant]
  rw [he]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous

lemma convex_upperOctant : Convex ℝ upperOctant := by
  have he : upperOctant=⋂ i : Fin 3,(fun x : Cover ↦ x i) ⁻¹' Ioo (1/2 : ℝ) 1 := by
    ext x; simp [upperOctant]
  rw [he]
  exact convex_iInter fun i ↦ (convex_Ioo (1/2 : ℝ) 1).linear_preimage
    (EuclideanSpace.proj i).toLinearMap

def OrientedCoordinateLE (b : Fin 3 → Bool) (x y : Cover) : Prop :=
  ∀ i,if b i then x i≤y i else y i≤x i

lemma isMinimizerAt_octant_normal_orientation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ b : Fin 3 → Bool,∀ i : Fin 3,∀ x∈upperOctant,
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0≤N x i else N x i≤0 := by
  classical
  have hh (i : Fin 3) : ∃ b : Bool,∀ x∈upperOctant,
      quotientMap x∈frontier (openRepresentative E) →
      if b then 0≤N x i else N x i≤0 := by
    have hrep {x : Cover} (hx : x∈upperOctant) : representative (quotientMap x)=x :=
      representative_quotientMap_of_mem (fun j ↦ ⟨by linarith [(hx j).1],(hx j).2⟩)
    rcases isMinimizerAt_axis_strict_normal_sign hV hE hmin hc i (hR i) hμ hN hp hae with hz|hn|hp'
    · refine ⟨true,fun x hx hb ↦ ?_⟩
      simpa only [ite_true,hrep hx] using (hz _ hb).ge
    · refine ⟨false,fun x hx hb ↦ ?_⟩
      have hs : Real.sin (2*Real.pi*representative (quotientMap x) i)<0 := by
        rw [hrep hx]
        exact (firstSeam_sign ⟨by linarith [(hx i).1],(hx i).2⟩).mpr (hx i).1
      simpa only [Bool.false_eq_true,ite_false,hrep hx] using (hn _ hb hs).le
    · refine ⟨true,fun x hx hb ↦ ?_⟩
      have hs : Real.sin (2*Real.pi*representative (quotientMap x) i)<0 := by
        rw [hrep hx]
        exact (firstSeam_sign ⟨by linarith [(hx i).1],(hx i).2⟩).mpr (hx i).1
      simpa only [ite_true,hrep hx] using (hp' _ hb hs).le
  choose b hb using hh
  exact ⟨b,hb⟩

theorem isMinimizerAt_octant_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ b : Fin 3 → Bool,∀ x∈upperOctant,∀ y∈upperOctant,
      OrientedCoordinateLE b x y → quotientMap y∈openRepresentative E →
      quotientMap x∈openRepresentative E := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rwa [openRepresentative_congr_ae hFE]
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hFE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  obtain ⟨μ,H,N,hN,hp,hμ,haN,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hF hmF
  obtain ⟨b,hb⟩ := isMinimizerAt_octant_normal_orientation hV hF hmF hcF hRF hμ hN hp haN
  refine ⟨b,fun x hx y hy hxy hyE ↦ ?_⟩
  rw [←openRepresentative_congr_ae hFE] at hyE ⊢
  apply isMinimizerAt_convex_phase_monotone hV hF hmF hμ hp haN
    isOpen_upperOctant convex_upperOctant (fun z hz i ↦ ⟨by linarith [(hz i).1],(hz i).2⟩)
    hx hy hyE
  intro z hz hbound
  simp only [PiLp.inner_apply,PiLp.sub_apply,RCLike.inner_apply,RCLike.conj_to_real]
  apply Finset.sum_nonneg
  intro i hi
  have hn := hb i z hz hbound
  have hh := hxy i
  cases hbi : b i <;> simp only [hbi,Bool.false_eq_true,ite_false,ite_true] at hn hh
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hh) hn
  · exact mul_nonneg (sub_nonneg.mpr hh) hn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_axis_fixed_normal_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hfix : (axisReflection i).torus (quotientMap x)=quotientMap x) : N x i=0 := by
  have he := (axisReflection i).normal_equivariant hV hE hmin hR hμ hN hp hae x hx
  have hq : quotientMap ((axisReflection i).cover x)=quotientMap x := by
    rw [(axisReflection i).commute,hfix]
  obtain ⟨m,hm⟩ := same_quotient_lattice hq
  rw [hm,hp] at he
  have hh := congrArg (fun v : Cover ↦ v i) he
  simp only [axisReflection_cover_apply,ite_true] at hh
  linarith

end CubicTorus
end
end
end

end OAI
