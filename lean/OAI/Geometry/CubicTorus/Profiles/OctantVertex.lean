import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NormalMap

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_common_fixed_not_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (x : Torus) (hfix : ∀ i : Fin 3,(axisReflection i).torus x=x) :
    x∉frontier (openRepresentative E) := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hae : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hae).mpr hmin
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hae.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hae.symm))
  intro hx
  have hxF : quotientMap (representative x)∈frontier (openRepresentative F) := by
    rw [quotientMap_representative,openRepresentative_congr_ae hae]
    exact hx
  obtain ⟨μ,H,N,hN,hp,hμ,haN,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hF hmF
  have hz : N (representative x)=0 := by
    ext i
    exact isMinimizerAt_axis_fixed_normal_zero hV hF hmF i (hRF i) hμ hN hp haN
      (representative x) hxF (by rw [quotientMap_representative]; exact hfix i)
  have hunit : ‖N (representative x)‖=1 := (hb _ hxF).1.self_of_nhds
  rw [hz,norm_zero] at hunit
  norm_num at hunit

def octantVertex (b : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i ↦ if b i then (1/2 : ℝ) else 0)

lemma octantVertex_fixed (b : Fin 3 → Bool) (i : Fin 3) :
    (axisReflection i).torus (quotientMap (octantVertex b))=quotientMap (octantVertex b) := by
  classical
  have he : (axisReflection i).cover (octantVertex b)=octantVertex b+
      latticeVector (Pi.single i (if b i then (-1 : ℤ) else 0)) := by
    ext j
    rw [axisReflection_cover_apply,PiLp.add_apply]
    by_cases h : j=i
    · subst j
      simp only [ite_true,octantVertex,latticeVector,WithLp.ofLp_toLp,Pi.single_eq_same]
      cases b i <;> norm_num
    · simp [h,latticeVector,Pi.single_apply]
  rw [←(axisReflection i).commute,he,quotientMap_add,quotientMap_latticeVector,add_zero]

theorem isMinimizerAt_reflection_origin_vertices {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ a : Torus,let F := (fun z : Torus ↦ z+a) ⁻¹' E
      (∀ i : Fin 3,F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F)) ∧
      ∀ b : Fin 3 → Bool,quotientMap (octantVertex b)∉frontier (openRepresentative F) := by
  obtain ⟨a,ha⟩ := isMinimizerAt_common_reflection_origin hV hmin hc
  refine ⟨a,ha,?_⟩
  intro b
  exact isMinimizerAt_common_fixed_not_boundary hV (isMinimizerAt_translation hmin a)
    ha _ (octantVertex_fixed b)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def closedUpperOctant : Set Cover := {x | ∀ i : Fin 3,(1/2 : ℝ)≤x i ∧ x i≤1}

def octantContract (t : ℝ) (x : Cover) : Cover :=
  (1-t) • x+t • WithLp.toLp 2 (fun _ : Fin 3 ↦ (3/4 : ℝ))

lemma octantContract_apply (t : ℝ) (x : Cover) (i : Fin 3) :
    octantContract t x i=(1-t)*x i+t*(3/4 : ℝ) := rfl

lemma octantContract_mem {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1)
    {x : Cover} (hx : x∈closedUpperOctant) : octantContract t x∈upperOctant := by
  intro i
  rw [octantContract_apply]
  have h1 := mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr (hx i).1)
  have h2 := mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith [ht.1]

lemma octantContract_mono {t : ℝ} (ht : t≤1) {b : Fin 3 → Bool} {x y : Cover}
    (hxy : OrientedCoordinateLE b x y) :
    OrientedCoordinateLE b (octantContract t x) (octantContract t y) := by
  intro i
  simp only [octantContract_apply]
  have hh := hxy i
  cases hbi : b i <;> simp only [hbi,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · linarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]
  · linarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]

lemma octantContract_tendsto (x : Cover) :
    Tendsto (fun t : ℝ ↦ quotientMap (octantContract t x)) (𝓝[>]0) (𝓝 (quotientMap x)) := by
  have hc : Continuous (fun t : ℝ ↦ quotientMap (octantContract t x)) := by
    exact continuous_quotientMap.comp
      (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const))
  have hh := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [octantContract] using hh

lemma octant_downset_closed_endpoint {O : Set Torus} (hO : IsOpen O)
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈O → quotientMap x∈O)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyo : quotientMap y∈O) :
    quotientMap x∈closure O := by
  have hyv : ∀ᶠ t in 𝓝[>](0 : ℝ),quotientMap (octantContract t y)∈O :=
    octantContract_tendsto y (hO.mem_nhds hyo)
  apply isClosed_closure.mem_of_tendsto (octantContract_tendsto x)
  filter_upwards [hyv,self_mem_nhdsWithin,(eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with t hty ht0 ht1
  exact subset_closure (hd _ (octantContract_mem ⟨ht0,ht1⟩ hx)
    _ (octantContract_mem ⟨ht0,ht1⟩ hy) (octantContract_mono ht1.le hxy) hty)

lemma octant_downset_nonboundary_endpoint {O : Set Torus} (hO : IsOpen O)
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈O → quotientMap x∈O)
    {x y : Cover} (hx : x∈closedUpperOctant) (hy : y∈closedUpperOctant)
    (hxy : OrientedCoordinateLE b x y) (hyo : quotientMap y∈O)
    (hxb : quotientMap x∉frontier O) : quotientMap x∈O := by
  have hh := octant_downset_closed_endpoint hO hd hx hy hxy hyo
  by_contra hn
  apply hxb
  rw [hO.frontier_eq]
  exact ⟨hh,hn⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LatticeIsometry.openRepresentative_preimage_null (e : LatticeIsometry)
    {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    openRepresentative (e.torus ⁻¹' E)=e.torus ⁻¹' openRepresentative E := by
  have he := hE.toMeasurable_ae_eq
  have hp := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [←openRepresentative_congr_ae hp,e.openRepresentative_preimage (measurableSet_toMeasurable _ _),
    openRepresentative_congr_ae he]

lemma reflection_invariant_openRepresentative {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈openRepresentative E ↔ z∈openRepresentative E := by
  intro i z
  have hh := openRepresentative_congr_ae (hR i)
  rw [(axisReflection i).openRepresentative_preimage_null hE] at hh
  exact (Set.ext_iff.mp hh z).symm

def octantFlipSet (s : Finset (Fin 3)) (x : Cover) : Cover :=
  WithLp.toLp 2 (fun i ↦ if i∈s then 1-x i else x i)

lemma octantFlipSet_empty (x : Cover) : octantFlipSet ∅ x=x := by
  ext i; simp [octantFlipSet]

lemma octantFlipSet_insert {s : Finset (Fin 3)} {i : Fin 3} (hi : i∉s) (x : Cover) :
    octantFlipSet (insert i s) x=(axisReflection i).cover (octantFlipSet s x)+
      latticeVector (Pi.single i (1 : ℤ)) := by
  ext j
  rw [PiLp.add_apply,axisReflection_cover_apply]
  by_cases hji : j=i
  · subst j
    simp [octantFlipSet,hi,latticeVector,Pi.single_eq_same]
    ring
  · simp [octantFlipSet,hji,latticeVector,Pi.single_apply]

lemma octantFlipSet_mem {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    (s : Finset (Fin 3)) (x : Cover) : quotientMap (octantFlipSet s x)∈O ↔ quotientMap x∈O := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [octantFlipSet_empty]
  | @insert i s hi ih =>
    rw [octantFlipSet_insert hi,quotientMap_add,quotientMap_latticeVector,add_zero,
      (axisReflection i).commute,hR,ih]

lemma reflection_invariant_fold {O : Set Torus}
    (hR : ∀ i : Fin 3,∀ z : Torus,(axisReflection i).torus z∈O ↔ z∈O)
    {z : Torus} (hz : z∈O) : ∃ x∈closedUpperOctant,quotientMap x∈O := by
  classical
  let y := representative z
  let s : Finset (Fin 3) := Finset.univ.filter (fun i ↦ y i≤1/2)
  refine ⟨octantFlipSet s y,?_,?_⟩
  · intro i
    have hy := representative_mem_fundamentalCube z i
    change 0≤y i ∧ y i<1 at hy
    change (1/2 : ℝ)≤(if i∈s then 1-y i else y i) ∧ (if i∈s then 1-y i else y i)≤1
    have hs : (i∈s) ↔ y i≤1/2 := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hi : y i≤1/2
    · rw [ite_eq_left (hs.mpr hi)]; constructor <;> linarith [hy.1]
    · rw [ite_eq_right (fun h ↦ hi (hs.mp h))]; constructor <;> linarith [hy.2]
  · apply (octantFlipSet_mem hR s y).mpr
    simpa only [y,quotientMap_representative] using hz

lemma sibling_isMinimizerAt_openRepresentative_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : (openRepresentative E).Nonempty := by
  let F := toMeasurable torusVolume E
  have hae : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hae).mpr hmin
  have hO : openRepresentative E=ᵐ[torusVolume]E := by
    rw [←openRepresentative_congr_ae hae]
    exact (isMinimizerAt_openRepresentative_ae hV (measurableSet_toMeasurable _ _) hmF).trans hae
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  have hm := measure_congr hO
  rw [he,measure_empty,hmin.2.1] at hm
  exact (ENNReal.ofReal_pos.mpr hV.1).ne' hm.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def upperVertex (c : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i ↦ if c i then (1 : ℝ) else 1/2)

def orientedUpperVertex (b c : Fin 3 → Bool) : Cover :=
  upperVertex (fun i ↦ if b i then c i else !c i)

lemma upperVertex_mem (c : Fin 3 → Bool) : upperVertex c∈closedUpperOctant := by
  intro i
  dsimp [upperVertex]
  cases c i <;> norm_num

lemma upperVertex_fixed (c : Fin 3 → Bool) (i : Fin 3) :
    (axisReflection i).torus (quotientMap (upperVertex c))=quotientMap (upperVertex c) := by
  have he : (axisReflection i).cover (upperVertex c)=upperVertex c+
      latticeVector (Pi.single i (if c i then (-2 : ℤ) else -1)) := by
    ext j
    rw [axisReflection_cover_apply,PiLp.add_apply]
    by_cases h : j=i
    · subst j
      simp only [ite_true,upperVertex,latticeVector,WithLp.ofLp_toLp,Pi.single_eq_same]
      cases c i <;> norm_num
    · simp [h,latticeVector,Pi.single_apply]
  rw [←(axisReflection i).commute,he,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma orientedUpperVertex_min (b : Fin 3 → Bool) {x : Cover} (hx : x∈closedUpperOctant) :
    OrientedCoordinateLE b (orientedUpperVertex b (fun _ ↦ false)) x := by
  intro i
  dsimp [orientedUpperVertex,upperVertex]
  by_cases hbi : b i=true
  · simpa [hbi] using (hx i).1
  · simpa [hbi] using (hx i).2

lemma orientedUpperVertex_max (b : Fin 3 → Bool) {x : Cover} (hx : x∈closedUpperOctant) :
    OrientedCoordinateLE b x (orientedUpperVertex b (fun _ ↦ true)) := by
  intro i
  dsimp [orientedUpperVertex,upperVertex]
  by_cases hbi : b i=true
  · simpa [hbi] using (hx i).2
  · simpa [hbi] using (hx i).1

lemma orientedUpperVertex_mono (b : Fin 3 → Bool) {c d : Fin 3 → Bool}
    (hcd : ∀ i,c i=true → d i=true) :
    OrientedCoordinateLE b (orientedUpperVertex b c) (orientedUpperVertex b d) := by
  intro i
  dsimp [orientedUpperVertex,upperVertex]
  have hh := hcd i
  by_cases hbi : b i=true <;> by_cases hci : c i=true <;> by_cases hdi : d i=true <;> simp_all <;> norm_num

lemma isMinimizerAt_closure_openRepresentative_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E)=volumeSupport E := by
  let F := toMeasurable torusVolume E
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  rw [←openRepresentative_congr_ae hFE,←volumeSupport_congr_ae hFE]
  exact isMinimizerAt_closure_openRepresentative hV (measurableSet_toMeasurable _ _)
    ((isMinimizerAt_congr_ae hFE).mpr hmin)

theorem isMinimizerAt_vertex_order_ideal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ b : Fin 3 → Bool,
      quotientMap (orientedUpperVertex b (fun _ ↦ false))∈openRepresentative E ∧
      quotientMap (orientedUpperVertex b (fun _ ↦ true))∉openRepresentative E ∧
      (∀ c : Fin 3 → Bool,quotientMap (orientedUpperVertex b c)∉frontier (openRepresentative E)) ∧
      ∀ c d : Fin 3 → Bool,(∀ i,c i=true → d i=true) →
        quotientMap (orientedUpperVertex b d)∈openRepresentative E →
        quotientMap (orientedUpperVertex b c)∈openRepresentative E := by
  obtain ⟨b,hb⟩ := isMinimizerAt_octant_downset hV hmin hc hR
  have hno (c : Fin 3 → Bool) : quotientMap (orientedUpperVertex b c)∉frontier (openRepresentative E) :=
    isMinimizerAt_common_fixed_not_boundary hV hmin hR _ (upperVertex_fixed _)
  have hminv : quotientMap (orientedUpperVertex b (fun _ ↦ false))∈openRepresentative E := by
    obtain ⟨z,hz⟩ := sibling_isMinimizerAt_openRepresentative_nonempty hV hmin
    obtain ⟨y,hy,hyO⟩ := reflection_invariant_fold (reflection_invariant_openRepresentative hmin.1.1 hR) hz
    exact octant_downset_nonboundary_endpoint (isOpen_openRepresentative E) hb (upperVertex_mem _)
      hy (orientedUpperVertex_min b hy) hyO (hno _)
  have hmaxv : quotientMap (orientedUpperVertex b (fun _ ↦ true))∉openRepresentative E := by
    intro hh
    have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
    have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
    have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
    obtain ⟨z,hz⟩ := sibling_isMinimizerAt_openRepresentative_nonempty hVc hmc
    obtain ⟨y,hy,hyO⟩ := reflection_invariant_fold (reflection_invariant_openRepresentative hmc.1.1 hRc) hz
    have hcO := octant_downset_closed_endpoint (isOpen_openRepresentative E) hb hy
      (upperVertex_mem _) (orientedUpperVertex_max b hy) hh
    rw [isMinimizerAt_closure_openRepresentative_null hV hmin] at hcO
    exact hyO (by simpa only [compl_compl] using hcO)
  refine ⟨b,hminv,hmaxv,hno,?_⟩
  intro c d hcd hd
  exact octant_downset_nonboundary_endpoint (isOpen_openRepresentative E) hb (upperVertex_mem _)
    (upperVertex_mem _) (orientedUpperVertex_mono b hcd) hd (hno c)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma representative_quotientMap_coordinate {x : Cover} {i : Fin 3} (hx : x i∈Ico (0 : ℝ) 1) :
    representative (quotientMap x) i=x i := by
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ)=x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx)]

theorem isMinimizerAt_nonstandard_strict_octant {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (b : Fin 3 → Bool),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
        quotientMap x∈frontier (openRepresentative E) →
        if b i then 0<N x i else N x i<0) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E → quotientMap x∈openRepresentative E) := by
  classical
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have hbd : frontier (openRepresentative F)=frontier (openRepresentative E) :=
    congrArg frontier (openRepresentative_congr_ae hFE)
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [hbd]
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hFE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  obtain ⟨μ,H,N,hN,hp,hμ,haN,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV' hF hmF
  have hb' (x : Cover) (hx : quotientMap x∈frontier (openRepresentative F)) :
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := ⟨(hb x hx).1,(hb x hx).2.1⟩
  have hbE : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := by rwa [hbd] at hb'
  have hμE := hμ.congr_ae hFE
  have hsg (i : Fin 3) : ∃ bi : Bool,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) → if bi then 0<N x i else N x i<0 := by
    rcases isMinimizerAt_axis_strict_normal_sign hV' hF hmF hcF i (hRF i) hμ hN hp haN with hz|hn|hp'
    · exfalso
      have hzE : ∀ x∈frontier (openRepresentative E),N (representative x) i=0 := by rwa [hbd] at hz
      obtain ⟨hlo,hhi,hcong⟩ := isMinimizerAt_zero_axis_standard hV hmin hc hμE hN hp haN hbE i hzE
      apply hstd
      unfold StandardRegionAt SmallStandardRegion
      rw [ite_eq_left hV.2]
      exact Or.inr (Or.inl ⟨hlo,hhi,hcong⟩)
    · refine ⟨false,fun x hx hxb ↦ ?_⟩
      have hh := hn (quotientMap x) (by rwa [hbd]) (by
        rw [representative_quotientMap_coordinate ⟨by linarith [hx.1],hx.2⟩]
        exact (firstSeam_sign ⟨by linarith [hx.1],hx.2⟩).mpr hx.1)
      simpa only [Bool.false_eq_true,ite_false,periodic_representative hp x] using hh
    · refine ⟨true,fun x hx hxb ↦ ?_⟩
      have hh := hp' (quotientMap x) (by rwa [hbd]) (by
        rw [representative_quotientMap_coordinate ⟨by linarith [hx.1],hx.2⟩]
        exact (firstSeam_sign ⟨by linarith [hx.1],hx.2⟩).mpr hx.1)
      simpa only [ite_true,periodic_representative hp x] using hh
  choose b hbsg using hsg
  refine ⟨μ,H,N,b,hμE,hN,hp,haN,hbE,hbsg,?_⟩
  intro x hx y hy hxy hyE
  rw [←openRepresentative_congr_ae hFE] at hyE ⊢
  apply isMinimizerAt_convex_phase_monotone hV' hF hmF hμ hp haN
    isOpen_upperOctant convex_upperOctant (fun z hz i ↦ ⟨by linarith [(hz i).1],(hz i).2⟩) hx hy hyE
  intro z hz hbound
  simp only [PiLp.inner_apply,PiLp.sub_apply,RCLike.inner_apply,RCLike.conj_to_real]
  apply Finset.sum_nonneg
  intro i hi
  have hn := hbsg i z (hz i) (by rwa [hbd] at hbound)
  have hh := hxy i
  cases hbi : b i <;> simp only [hbi,Bool.false_eq_true,ite_false,ite_true] at hn hh
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hh) hn.le
  · exact mul_nonneg (sub_nonneg.mpr hh) hn.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_periodic_centered_primitive {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.Periodic ψ 1 ∧
      ∀ t,deriv ψ t=f t-∫ u in (0 : ℝ)..1,f u := by
  let c : ℝ := ∫ u in (0 : ℝ)..1,f u
  let g : ℝ → ℝ := fun t ↦ f t-c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hgp : Function.Periodic g 1 := fun t ↦ by simp [g,hp t]
  let ψ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t,g u
  have hd (t : ℝ) : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun t ↦ (hd t).differentiableAt,(funext fun t ↦ (hd t).deriv) ▸ hg⟩
  have hz : (∫ u in (0 : ℝ)..1,g u)=0 := by
    rw [show g=(fun t ↦ f t-c) from rfl,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
        intervalIntegrable_const,intervalIntegral.integral_const]
    simp [c]
  refine ⟨ψ,hψ,?_,fun t ↦ (hd t).deriv⟩
  intro t
  change (∫ u in (0 : ℝ)..t+1,g u)=∫ u in (0 : ℝ)..t,g u
  rw [hgp.intervalIntegral_add_eq_add 0 t (fun _ _ ↦ hg.continuous.intervalIntegrable _ _)]
  simp only [zero_add,hz,add_zero]

lemma axial_scalar_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (i : Fin 3) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa only [PiLp.add_apply,latticeVector,WithLp.ofLp_toLp,mul_one] using hp.int_mul (m i) (x i)

lemma axial_scalar_fderiv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i : Fin 3) (x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ f (y i)) x v=deriv f (x i)*v i := by
  have hh := (hf (x i)).hasDerivAt.comp_hasFDerivAt x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : Cover ↦ f (y i)) _ x at hh
  rw [hh.fderiv]
  rfl

lemma axial_field_tangentialDivergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x ν : Cover) :
    tangentialDivergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x ν=
      deriv f (x i)*(1-(ν i)^2) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [tangentialDivergence_smul_const hd,axial_scalar_fderiv hf]
  simp [tangentPart,EuclideanSpace.inner_single_right,pow_two]

lemma axial_field_divergence {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Cover) :
    divergence (fun y : Cover ↦ f (y i) • EuclideanSpace.single i 1) x=deriv f (x i) := by
  have hd : DifferentiableAt ℝ (fun y : Cover ↦ f (y i)) x :=
    hf.differentiableAt.comp x (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiableAt
  rw [divergence_smul_const hd,axial_scalar_fderiv hf]
  simp

theorem sibling_axial_flux_derivative {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : Function.Periodic ψ 1) :
    (∫ z,deriv ψ ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))=
      H*∫ x in fundamentalCube∩quotientMap ⁻¹' E,deriv ψ (x i) := by
  have hfield : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Cover ↦ ψ (x i) • (EuclideanSpace.single i 1 : Cover)) :=
    (hψ.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hh := Periodic.tangent_firstVariation_of_coordinate hH hfield (fun m x ↦ by
    rw [axial_scalar_periodic hp i m x])
  simpa only [axial_field_tangentialDivergence (hψ.differentiable (by simp)),
    axial_field_divergence (hψ.differentiable (by simp))] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialTransverseMass (μ : FiniteMeasure NormalBundle) (i : Fin 3) : ℝ :=
  ∫ z,1-((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)

lemma normal_component_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (z.2 : Cover) i) :=
  (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.snd

lemma normal_axial_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun z : NormalBundle ↦ f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2))
      (μ : Measure NormalBundle) :=
  ((hf.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    normalEmbedding_continuous.fst)).mul
      (continuous_const.sub ((normal_component_continuous i).pow 2))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma normal_transverse_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (fun z : NormalBundle ↦ 1-((z.2 : Cover) i)^2) (μ : Measure NormalBundle) := by
  simpa only [one_mul] using normal_axial_integrable μ i (f := fun _ ↦ (1 : ℝ)) continuous_const

theorem axial_flux_marginal {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  obtain ⟨ψ,hψ,hψp,hd⟩ := smooth_periodic_centered_primitive hf hp
  have hh := sibling_axial_flux_derivative hH i hψ hψp
  simp_rw [hd,sub_mul] at hh
  have hiV : IntegrableOn (fun x : Cover ↦ f (x i))
      (fundamentalCube∩quotientMap ⁻¹' E) :=
    (integrableOn_fundamentalCube_of_continuous
      (hf.continuous.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous)).mono_set inter_subset_left
  rw [integral_sub (normal_axial_integrable μ i hf.continuous)
      ((normal_transverse_integrable μ i).const_mul _),integral_const_mul,
    integral_sub hiV (integrable_const _),integral_const] at hh
  simp only [Measure.real_def,Measure.restrict_apply_univ,smul_eq_mul] at hh
  change _-_ = H*(_-volume.real (fundamentalCube∩quotientMap ⁻¹' E)*_) at hh
  unfold axialTransverseMass
  nlinarith [hh]

theorem isMinimizerAt_axial_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      ∀ (i : Fin 3) (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → Function.Periodic f 1 →
      (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
        H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
        (axialTransverseMass μ i-H*V)*(∫ t in (0 : ℝ)..1,f t) := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  obtain ⟨μ,H,hμ,hCMC,hs⟩ := Periodic.isMinimizerAt_boundary_stability hV hF hmF
  refine ⟨μ,H,hμ.congr_ae hFE,?_⟩
  intro i f hf hp
  have hh := axial_flux_marginal (Periodic.coordinateCMC_of_global hμ hCMC) i hf hp
  rw [setIntegral_congr_set (liftSet_congr_ae hFE)] at hh
  have hvol : volume.real (fundamentalCube ∩ quotientMap ⁻¹' F)=V := by
    rw [←realVolume_lift hF,Measure.real,hmF.2.1,ENNReal.toReal_ofReal hV.1.le]
  simpa only [hvol] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_stationary_tubular_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H := by
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hpoint (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      ‖N x‖=1 ∧ divergence N x=H := by
    constructor
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
        continuous_const (fun m y ↦ by rw [hp]) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hn] with z hz
      rw [hz.1,z.2.property]
    · exact isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ (continuous_divergence hN)
        continuous_const (divergence_periodic hp) (fun _ _ ↦ rfl) hH x hx
  have hR := regularizedNormal_contDiff hN
  have hrp : ∀ m x,regularizedNormal N (x+latticeVector m)=regularizedNormal N x := by
    intro m x
    simp only [regularizedNormal,hp]
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),regularizedNormal N=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hn] with z hz
    exact regularizedNormal_eventuallyEq hz.2
  refine ⟨regularizedNormal N,hR,hrp,?_,?_⟩
  · filter_upwards [hn,he] with z hz hze
    exact hze.eq_of_nhds.trans hz.1
  · intro x hx
    refine ⟨regularizedNormal_unit_near hN.continuous (by rw [(hpoint x hx).1]; norm_num),?_⟩
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) (continuous_divergence hN)
      (divergence_periodic hrp) (divergence_periodic hp) _ x hx |>.trans (hpoint x hx).2
    filter_upwards [he] with z hz
    simp only [divergence_eq_coverTrace,hz.fderiv_eq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalSphere_sum_sq (ν : NormalSphere) : (∑ i : Fin 3,((ν : Cover) i)^2)=1 := by
  have hh := real_inner_self_eq_norm_sq (ν : Cover)
  rw [ν.property,one_pow] at hh
  simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,←pow_two] using hh

lemma normalSphere_coordinate_sq_le (ν : NormalSphere) (i : Fin 3) : ((ν : Cover) i)^2≤1 := by
  exact (Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) ↦ sq_nonneg ((ν : Cover) j))
    (Finset.mem_univ i)).trans_eq (normalSphere_sum_sq ν)

lemma axialTransverseMass_nonneg (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    0≤axialTransverseMass μ i :=
  integral_nonneg fun z ↦ sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)

lemma axialTransverseMass_sum (μ : FiniteMeasure NormalBundle) :
    (∑ i : Fin 3,axialTransverseMass μ i)=2*(μ.mass : ℝ) := by
  unfold axialTransverseMass
  rw [←integral_finsetSum _ (fun i _ ↦ normal_transverse_integrable μ i)]
  have hh (z : NormalBundle) : (∑ i : Fin 3,(1-((z.2 : Cover) i)^2))=(2 : ℝ) := by
    rw [Finset.sum_sub_distrib,normalSphere_sum_sq]
    norm_num
  simp_rw [hh]
  simp only [integral_const,smul_eq_mul,Measure.real_def,
    ←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
  ring

lemma axialTransverseMass_defect (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    axialTransverseMass μ i=(μ.mass : ℝ)-∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle) := by
  unfold axialTransverseMass
  have hi : Integrable (fun z : NormalBundle ↦ ((z.2 : Cover) i)^2) (μ : Measure NormalBundle) :=
    ((normal_component_continuous i).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (integrable_const _) hi,normalMeasure_integral_one]

theorem isMinimizerAt_nonstandard_axial_mass_lt {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) (i : Fin 3) :
    axialTransverseMass μ i<(μ.mass : ℝ) := by
  rw [axialTransverseMass_defect,sub_lt_self_iff]
  have hi : Integrable (fun z : NormalBundle ↦ ((z.2 : Cover) i)^2) (μ : Measure NormalBundle) :=
    ((normal_component_continuous i).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hznon : 0≤∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  by_contra hpos
  have hz := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ sq_nonneg ((z.2 : Cover) i)) hi).mp
    (le_antisymm (le_of_not_gt hpos) hznon)
  have hn0 : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1 i=0 := by
    filter_upwards [hae,hz] with z he hz
    rw [he]
    exact sq_eq_zero_iff.mp hz
  have hb0 (x : Torus) (hx : x∈frontier (openRepresentative E)) : N (representative x) i=0 := by
    apply isMinimizerAt_periodic_ae_eq_boundary ⟨hV.1,by linarith [hV.2]⟩ hE hmin hμ
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous).comp hN.continuous)
      continuous_const (fun m y ↦ by change N (y+latticeVector m) i=N y i; rw [hp]) (fun _ _ ↦ rfl) hn0 (representative x)
    simpa only [quotientMap_representative] using hx
  obtain ⟨hlo,hhi,hcong⟩ := isMinimizerAt_zero_axis_standard hV hmin hc hμ hN hp hae hb i hb0
  apply hstd
  unfold StandardRegionAt SmallStandardRegion
  rw [ite_eq_left hV.2]
  exact Or.inr (Or.inl ⟨hlo,hhi,hcong⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

def circleMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((n : ℝ)+1)
  rOut := 2/((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma circleMollifier_tendsto : Tendsto (fun n ↦ (circleMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [circleMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def circleSmoothApprox (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (circleMollifier n).normed volume ⋆ f

lemma circleSmoothApprox_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (circleSmoothApprox f n) :=
  (circleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (circleMollifier n).contDiff_normed hf.locallyIntegrable

lemma circleSmoothApprox_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (circleSmoothApprox f n) 1 := by
  intro x
  simp only [circleSmoothApprox,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [show x+1-y=(x-y)+1 by ring,hp]

lemma circleSmoothApprox_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n ↦ circleSmoothApprox f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous circleMollifier_tendsto hf x

lemma circleSmoothApprox_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ x,‖f x‖≤C)
    (n : ℕ) (x : ℝ) : ‖circleSmoothApprox f n x‖≤C := by
  rw [circleSmoothApprox,convolution_def]
  calc
    _ ≤ ∫ y : ℝ,(circleMollifier n).normed volume y*C := by
      apply norm_integral_le_of_norm_le ((circleMollifier n).integrable_normed.mul_const C)
      filter_upwards [] with y
      rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg ((circleMollifier n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hb (x-y)) ((circleMollifier n).nonneg_normed y)
    _ = C := by rw [integral_mul_const,(circleMollifier n).integral_normed,one_mul]

lemma circleSmoothApprox_integral_tendsto {α : Type*} [MeasurableSpace α]
    {η : Measure α} {g w : α → ℝ} (hg : Measurable g) (hw : Integrable w η)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x)*w x ∂η) atTop
      (𝓝 (∫ x,f (g x)*w x ∂η)) := by
  obtain ⟨C,hC⟩ := (hp.isBounded_of_continuous (by norm_num) hf).exists_norm_le
  have hbound (t : ℝ) : ‖f t‖≤C := hC _ ⟨t,rfl⟩
  apply tendsto_integral_of_dominated_convergence (fun x ↦ C*‖w x‖)
  · intro n
    exact (((circleSmoothApprox_contDiff hf n).continuous.measurable.comp hg).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  · exact hw.norm.const_mul C
  · intro n
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (circleSmoothApprox_bound hbound n (g x)) (norm_nonneg _)
  · filter_upwards [] with x
    exact (circleSmoothApprox_tendsto hf (g x)).mul tendsto_const_nhds

lemma circleSmoothApprox_integral_tendsto_finite {α : Type*} [MeasurableSpace α]
    {η : Measure α} [IsFiniteMeasure η] {g : α → ℝ} (hg : Measurable g)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun n ↦ ∫ x,circleSmoothApprox f n (g x) ∂η) atTop
      (𝓝 (∫ x,f (g x) ∂η)) := by
  simpa only [mul_one] using circleSmoothApprox_integral_tendsto hg
    (integrable_const (1 : ℝ) (μ := η)) hf hp

theorem axial_flux_marginal_continuous {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ z,f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))-
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      (axialTransverseMass μ i-H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))*
        ∫ t in (0 : ℝ)..1,f t := by
  let A := fundamentalCube∩quotientMap ⁻¹' E
  have hA : volume A≠⊤ := ne_top_of_le_ne_top (by rw [volume_fundamentalCube]; exact ENNReal.one_ne_top)
    (measure_mono inter_subset_left)
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hA.lt_top⟩
  have hs := circleSmoothApprox_integral_tendsto
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.fst).measurable)
    (normal_transverse_integrable μ i) hf hp
  have hv := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict A)
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).measurable hf hp
  have ht := circleSmoothApprox_integral_tendsto_finite (η := volume.restrict (Ioc (0 : ℝ) 1))
    measurable_id hf hp
  have ht' : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1,circleSmoothApprox f n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1,f t)) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),id_eq] using ht
  have hleft := hs.sub (hv.const_mul H)
  have hright := ht'.const_mul (axialTransverseMass μ i-H*volume.real A)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [] with n
  exact (axial_flux_marginal hH i (circleSmoothApprox_contDiff hf n)
    (circleSmoothApprox_periodic hp n)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev AxisCircle := AddCircle (1 : ℝ)

def axialSurfaceMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2))
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal
    (normal_transverse_integrable μ i).hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,inferInstance⟩

def axialVolumeMarginal (E : Set Torus) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)
  haveI : IsFiniteMeasure η := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono inter_subset_left).trans_lt (by rw [volume_fundamentalCube]; exact ENNReal.one_lt_top)⟩
  exact ⟨Measure.map (fun x : Cover ↦ (x i : AxisCircle)) η,inferInstance⟩

end CubicTorus
end
end
end

end OAI
