import Mathlib
import OAI.Geometry.BallPacking.Degree.BoxContinuation

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I B : Type*} [TopologicalSpace M]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {d : ℕ}

structure SignedModelAtlas (M I B : Type*) [TopologicalSpace M]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] where
  chart : I → OpenPartialHomeomorph M B
  cover : ∀ x : M,∃ i,x∈(chart i).source
  sign : I → ℝ
  sign_sq : ∀ i,sign i*sign i=1
  transition_smooth : ∀ i j,ContDiffOn ℝ ∞ (chart j ∘ (chart i).symm)
    ((chart i).symm ≫ₕ chart j).source
  orientation : ∀ i j,∀ q∈((chart i).symm ≫ₕ chart j).source,
    sign i*(fderiv ℝ (chart j ∘ (chart i).symm) q).det =
      sign j*|(fderiv ℝ (chart j ∘ (chart i).symm) q).det|

omit [FiniteDimensional ℝ B] in
lemma conjugate_clm_det [FiniteDimensional ℝ B]
    (e : B ≃L[ℝ] CoordinateSpace d) (A : B →L[ℝ] B) :
    (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap)).det=A.det := by
  exact LinearMap.det_conj A.toLinearMap e.toLinearEquiv

def SignedModelAtlas.toCoordinates (a : SignedModelAtlas M I B)
    (e : B ≃L[ℝ] CoordinateSpace d) : SignedSmoothAtlas M I d where
  chart i := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
  cover x := by
    obtain ⟨i,hi⟩ := a.cover x
    exact ⟨i,hi,mem_univ _⟩
  sign := a.sign
  sign_sq := a.sign_sq
  transition_smooth i j := by
    let c := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
    let b := (a.chart j).trans e.toHomeomorph.toOpenPartialHomeomorph
    have hs : MapsTo e.symm (c.symm ≫ₕ b).source ((a.chart i).symm ≫ₕ a.chart j).source := by
      intro q hq
      exact ⟨hq.1.2,hq.2.1⟩
    exact (e.contDiff.comp_contDiffOn ((a.transition_smooth i j).comp e.symm.contDiff.contDiffOn hs))
  orientation i j q hq := by
    let c := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
    let b := (a.chart j).trans e.toHomeomorph.toOpenPartialHomeomorph
    have hs : e.symm q∈((a.chart i).symm ≫ₕ a.chart j).source := ⟨hq.1.2,hq.2.1⟩
    have hd := ((a.transition_smooth i j).contDiffAt
      (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hs)).differentiableAt (by simp)
    have he := e.hasFDerivAt.comp q (hd.hasFDerivAt.comp q e.symm.hasFDerivAt)
    have he' : fderiv ℝ (b ∘ c.symm) q =
      e.toContinuousLinearMap.comp ((fderiv ℝ (a.chart j ∘ (a.chart i).symm) (e.symm q)).comp
        e.symm.toContinuousLinearMap) := he.fderiv
    change a.sign i*(fderiv ℝ (b ∘ c.symm) q).det =a.sign j*|(fderiv ℝ (b ∘ c.symm) q).det|
    rw [he',conjugate_clm_det]
    exact a.orientation i j (e.symm q) hs


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

def timeSpaceCoordinates (e : E ≃L[ℝ] CoordinateSpace m) : (ℝ × E) ≃L[ℝ] CoordinateSpace (m+1) where
  toFun v := Fin.cons v.1 (e v.2)
  invFun v := (v 0,e.symm (Fin.tail v))
  left_inv v := by simp only [Fin.cons_zero,Fin.tail_cons,e.symm_apply_apply,Prod.mk.eta]
  right_inv v := by simp only [e.apply_symm_apply,Fin.cons_self_tail]
  map_add' v w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp (e.continuous.comp continuous_snd)
  continuous_invFun := (continuous_apply 0).prodMk (e.symm.continuous.comp (continuous_pi (fun i => continuous_apply i.succ)))

lemma timeSpaceCoordinates_apply (e : E ≃L[ℝ] CoordinateSpace m) (v : ℝ × E) :
    timeSpaceCoordinates e v=Fin.cons v.1 (e v.2) := rfl
lemma timeSpaceCoordinates_symm_apply (e : E ≃L[ℝ] CoordinateSpace m) (v : CoordinateSpace (m+1)) :
    (timeSpaceCoordinates e).symm v=(v 0,e.symm (Fin.tail v)) := rfl


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {m : ℕ}

def initialCollarDensity (a b : ℝ) (ρ : CoordinateSpace m → ℝ) (v : CoordinateSpace (m+1)) : ℝ :=
  deriv (collarRise a b) (v 0)*ρ (Fin.tail v)

lemma initialCollarDensity_continuous (a b : ℝ) {ρ : CoordinateSpace m → ℝ}
    (hρ : Continuous ρ) : Continuous (initialCollarDensity a b ρ) :=
  (((collarRise_smooth a b).continuous_deriv (by simp)).comp (continuous_apply 0)).mul
    (hρ.comp tail_smooth.continuous)

lemma initialCollarDensity_support {a b : ℝ} (hab : a<b) (ρ : CoordinateSpace m → ℝ) :
    tsupport (initialCollarDensity a b ρ)⊆{v | v 0∈Icc a b ∧ Fin.tail v∈tsupport ρ} := by
  apply closure_minimal _ ((isClosed_Icc.preimage (continuous_apply 0)).inter
    ((isClosed_tsupport ρ).preimage tail_smooth.continuous))
  intro v hv
  constructor
  · by_contra hn
    exact hv (by simp [initialCollarDensity,collarRise_deriv_zero hab hn])
  · by_contra hn
    exact hv (by simp [initialCollarDensity,image_eq_zero_of_notMem_tsupport hn])

lemma initialCollarDensity_compact {a b : ℝ} (hab : a<b) {ρ : CoordinateSpace m → ℝ}
    (hρ : HasCompactSupport ρ) : HasCompactSupport (initialCollarDensity a b ρ) := by
  let e := timeSpaceCoordinates (ContinuousLinearEquiv.refl ℝ (CoordinateSpace m))
  have hK : IsCompact (e '' (Icc a b ×ˢ tsupport ρ)) := (isCompact_Icc.prod hρ).image e.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  intro v hv
  have hh := initialCollarDensity_support hab ρ hv
  refine ⟨(v 0,Fin.tail v),hh,?_⟩
  exact Fin.cons_self_tail v

lemma initialCollarDensity_integral_pos {a b : ℝ} (hab : a<b) {ρ : CoordinateSpace m → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρn : ∀ x,0≤ρ x) (hρ0 : 0<ρ 0) :
    0<∫v,initialCollarDensity a b ρ v := by
  obtain ⟨t,ht,hpos⟩ := collarRise_deriv_positive hab
  apply (initialCollarDensity_continuous a b hρ).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := Fin.cons t 0) (initialCollarDensity_compact hab hρc)
  · intro v
    exact mul_nonneg (collarRise_deriv_nonneg hab _) (hρn _)
  · exact (show 0 < initialCollarDensity a b ρ (Fin.cons t 0) by
      simpa only [initialCollarDensity,Fin.cons_zero,Fin.tail_cons] using mul_pos hpos hρ0).ne'

variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I]
  {atlas : SignedSmoothAtlas M I (m+1)} {K T : Set M}
  (p : AtlasPartition atlas K) (f : AtlasSmoothMap atlas (CoordinateSpace (m+1)))
  {a b c d : ℝ} {ρ : CoordinateSpace m → ℝ}

include p in

theorem collar_stokes_contradiction (hab : a<b) (hcd : c<d)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρn : ∀ x,0≤ρ x) (hρ0 : 0<ρ 0)
    (hK : IsCompact K) (hT : IsCompact T) (hTK : T⊆K)
    (hα : (f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
      (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)).SupportedIn K)
    (hdα : (f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
      (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)).exterior.SupportedIn T)
    (i : I) (hTi : T⊆(atlas.chart i).source)
    (hidentity : EqOn (f.map ∘ (atlas.chart i).symm) id (atlas.chart i).target)
    (hinitial : ∀ q∈(atlas.chart i).target,q 0<c)
    (hcover : tsupport (initialCollarDensity a b ρ)⊆(atlas.chart i).target) : False := by
  let α := f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
    (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)
  have hz := p.compact_stokes hK α hα
  rw [p.mass_eq_chartMass hT hTK α.exterior hdα i hTi] at hz
  have he : α.exterior.chartMass i=atlas.sign i*(∫q,initialCollarDensity a b ρ q) := by
    rw [AtlasForm.chartMass,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    dsimp only
    by_cases hq : q∈(atlas.chart i).target
    · rw [AtlasForm.chartExtension,indicator_of_mem hq]
      change atlas.sign i*(f.pullback _ _).exterior.form i q coordinateVector=_
      rw [collar_pullback_identity_density f (collarCutoff_smooth a b c d) hρ i hidentity hq,
        collarCutoff_deriv_initial hcd (hinitial q hq)]
      rfl
    · rw [AtlasForm.chartExtension,indicator_of_notMem hq]
      have hn : q∉tsupport (initialCollarDensity a b ρ) := fun hh => hq (hcover hh)
      rw [image_eq_zero_of_notMem_tsupport hn]
      rfl
  rw [he] at hz
  have hs : atlas.sign i≠0 := by
    intro h
    have hh := atlas.sign_sq i
    rw [h,zero_mul] at hh
    exact zero_ne_one hh
  exact (mul_ne_zero hs (initialCollarDensity_integral_pos hab hρ.continuous hρc hρn hρ0).ne') hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {M I B P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {d : ℕ}

structure ModelAtlasSmoothMap (a : SignedModelAtlas M I B) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  map : M → P
  smooth : ∀ i,ContDiffOn ℝ ∞ (map ∘ (a.chart i).symm) (a.chart i).target

def ModelAtlasSmoothMap.toCoordinates {a : SignedModelAtlas M I B}
    (f : ModelAtlasSmoothMap a P) (e : B ≃L[ℝ] CoordinateSpace d) :
    AtlasSmoothMap (a.toCoordinates e) P where
  map := f.map
  smooth i := (f.smooth i).comp e.symm.contDiff.contDiffOn (fun _ h => h.2)

 def AtlasSmoothMap.restrict {a : SignedSmoothAtlas M I d} (f : AtlasSmoothMap a P)
    (J : Set I) (W : TopologicalSpace.Opens M) (hW : Nonempty W)
    (hcover : ∀ x : W,∃ i∈J,x.val∈(a.chart i).source) :
    AtlasSmoothMap (a.restrict J W hW hcover) P where
  map x := f.map x.val
  smooth i := by
    let c := (a.chart i.val).subtypeRestr hW
    apply ((f.smooth i.val).mono ((a.chart i.val).subtypeRestr_target_subset hW)).congr
    intro q hq
    change f.map (c.symm q).val=f.map ((a.chart i.val).symm q)
    exact congrArg f.map ((a.chart i.val).subtypeRestr_symm_apply hW hq)

 def AtlasSmoothMap.comp {a : SignedSmoothAtlas M I d} (f : AtlasSmoothMap a P)
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (g : P → Q) (hg : ContDiff ℝ ∞ g) : AtlasSmoothMap a Q where
  map := g ∘ f.map
  smooth i := hg.comp_contDiffOn (f.smooth i)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {M I : Type*} [TopologicalSpace M] {d : ℕ}
lemma SignedSmoothAtlas.finite_inside (a : SignedSmoothAtlas M I d)
    {K N : Set M} (hK : IsCompact K) (hN : IsOpen N) (hKN : K⊆N)
    (p : M) (hp : p∈K) (i : I) (_hpi : p∈(a.chart i).source) :
    ∃ J : Finset I,i∈J ∧ ∃ W : TopologicalSpace.Opens M,
      K⊆W ∧ (W:Set M)⊆N ∧ ∃ _hW : Nonempty W,
        ∀ x : W,∃ j∈(J:Set I),x.val∈(a.chart j).source := by
  classical
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover (fun j => (a.chart j).source)
    (fun j => (a.chart j).open_source) (fun x hx => mem_iUnion.mpr (a.cover x))
  let A := insert i J
  let W : TopologicalSpace.Opens M := ⟨N∩⋃j∈A,(a.chart j).source,
    hN.inter (isOpen_biUnion (fun j hj => (a.chart j).open_source))⟩
  have hKW : K⊆W := by
    intro x hx
    refine ⟨hKN hx,?_⟩
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion₂.mpr ⟨j,Finset.mem_insert_of_mem hj,hxj⟩
  refine ⟨A,Finset.mem_insert_self _ _,W,hKW,fun _ h => h.1,⟨⟨p,hKW hp⟩⟩,?_⟩
  intro x
  obtain ⟨j,hj,hx⟩ := mem_iUnion₂.mp x.property.2
  exact ⟨j,hj,hx⟩

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
lemma small_inverse_bump (e : E ≃L[ℝ] CoordinateSpace m) {δ : ℝ} (hδ : 0<δ) :
    ∃ b : ContDiffBump (0:CoordinateSpace m),∀ z∈tsupport (b : CoordinateSpace m → ℝ),‖e.symm z‖≤δ := by
  have ho : IsOpen {z : CoordinateSpace m | ‖e.symm z‖<δ} :=
    isOpen_lt e.symm.continuous.norm continuous_const
  have h0 : (0:CoordinateSpace m)∈{z | ‖e.symm z‖<δ} := by simpa only [mem_ofPred_eq,map_zero,norm_zero] using hδ
  obtain ⟨r,hr,hrd⟩ := Metric.isOpen_iff.mp ho 0 h0
  let b : ContDiffBump (0:CoordinateSpace m) := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨b,?_⟩
  intro z hz
  rw [b.tsupport_eq,Metric.mem_closedBall,dist_zero_right] at hz
  exact (hrd (show z∈Metric.ball 0 r from by
    rw [Metric.mem_ball,dist_zero_right]
    exact hz.trans_lt (half_lt_self hr))).le

end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {M I E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem isolated_collar_impossible
    (a : SignedModelAtlas M I (ℝ × E)) (f : ModelAtlasSmoothMap a (ℝ × E))
    (hf : Continuous f.map) (i : I) (p : M) (hpi : p∈(a.chart i).source)
    (hp : f.map p=((1:ℝ)/8,0))
    (hidentity : EqOn (f.map ∘ (a.chart i).symm) id (a.chart i).target)
    (hinit : ∀ q∈(a.chart i).target,q.1<1/4)
    (hinj : ∀ x y : M,(f.map x).1<1/4 →(f.map y).1<1/4 →f.map x=f.map y →x=y)
    (N : Set M) (hN : IsOpen N) (hpN : p∈N)
    (δ₀ : ℝ) (hδ₀ : 0<δ₀)
    (hcompact : ∀ δ : ℝ,0<δ →δ≤δ₀ →IsCompact {x : M | x∈N ∧
      (f.map x).1∈Icc (0:ℝ) 1 ∧ ‖(f.map x).2‖≤δ})
    (hfinal : ∀ x∈N,3/4≤(f.map x).1 →‖(f.map x).2‖≤δ₀ →False) : False := by
  classical
  let m := Module.finrank ℝ E
  let e : E ≃L[ℝ] CoordinateSpace m := (Module.finBasis ℝ E).equivFunL
  let c := a.chart i
  have hpchart : c p=((1:ℝ)/8,0) := by
    have hh : f.map (c.symm (c p))=c p := hidentity (c.map_source hpi)
    rw [c.left_inv hpi,hp] at hh
    exact hh.symm
  let O := c.target∩c.symm ⁻¹' N
  have hO : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target hN
  have hpO : ((1:ℝ)/8,(0:E))∈O := by
    rw [←hpchart]
    exact ⟨c.map_source hpi,by simpa only [mem_preimage,c.left_inv hpi] using hpN⟩
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp hO _ hpO
  let s := min r ((1:ℝ)/16)/4
  have hs : 0<s := div_pos (lt_min hr (by norm_num)) (by norm_num)
  have hsm : s < min r ((1:ℝ)/16) := by dsimp [s]; linarith [lt_min hr (by norm_num : (0:ℝ)<1/16)]
  have hsr : s<r := hsm.trans_le (min_le_left _ _)
  have hs16 : s<1/16 := hsm.trans_le (min_le_right _ _)
  let δ := min δ₀ s/2
  have hδ : 0<δ := half_pos (lt_min hδ₀ hs)
  have hδ₀' : δ≤δ₀ := (half_le_self (lt_min hδ₀ hs).le).trans (min_le_left _ _)
  have hδs : δ<s := (half_lt_self (lt_min hδ₀ hs)).trans_le (min_le_right _ _)
  let A := (1:ℝ)/8-s/2
  let B := (1:ℝ)/8+s/2
  have hAB : A<B := by dsimp [A,B]; linarith
  have hA : 0<A := by dsimp [A]; linarith
  have hB : B<1/4 := by dsimp [B]; linarith
  have hbox (t : ℝ) (ht : t∈Icc A B) (y : E) (hy : ‖y‖≤δ) : (t,y)∈O := by
    apply hrO
    rw [Metric.mem_ball,Prod.dist_eq,dist_zero_right,Real.dist_eq,max_lt_iff,abs_lt]
    dsimp only [Prod.fst,Prod.snd]
    dsimp [A,B] at ht
    constructor
    · constructor <;> linarith [ht.1,ht.2]
    · exact hy.trans_lt (hδs.trans hsr)
  let K : Set M := {x | x∈N ∧ (f.map x).1∈Icc (0:ℝ) 1 ∧ ‖(f.map x).2‖≤δ}
  have hK : IsCompact K := hcompact δ hδ hδ₀'
  have hpK : p∈K := by
    refine ⟨hpN,?_,?_⟩ <;> simp only [hp,norm_zero]
    · constructor <;> norm_num
    · exact hδ.le
  let eco := timeSpaceCoordinates e
  let atlas := a.toCoordinates eco
  let fco := (f.toCoordinates eco).comp eco eco.contDiff
  have hpic : p∈(atlas.chart i).source := ⟨hpi,mem_univ _⟩
  obtain ⟨J,hiJ,W,hKW,hWN,hW,hcover⟩ := atlas.finite_inside hK hN (fun _ h => h.1) p hpK i hpic
  let af := atlas.restrict (J:Set I) W hW hcover
  let ff := fco.restrict (J:Set I) W hW hcover
  let j : (J:Set I) := ⟨i,hiJ⟩
  let KW : Set W := Subtype.val ⁻¹' K
  have hKWc : IsCompact KW := (Topology.IsEmbedding.subtypeVal.isCompact_preimage_iff
    (show K⊆range (Subtype.val : W → M) from fun x hx => ⟨⟨x,hKW hx⟩,rfl⟩)).mpr hK
  let T : Set W := KW∩{x | (f.map x.val).1∈Icc A B}
  have hT : IsCompact T := hKWc.inter_right (isClosed_Icc.preimage (continuous_fst.comp (hf.comp continuous_subtype_val)))
  have hTi : T⊆(af.chart j).source := by
    intro x hx
    have hxO := hbox _ hx.2 _ hx.1.2.2
    have hz := c.map_target hxO.1
    have he : f.map (c.symm (f.map x.val))=f.map x.val := hidentity hxO.1
    have hxx : c.symm (f.map x.val)=x.val := hinj _ _ (by rw [he]; exact hinit _ hxO.1)
      (hx.2.2.trans_lt hB) he
    have hsource : x.val∈c.source := hxx ▸ hz
    simpa only [af,SignedSmoothAtlas.restrict,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage] using
      (show x.val∈(atlas.chart i).source from ⟨hsource,mem_univ _⟩)
  obtain ⟨bump,hbump⟩ := small_inverse_bump e hδ
  let ρ : CoordinateSpace m → ℝ := bump
  have hρ : ContDiff ℝ ∞ ρ := bump.contDiff
  have hsmall (x : W) (hx : ρ (Fin.tail (ff.map x))≠0) : ‖(f.map x.val).2‖≤δ := by
    have hh := hbump (Fin.tail (ff.map x)) (subset_tsupport _ (show Fin.tail (ff.map x)∈support ρ from hx))
    simpa only [ff,AtlasSmoothMap.restrict,fco,AtlasSmoothMap.comp,ModelAtlasSmoothMap.toCoordinates,
      Function.comp_apply,eco,timeSpaceCoordinates_apply,Fin.tail_cons,e.symm_apply_apply] using hh
  have htime (x : W) : ff.map x 0=(f.map x.val).1 := rfl
  have hit (q : CoordinateSpace (m+1)) (hq : q∈(af.chart j).target) : eco.symm q∈c.target :=
    ((atlas.chart i).subtypeRestr_target_subset hW hq).2
  have hid : EqOn (ff.map ∘ (af.chart j).symm) id (af.chart j).target := by
    intro q hq
    have he := (atlas.chart i).subtypeRestr_symm_apply hW hq
    change ((af.chart j).symm q).val=(atlas.chart i).symm q at he
    change eco (f.map (((af.chart j).symm q).val))=q
    rw [he]
    change eco (f.map (c.symm (eco.symm q)))=q
    rw [show f.map (c.symm (eco.symm q))=eco.symm q from hidentity (hit q hq)]
    exact eco.apply_symm_apply q
  have hind (q : CoordinateSpace (m+1)) (hq : q∈(af.chart j).target) : q 0<(13:ℝ)/16 := by
    have hh := hinit _ (hit q hq)
    change q 0<1/4 at hh
    linarith
  have hden : tsupport (initialCollarDensity A B ρ)⊆(af.chart j).target := by
    intro q hq
    have hh := initialCollarDensity_support hAB ρ hq
    have hqO := hbox (q 0) hh.1 (e.symm (Fin.tail q)) (hbump _ hh.2)
    have hqOc : eco.symm q∈O := hqO
    let z := c.symm (eco.symm q)
    have hzmap : f.map z=eco.symm q := hidentity hqOc.1
    have hzK : z∈K := by
      refine ⟨hqOc.2,?_,?_⟩
      · rw [hzmap]
        change q 0∈Icc (0:ℝ) 1
        exact ⟨hA.le.trans hh.1.1,hh.1.2.trans (hB.le.trans (by norm_num))⟩
      · rw [hzmap]
        exact hbump _ hh.2
    let zw : W := ⟨z,hKW hzK⟩
    have hzc : z∈(atlas.chart i).source := ⟨c.map_target hqOc.1,mem_univ _⟩
    have hztarget := (atlas.chart i).map_subtype_source hW (x := zw) hzc
    have he : atlas.chart i z=q := by
      change eco (c (c.symm (eco.symm q)))=q
      rw [c.right_inv hqOc.1,eco.apply_symm_apply]
    exact he ▸ hztarget
  obtain ⟨partition⟩ := af.partition_exists hKWc
  let θ := collarCutoff A B ((13:ℝ)/16) ((7:ℝ)/8)
  have hθ : ContDiff ℝ ∞ θ := collarCutoff_smooth _ _ _ _
  have hα : (ff.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).SupportedIn KW := by
    apply ff.pullback_supported
    intro x hx
    by_cases hz : ρ (Fin.tail (ff.map x))=0
    · exact collarVolumeForm_zero_of_space hz
    have hsx := hsmall x hz
    have ht : (f.map x.val).1∉Icc (0:ℝ) 1 := by
      intro hh
      exact hx ⟨hWN x.property,hh,hsx⟩
    apply collarVolumeForm_zero_of_time
    apply collarCutoff_zero hAB (by linarith) (by norm_num)
    rw [htime]
    intro hh
    exact ht ⟨hA.le.trans hh.1,hh.2.trans (by norm_num)⟩
  have hdα : (ff.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.SupportedIn T := by
    apply collar_pullback_exterior_supported ff hθ hρ
    intro x hx
    by_cases hz : ρ (Fin.tail (ff.map x))=0
    · exact Or.inr hz
    refine Or.inl ?_
    by_contra ht
    have hsx := hsmall x hz
    have hts := collarCutoff_deriv_support hAB (by norm_num : (13:ℝ)/16<7/8)
      (subset_tsupport _ (show ff.map x 0∈support (deriv θ) from ht))
    rw [htime] at hts
    rcases hts with hh|hh
    · apply hx
      refine ⟨⟨hWN x.property,?_,hsx⟩,hh⟩
      exact ⟨hA.le.trans hh.1,hh.2.trans (hB.le.trans (by norm_num))⟩
    · exact hfinal x.val (hWN x.property) (le_trans (by norm_num) hh.1) (hsx.trans hδ₀')
  have hρ0 : 0<ρ 0 := by
    change 0<bump 0
    rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
    norm_num
  exact collar_stokes_contradiction partition ff hAB (by norm_num) hρ bump.hasCompactSupport
    (fun _ => bump.nonneg) hρ0 hKWc hT inter_subset_left
    hα hdα j hTi hid hind hden


end

end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
