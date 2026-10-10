import OAI.Geometry.KahlerSplitting.PolydiskAxes

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

def IsHorizontal (atlas : Set (OpenPartialHomeomorph X (C × D))) (f : A → X) : Prop :=
  Continuous f ∧ ∀ e ∈ atlas,
    IsLocallyConstant (fun a : {a : A // f a ∈ e.source} ↦ (e (f a)).2)

def IsVertical (atlas : Set (OpenPartialHomeomorph X (C × D))) (f : A → X) : Prop :=
  Continuous f ∧ ∀ e ∈ atlas,
    IsLocallyConstant (fun a : {a : A // f a ∈ e.source} ↦ (e (f a)).1)

lemma IsBox.horizontal {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A × B → X} (hf : IsBox atlas f) (b : B) :
    IsHorizontal atlas (fun a ↦ f (a,b)) :=
  ⟨hf.1.comp (continuous_id.prodMk continuous_const),fun e he ↦ (hf.2 e he).2 b⟩

lemma IsBox.vertical {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A × B → X} (hf : IsBox atlas f) (a : A) :
    IsVertical atlas (fun b ↦ f (a,b)) :=
  ⟨hf.1.comp (continuous_const.prodMk continuous_id),fun e he ↦ (hf.2 e he).1 a⟩

lemma IsHorizontal.precomp {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A → X} (hf : IsHorizontal atlas f) {a : B → A} (ha : Continuous a) :
    IsHorizontal atlas (f ∘ a) := by
  refine ⟨hf.1.comp ha,fun e he ↦ ?_⟩
  exact (hf.2 e he).comp_continuous
    ((ha.comp continuous_subtype_val).subtype_mk fun x ↦ x.property)

lemma IsVertical.precomp {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A → X} (hf : IsVertical atlas f) {a : B → A} (ha : Continuous a) :
    IsVertical atlas (f ∘ a) := by
  refine ⟨hf.1.comp ha,fun e he ↦ ?_⟩
  exact (hf.2 e he).comp_continuous
    ((ha.comp continuous_subtype_val).subtype_mk fun x ↦ x.property)

end ProductBoxTopology

open Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A]

lemma horizontal_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {α : A → X.Carrier}
    (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk r → X.Carrier,
      IsDiskHorizontal S f ∧ ∃ a : U → Polydisk r, Continuous a ∧ ∀ y, f (a y)=α y := by
  obtain ⟨e,hxe,he0⟩ := exists_splittingChart S h₁ h₂ (α x)
  let W := α ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hα.1
  have hlc := (hα.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨x,hxe⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨x,hxe⟩ _).mp hlc
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp (inter_mem hV (hW.mem_nhds hxe))
  have heU (y : U) : α y ∈ e.chart.source := (hUV y.property).2
  have hcoord (y : U) : (e.chart (α y)).2=0 := by
    have hh := hsub (show (⟨y,heU y⟩ : W) ∈ Subtype.val ⁻¹' V from (hUV y.property).1)
    change (e.chart (α y)).2=(e.chart (α x)).2 at hh
    rw [he0] at hh
    exact hh
  let a : U → Polydisk r := fun y ↦ ⟨(e.radius : ℂ)⁻¹ • (e.chart (α y)).1,
    unscale_mem_ball e.radius_pos (by
      have hh := e.chart.map_source (heU y)
      rw [e.product_range] at hh
      exact hh.1)⟩
  have ha : Continuous a := by
    apply Continuous.subtype_mk
    exact ((e.chart.continuousOn.comp_continuous (hα.1.comp continuous_subtype_val)
      heU).fst.const_smul ((e.radius : ℂ)⁻¹))
  let q : Polydisk s := ⟨0,mem_ball_self zero_lt_one⟩
  refine ⟨U,hU,hxU,fun p ↦ e.unitMap (p,q),
    ⟨fun p ↦ e.unitMap (p,0),e.unitMap_block.horizontal_slice isOpen_ball isOpen_ball q.property,
      fun _ ↦ rfl⟩,a,ha,?_⟩
  intro y
  have hh := e.unitMap_coordinates (heU y)
  simpa only [hcoord y,smul_zero] using hh

lemma vertical_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {β : A → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk s → X.Carrier,
      IsDiskVertical S f ∧ ∃ b : U → Polydisk s, Continuous b ∧ ∀ y, f (b y)=β y := by
  obtain ⟨e,hxe,he0⟩ := exists_splittingChart S h₁ h₂ (β x)
  let W := β ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hβ.1
  have hlc := (hβ.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨x,hxe⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨x,hxe⟩ _).mp hlc
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp (inter_mem hV (hW.mem_nhds hxe))
  have heU (y : U) : β y ∈ e.chart.source := (hUV y.property).2
  have hcoord (y : U) : (e.chart (β y)).1=0 := by
    have hh := hsub (show (⟨y,heU y⟩ : W) ∈ Subtype.val ⁻¹' V from (hUV y.property).1)
    change (e.chart (β y)).1=(e.chart (β x)).1 at hh
    rw [he0] at hh
    exact hh
  let b : U → Polydisk s := fun y ↦ ⟨(e.radius : ℂ)⁻¹ • (e.chart (β y)).2,
    unscale_mem_ball e.radius_pos (by
      have hh := e.chart.map_source (heU y)
      rw [e.product_range] at hh
      exact hh.2)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact ((e.chart.continuousOn.comp_continuous (hβ.1.comp continuous_subtype_val)
      heU).snd.const_smul ((e.radius : ℂ)⁻¹))
  let p : Polydisk r := ⟨0,mem_ball_self zero_lt_one⟩
  refine ⟨U,hU,hxU,fun q ↦ e.unitMap (p,q),
    ⟨fun q ↦ e.unitMap (0,q),e.unitMap_block.vertical_slice isOpen_ball isOpen_ball p.property,
      fun _ ↦ rfl⟩,b,hb,?_⟩
  intro y
  have hh := e.unitMap_coordinates (heU y)
  simpa only [hcoord y,smul_zero] using hh

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology

namespace ClosedCoverGlue
variable {A X ι : Type*} [TopologicalSpace A] [TopologicalSpace X] [Finite ι]

theorem exists_glue (U : ι → Set A) (hU : ∀ i, IsClosed (U i))
    (cover : ∀ x, ∃ i, x ∈ U i) (f : ∀ i, U i → X) (hf : ∀ i, Continuous (f i))
    (compat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) :
    ∃ F : A → X, Continuous F ∧ ∀ i (x : U i), F x=f i x := by
  classical
  let F : A → X := fun x ↦ f (cover x).choose ⟨x,(cover x).choose_spec⟩
  have herr (i : ι) (x : U i) : F x=f i x := compat _ _ _ _ _
  refine ⟨F,?_,herr⟩
  apply (locallyFinite_of_finite U).continuous (iUnion_eq_univ_iff.mpr cover) hU
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (U i).domRestrict F=f i := funext fun x ↦ herr i x
  rw [he]
  exact hf i

end ClosedCoverGlue
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
open IntervalChain
variable {X C D : Type*} [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

theorem grid_glue (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (t u : ℕ → I) (ht0 : t 0=0) (hu0 : u 0=0) (ht : Monotone t) (hu : Monotone u)
    (N M : ℕ) (hN : t N=1) (hM : u M=1)
    (R : ∀ i j, cell t i × cell u j → X) (hR : ∀ i j, IsBox atlas (R i j))
    (seamA : ∀ i j (y : cell u j),
      R i j (⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩,y)=
      R (i+1) j (⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩,y))
    (seamB : ∀ i j (x : cell t i),
      R i j (x,⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩)=
      R i (j+1) (x,⟨u (j+1),le_rfl,hu (Nat.le_succ (j+1))⟩)) :
    ∃ F : I × I → X, IsBox atlas F ∧
      ∀ i j (x : cell t i) (y : cell u j), F (x,y)=R i j (x,y) := by
  classical
  have compat (i j k l : ℕ) (p : I × I) (hi : p.1 ∈ cell t i) (hj : p.2 ∈ cell u j)
      (hk : p.1 ∈ cell t k) (hl : p.2 ∈ cell u l) :
      R i j (⟨p.1,hi⟩,⟨p.2,hj⟩)=R k l (⟨p.1,hk⟩,⟨p.2,hl⟩) := by
    have hA := overlap t ht (fun i x ↦ R i j (x,⟨p.2,hj⟩))
      (fun i ↦ seamA i j ⟨p.2,hj⟩) i k p.1 hi hk
    have hB := overlap u hu (fun j y ↦ R k j (⟨p.1,hk⟩,y))
      (fun j ↦ seamB k j ⟨p.1,hk⟩) j l p.2 hj hl
    exact hA.trans hB
  let K := Fin (N+1) × Fin (M+1)
  let U : K → Set I := fun k ↦ cell t k.1
  let V : K → Set I := fun k ↦ cell u k.2
  have cover (p : I × I) : ∃ k : K, p ∈ U k ×ˢ V k := by
    obtain ⟨i,hi,hpi⟩ := covers t ht0 ht N hN p.1
    obtain ⟨j,hj,hpj⟩ := covers u hu0 hu M hM p.2
    exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hpi,hpj⟩
  let f : ∀ k : K, (U k ×ˢ V k) → X := fun k p ↦
    R k.1 k.2 (⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩)
  have hf (k : K) : Continuous (f k) := (hR k.1 k.2).1.comp
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  obtain ⟨F,hF,hFr⟩ := ClosedCoverGlue.exists_glue (fun k ↦ U k ×ˢ V k)
    (fun _ ↦ isClosed_Icc.prod isClosed_Icc) cover f hf
    (fun a b p ha hb ↦ compat a.1 a.2 b.1 b.2 p ha.1 ha.2 hb.1 hb.2)
  have he (i j : ℕ) (x : cell t i) (y : cell u j) : F (x,y)=R i j (x,y) := by
    obtain ⟨k,hk⟩ := cover (x,y)
    exact (hFr k ⟨(x,y),hk⟩).trans (compat k.1 k.2 i j (x,y) hk.1 hk.2 x.property y.property)
  refine ⟨F,?_,he⟩
  apply IsBox.of_closed_rectangles hF U V (fun _ ↦ isClosed_Icc) (fun _ ↦ isClosed_Icc) cover
  intro k
  have hh : (fun p : U k × V k ↦ F (p.1,p.2))=R k.1 k.2 :=
    funext fun p ↦ he k.1 k.2 p.1 p.2
  rw [hh]
  exact hR k.1 k.2

end ProductBoxTopology
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
open IntervalChain
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem path_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : I → X.Carrier} (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α)
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β) (hbase : α 0=β 0) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      (∀ x, R (x,0)=α x) ∧ (∀ y, R (0,y)=β y) := by
  obtain ⟨t,ht0,ht,⟨N,hN⟩,A,hA,a,ha,eA⟩ :=
    PathSubdivision.parameterize α (IsDiskHorizontal S) (horizontal_local_parameter h₁ h₂ hα)
  obtain ⟨u,hu0,hu,⟨M,hM⟩,B,hB,b,hb,eB⟩ :=
    PathSubdivision.parameterize β (IsDiskVertical S) (vertical_local_parameter h₁ h₂ hβ)
  let lo : ℕ → Polydisk r := fun i ↦ a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩
  let hi : ℕ → Polydisk r := fun i ↦ a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩
  let bot : ℕ → Polydisk s := fun j ↦ b j ⟨u j,le_rfl,hu (Nat.le_succ j)⟩
  let top : ℕ → Polydisk s := fun j ↦ b j ⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩
  have joinA (i : ℕ) : A i (hi i)=A (i+1) (lo (i+1)) :=
    (eA i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).trans
      (eA (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩).symm
  have joinB (j : ℕ) : B j (top j)=B (j+1) (bot (j+1)) :=
    (eB j ⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩).trans
      (eB (j+1) ⟨u (j+1),le_rfl,hu (Nat.le_succ (j+1))⟩).symm
  have corner : A 0 (lo 0)=B 0 (bot 0) := by
    change A 0 (a 0 _)=B 0 (b 0 _)
    rw [eA,eB]
    change α (t 0)=β (u 0)
    simpa only [ht0,hu0] using hbase
  obtain ⟨F,hF,hFa,hFb,hFh,hFv⟩ :=
    holomorphic_grid g h₁ h₂ A hA lo hi joinA B hB bot top joinB corner
  let tile (i j : ℕ) : cell t i × cell u j → X.Carrier :=
    fun p ↦ F i j (a i p.1,b j p.2)
  have htile (i j : ℕ) : ProductBoxTopology.IsBox (splittingAtlas S) (tile i j) :=
    (hF i j).plaqueBox.precomp (ha i) (hb j)
  obtain ⟨R,hR,hRt⟩ := ProductBoxTopology.grid_glue (splittingAtlas S) t u ht0 hu0 ht hu
    N M (hN N le_rfl) (hM M le_rfl) tile htile
    (fun i j y ↦ hFh i j (b j y)) (fun i j x ↦ hFv i j (a i x))
  refine ⟨R,hR,?_,?_⟩
  · intro x
    obtain ⟨i,_,hxi⟩ := covers t ht0 ht N (hN N le_rfl) x
    let xx : cell t i := ⟨x,hxi⟩
    let yy : cell u 0 := ⟨u 0,le_rfl,hu (Nat.le_succ 0)⟩
    calc R (x,0) = tile i 0 (xx,yy) := by simpa only [yy,hu0] using hRt i 0 xx yy
         _ = A i (a i xx) := hFa i (a i xx)
         _ = α x := eA i xx
  · intro y
    obtain ⟨j,_,hyj⟩ := covers u hu0 hu M (hM M le_rfl) y
    let xx : cell t 0 := ⟨t 0,le_rfl,ht (Nat.le_succ 0)⟩
    let yy : cell u j := ⟨y,hyj⟩
    calc R (0,y) = tile 0 j (xx,yy) := by simpa only [xx,ht0] using hRt 0 j xx yy
         _ = B j (b j yy) := hFb j (b j yy)
         _ = β y := eB j yy

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
open IntervalChain
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A]

lemma continuous_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {γ : A → X.Carrier}
    (hγ : Continuous γ) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk r × Polydisk s → X.Carrier,
      IsDiskTile S f ∧ ∃ a : U → Polydisk r × Polydisk s, Continuous a ∧
        ∀ y, f (a y)=γ y := by
  obtain ⟨e,hxe,_⟩ := exists_splittingChart S h₁ h₂ (γ x)
  let U := γ ⁻¹' e.chart.source
  have heU (y : U) : γ y ∈ e.chart.source := y.property
  have hcoord (y : U) : e.chart (γ y) ∈ ball 0 e.radius ×ˢ ball 0 e.radius := by
    simpa only [←e.product_range] using e.chart.map_source (heU y)
  let a : U → Polydisk r × Polydisk s := fun y ↦
    (⟨(e.radius : ℂ)⁻¹ • (e.chart (γ y)).1,unscale_mem_ball e.radius_pos (hcoord y).1⟩,
     ⟨(e.radius : ℂ)⁻¹ • (e.chart (γ y)).2,unscale_mem_ball e.radius_pos (hcoord y).2⟩)
  have hc := e.chart.continuousOn.comp_continuous (hγ.comp continuous_subtype_val) heU
  have ha : Continuous a :=
    ((hc.fst.const_smul ((e.radius : ℂ)⁻¹)).subtype_mk _).prodMk
      ((hc.snd.const_smul ((e.radius : ℂ)⁻¹)).subtype_mk _)
  exact ⟨U,e.chart.open_source.preimage hγ,hxe,fun p ↦ e.unitMap (p.1,p.2),
    ⟨e.unitMap,e.unitMap_block,fun _ ↦ rfl⟩,a,ha,fun y ↦ e.unitMap_coordinates (heU y)⟩

theorem path_diagonal [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {γ : I → X.Carrier} (hγ : Continuous γ) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      ∀ t, R (t,t)=γ t := by
  obtain ⟨t,ht0,ht,⟨N,hN⟩,D,hD,a,ha,eD⟩ :=
    PathSubdivision.parameterize γ (IsDiskTile (d:=r) (e:=s) S)
      (continuous_local_parameter h₁ h₂ hγ)
  let lo : ℕ → Polydisk r := fun i ↦ (a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩).1
  let hi : ℕ → Polydisk r := fun i ↦ (a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).1
  let bot : ℕ → Polydisk s := fun i ↦ (a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩).2
  let top : ℕ → Polydisk s := fun i ↦ (a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).2
  have join (i : ℕ) : D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1)) :=
    (eD i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).trans
      (eD (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩).symm
  obtain ⟨F,hF,hFD,hFh,hFv⟩ := RectangleGrid.diagonal_grid
    {a | IsDiskHorizontal S a} {b | IsDiskVertical S b} {f | IsDiskTile S f}
    (fun _ h q ↦ h.horizontal q) (fun _ h p ↦ h.vertical p)
    (fun _ hA _ hB p q hc ↦ disk_fill g h₁ h₂ hA hB p q hc)
    D hD lo hi bot top join
  let tile (i j : ℕ) : cell t i × cell t j → X.Carrier :=
    fun p ↦ F i j ((a i p.1).1,(a j p.2).2)
  have htile (i j : ℕ) : ProductBoxTopology.IsBox (splittingAtlas S) (tile i j) :=
    (hF i j).plaqueBox.precomp (ha i).fst (ha j).snd
  obtain ⟨R,hR,hRt⟩ := ProductBoxTopology.grid_glue (splittingAtlas S) t t ht0 ht0 ht ht
    N N (hN N le_rfl) (hN N le_rfl) tile htile
    (fun i j y ↦ hFh i j (a j y).2) (fun i j x ↦ hFv i j (a i x).1)
  refine ⟨R,hR,fun x ↦ ?_⟩
  obtain ⟨i,_,hxi⟩ := covers t ht0 ht N (hN N le_rfl) x
  let xx : cell t i := ⟨x,hxi⟩
  calc R (x,x)=tile i i (xx,xx) := hRt i i xx xx
       _ = D i (a i xx) := congrFun (hFD i) (a i xx)
       _ = γ x := eD i xx

end UniversalCoverSplitting
end
end

end OAI
