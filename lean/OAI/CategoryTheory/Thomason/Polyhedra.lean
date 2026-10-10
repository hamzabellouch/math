import Mathlib

namespace OAI

/-! Polyhedra. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition

@[ext] structure PolyPoint (P : Type u) [PartialOrder P] where
  weights : P →₀ ℝ
  nonneg : ∀ p, 0 ≤ weights p
  total : weights.sum (fun _ r => r) = 1
  chain : IsChain (· ≤ ·) (weights.support : Set P)

namespace PolyPoint
variable {P : Type u} [PartialOrder P]
local instance polyhedraDecidableEq : DecidableEq P := Classical.decEq P

def Face (s : Finset P) := {x : PolyPoint P // x.weights.support ⊆ s}

instance faceTopology (s : Finset P) : TopologicalSpace (Face s) :=
  TopologicalSpace.induced (fun x p => x.val.weights p) inferInstance

lemma face_coords_injective (s : Finset P) :
    Function.Injective (fun x : Face s => (fun p => x.val.weights p)) := by
  intro x y h
  apply Subtype.ext
  apply PolyPoint.ext
  exact Finsupp.ext (congrFun h)

instance faceT2 (s : Finset P) : T2Space (Face s) :=
  (Topology.IsEmbedding.induced (face_coords_injective s)).t2Space

structure ChainIndex (P : Type u) [PartialOrder P] where
  carrier : Finset P
  chain : IsChain (· ≤ ·) (carrier : Set P)
  nonempty : carrier.Nonempty

instance weakTopology : TopologicalSpace (PolyPoint P) :=
  TopologicalSpace.coinduced
    (fun x : Σ s : ChainIndex P, Face s.carrier => x.2.val) inferInstance

lemma isClosed_iff_faces (A : Set (PolyPoint P)) :
    IsClosed A ↔ ∀ s : ChainIndex P,
      IsClosed ((fun x : Face s.carrier => x.val) ⁻¹' A) := by
  rw [isClosed_coinduced, isClosed_sigma_iff]
  rfl

lemma isClosed_of_face_finite {A : Set (PolyPoint P)}
    (hA : ∀ s : Finset P, ((fun x : Face s => x.val) ⁻¹' A).Finite) : IsClosed A := by
  rw [isClosed_iff_faces]
  exact fun s => (hA s.carrier).isClosed

theorem compact_finite_carrier {K : Set (PolyPoint P)} (hK : IsCompact K) :
    ∃ s : Finset P, ∀ x ∈ K, x.weights.support ⊆ s := by
  classical
  let V : Set P := {p | ∃ x ∈ K, p ∈ x.weights.support}
  let f : V → PolyPoint P := fun p => Classical.choose p.property
  have hfK (p : V) : f p ∈ K := (Classical.choose_spec p.property).1
  have hfp (p : V) : p.val ∈ (f p).weights.support :=
    (Classical.choose_spec p.property).2
  let R : Set (PolyPoint P) := Set.range f
  have hRK : R ⊆ K := by
    rintro x ⟨p, rfl⟩
    exact hfK p
  have hface (s : Finset P) : ((fun x : Face s => x.val) ⁻¹' R).Finite := by
    have hv : {p : V | p.val ∈ s}.Finite :=
      (s.finite_toSet).preimage Subtype.val_injective.injOn
    apply Set.Finite.of_finite_image (f := fun x : Face s => x.val) _
      Subtype.val_injective.injOn
    apply (hv.image f).subset
    rintro x ⟨y, ⟨p, hp⟩, rfl⟩
    refine ⟨p, ?_, hp⟩
    exact y.property ((congrArg (fun z : PolyPoint P => p.val ∈ z.weights.support) hp).mp
      (hfp p))
  have hclosed (A : Set (PolyPoint P)) (hA : A ⊆ R) : IsClosed A := by
    apply isClosed_of_face_finite
    intro s
    exact (hface s).subset (Set.preimage_mono hA)
  have hRcompact : IsCompact R := by
    simpa only [Set.inter_eq_right.mpr hRK] using hK.inter_right (hclosed R Set.Subset.rfl)
  have hRdiscrete : IsDiscrete R := by
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isClosed]
    intro A
    have hc : IsClosed (Subtype.val '' A : Set (PolyPoint P)) :=
      hclosed _ (by rintro x ⟨a, ha, rfl⟩; exact a.property)
    have he : (Subtype.val : R → PolyPoint P) ⁻¹' (Subtype.val '' A) = A := by
      ext x
      simp
    rw [← he]
    exact hc.preimage continuous_subtype_val
  have hRfinite : R.Finite := hRcompact.finite hRdiscrete
  have hVfinite : V.Finite := by
    apply (hRfinite.biUnion (fun x _ => x.weights.support.finite_toSet)).subset
    intro p hp
    exact Set.mem_iUnion_of_mem (f ⟨p,hp⟩)
      (Set.mem_iUnion_of_mem (Set.mem_range_self _) (hfp ⟨p,hp⟩))
  refine ⟨hVfinite.toFinset, ?_⟩
  intro x hx p hp
  exact hVfinite.mem_toFinset.mpr ⟨x,hx,hp⟩

lemma continuous_chainFace_val (s : ChainIndex P) :
    Continuous (fun x : Face s.carrier => x.val) := by
  have h : Continuous (fun x : Σ s : ChainIndex P, Face s.carrier => x.2.val) :=
    continuous_coinduced_rng
  exact h.comp (continuous_sigmaMk (i := s))

lemma continuous_weights (p : P) : Continuous (fun x : PolyPoint P => x.weights p) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  exact (continuous_apply p).comp continuous_induced_dom

instance : T2Space (PolyPoint P) :=
  T2Space.of_injective_continuous (f := fun x : PolyPoint P => (fun p => x.weights p))
    (by intro x y h; exact PolyPoint.ext (Finsupp.ext (congrFun h)))
    (continuous_pi continuous_weights)

def evalWeights {ι : Type*} [Fintype ι] (a : ι → P) (x : Convexity.StdSimplex ℝ ι) : P →₀ ℝ :=
  ∑ i, Finsupp.single (a i) (x.weights i)

omit [PartialOrder P] in
lemma evalWeights_support {ι : Type*} [Fintype ι] (a : ι → P) (x : Convexity.StdSimplex ℝ ι) :
    (evalWeights a x).support ⊆ Finset.univ.image a := by
  classical
  intro p hp
  by_contra h
  apply Finsupp.mem_support_iff.mp hp
  rw [evalWeights, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact Finsupp.single_eq_of_ne (by
    intro he
    apply h
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)

def eval {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι →o P)
    (x : Convexity.StdSimplex ℝ ι) : PolyPoint P where
  weights := evalWeights a x
  nonneg p := by
    classical
    rw [evalWeights, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Finsupp.single_apply]
      split_ifs
      · exact x.weights_nonneg i
      · exact le_rfl)
  total := by
    rw [evalWeights, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simpa only [Finsupp.sum_single_index] using x.total_of_fintype
  chain := by
    classical
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (evalWeights_support a x hp)
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (evalWeights_support a x hq)
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h)

lemma continuous_eval {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (a : ι →o P) :
    Continuous (eval a) := by
  classical
  let s := Finset.univ.image a
  let f : Convexity.StdSimplex ℝ ι → Face s := fun x => ⟨eval a x, evalWeights_support a x⟩
  have hf : Continuous f := by
    rw [continuous_induced_rng]
    apply continuous_pi
    intro p
    change Continuous (fun x : Convexity.StdSimplex ℝ ι => (evalWeights a x) p)
    simp only [evalWeights, Finsupp.finsetSum_apply, Finsupp.single_apply]
    apply continuous_finsetSum
    intro i hi
    split_ifs
    · exact Convexity.StdSimplex.continuous_weights_apply ℝ i
    · exact continuous_const
  let c : ChainIndex P := ⟨s, by
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h),
    Finset.image_nonempty.mpr Finset.univ_nonempty⟩
  exact (continuous_chainFace_val c).comp hf

omit [PartialOrder P] in
lemma evalWeights_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : κ → P) (b : ι → κ) (x : Convexity.StdSimplex ℝ ι) :
    evalWeights a (Convexity.StdSimplex.map b x) = evalWeights (a ∘ b) x := by
  classical
  simp only [evalWeights, ← Finsupp.mapDomain_fintype, Convexity.StdSimplex.weights_map,
    ← Finsupp.mapDomain_comp]

lemma eval_map {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (a : κ →o P) (b : ι →o κ) (x : Convexity.StdSimplex ℝ ι) :
    eval a (Convexity.StdSimplex.map b x) = eval (a.comp b) x := by
  apply PolyPoint.ext
  exact evalWeights_map a b x

omit [PartialOrder P] in
lemma evalWeights_apply_image {ι : Type*} [Fintype ι] (a : ι → P)
    (ha : Function.Injective a) (x : Convexity.StdSimplex ℝ ι) (i : ι) :
    evalWeights a x (a i) = x.weights i := by
  classical
  simp only [evalWeights, Finsupp.finsetSum_apply, Finsupp.single_apply, ha.eq_iff]
  simp

namespace ChainIndex

instance carrierLinearOrder (s : ChainIndex P) : LinearOrder s.carrier := by
  classical
  exact s.chain.lt_of_le.linearOrder

def dimension (s : ChainIndex P) : ℕ := s.carrier.card - 1

lemma card_eq (s : ChainIndex P) : Fintype.card s.carrier = s.dimension + 1 := by
  rw [Fintype.card_coe]
  have h := Finset.card_pos.mpr s.nonempty
  dsimp [dimension]
  omega

def enumerate (s : ChainIndex P) : Fin (s.dimension + 1) ≃o s.carrier :=
  Fintype.orderIsoFinOfCardEq s.carrier s.card_eq

def vertices (s : ChainIndex P) : Fin (s.dimension + 1) →o P :=
  (OrderHom.Subtype.val _).comp s.enumerate.toOrderEmbedding.toOrderHom

lemma vertices_injective (s : ChainIndex P) : Function.Injective s.vertices :=
  Subtype.val_injective.comp s.enumerate.injective

lemma vertices_mem (s : ChainIndex P) (i : Fin (s.dimension + 1)) :
    s.vertices i ∈ s.carrier := (s.enumerate i).property

lemma vertices_surjective (s : ChainIndex P) {p : P} (hp : p ∈ s.carrier) :
    ∃ i, s.vertices i = p := by
  obtain ⟨i,hi⟩ := s.enumerate.surjective ⟨p,hp⟩
  exact ⟨i,congrArg Subtype.val hi⟩

def coordinates (s : ChainIndex P) (x : Face s.carrier) :
    Convexity.StdSimplex ℝ (Fin (s.dimension + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun index => x.val.weights (s.vertices index))
  nonneg index := x.val.nonneg (s.vertices index)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ index, x.val.weights (s.vertices index) = 1
    calc
      ∑ i, x.val.weights (s.vertices i) = ∑ p : s.carrier, x.val.weights p.val :=
        Equiv.sum_comp s.enumerate.toEquiv (fun p : s.carrier => x.val.weights p.val)
      _ = ∑ p ∈ s.carrier, x.val.weights p := Finset.sum_attach _ _
      _ = 1 := (x.val.weights.sum_of_support_subset x.property (fun _ r => r)
        (fun _ _ => rfl)).symm.trans x.val.total

lemma continuous_coordinates (s : ChainIndex P) : Continuous s.coordinates := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
  apply continuous_pi
  intro i
  exact (continuous_apply (s.vertices i)).comp continuous_induced_dom

lemma eval_coordinates (s : ChainIndex P) (x : Face s.carrier) :
    eval s.vertices (s.coordinates x) = x.val := by
  apply PolyPoint.ext
  ext p
  by_cases hp : p ∈ s.carrier
  · obtain ⟨i,rfl⟩ := s.vertices_surjective hp
    exact evalWeights_apply_image s.vertices s.vertices_injective _ i
  · change evalWeights s.vertices (s.coordinates x) p = x.val.weights p
    have hz : x.val.weights p = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hp (x.property h))
    rw [hz]
    apply Finsupp.notMem_support_iff.mp
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (evalWeights_support s.vertices _ h)
    exact hp (he ▸ s.vertices_mem i)

end ChainIndex

def supportIndex (x : PolyPoint P) : ChainIndex P :=
  ⟨x.weights.support, x.chain, by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    have ht := x.total
    rw [h, Finsupp.sum_zero_index] at ht
    norm_num at ht⟩

end PolyPoint

open CategoryTheory Limits Simplicial Opposite

variable (P : Type u) [PartialOrder P]

noncomputable def polyCocone :
    Cocone ((CostructuredArrow.proj uliftYoneda.{u,0,0} (nerve P) ⋙
      uliftYoneda.{u,0,0}) ⋙ SSet.toTop.{u}) where
  pt := TopCat.of (PolyPoint P)
  ι := {
    app j := TopCat.ofHom ⟨fun z => PolyPoint.eval (SSet.yonedaEquiv j.hom).toOrderHom
      (j.left.toTopHomeo z), (PolyPoint.continuous_eval _).comp j.left.toTopHomeo.continuous⟩
    naturality j k a := by
      ext z
      change PolyPoint.eval (SSet.yonedaEquiv k.hom).toOrderHom
        (k.left.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.map a.left) z)) =
        PolyPoint.eval (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeo z)
      erw [SimplexCategory.toTopHomeo_naturality_apply]
      have hw : SSet.stdSimplex.map a.left ≫ k.hom = j.hom := CostructuredArrow.w a
      have hσ : (nerve P).map a.left.op (SSet.yonedaEquiv k.hom) =
          SSet.yonedaEquiv j.hom :=
        (SSet.yonedaEquiv_naturality a.left k.hom).trans (congrArg SSet.yonedaEquiv hw)
      rw [← hσ]
      exact PolyPoint.eval_map (SSet.yonedaEquiv k.hom).toOrderHom a.left.toOrderHom _ }

noncomputable def nerveRealizationIsColimit (P : Type u) [PartialOrder P] :
    IsColimit (SSet.toTop.mapCocone (Presheaf.tautologicalCocone'.{u} (nerve P))) :=
  isColimitOfPreserves SSet.toTop (Presheaf.isColimitTautologicalCocone'.{u} (nerve P))

noncomputable def realizationToPoly : |nerve P| ⟶ TopCat.of (PolyPoint P) :=
  (nerveRealizationIsColimit P).desc (polyCocone P)

variable {P}

def realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : |nerve P| :=
  SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
    ((SimplexCategory.mk n).toTopHomeo.symm x)

lemma continuous_realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P) :
    Continuous (realizeSimplex a) :=
  (SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)).hom.continuous.comp
    (SimplexCategory.mk n).toTopHomeo.symm.continuous

lemma realizeSimplex_map {m n : ℕ} (a : Fin (n + 1) →o P)
    (b : Fin (m + 1) →o Fin (n + 1)) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    realizeSimplex a (Convexity.StdSimplex.map b x) = realizeSimplex (a.comp b) x := by
  let β : SimplexCategory.mk m ⟶ SimplexCategory.mk n := SimplexCategory.mkHom b
  have hβ : SSet.stdSimplex.map β ≫ (SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor =
      (SSet.yonedaEquiv (X := nerve P)).symm (a.comp b).monotone.functor := by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    rfl
  have ht : (SimplexCategory.mk n).toTopHomeo.symm (Convexity.StdSimplex.map b x) =
      SSet.toTop.map (SSet.stdSimplex.map β)
        ((SimplexCategory.mk m).toTopHomeo.symm x) := by
    apply (SimplexCategory.mk n).toTopHomeo.injective
    rw [Homeomorph.apply_symm_apply]
    erw [SimplexCategory.toTopHomeo_naturality_apply]
    simp only [Homeomorph.apply_symm_apply]
    rfl
  change (SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor))
    ((SimplexCategory.mk n).toTopHomeo.symm (Convexity.StdSimplex.map b x)) = _
  calc
    _ = SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
        (SSet.toTop.map (SSet.stdSimplex.map β)
          ((SimplexCategory.mk m).toTopHomeo.symm x)) := congrArg _ ht
    _ = _ := congrArg (fun f : SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk m)) ⟶
        SSet.toTop.obj (nerve P) => f ((SimplexCategory.mk m).toTopHomeo.symm x))
      ((SSet.toTop.map_comp (SSet.stdSimplex.map β) _).symm.trans
        (congrArg SSet.toTop.map hβ))

namespace PolyPoint.ChainIndex

def inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier) :
    Fin (s.dimension + 1) →o Fin (t.dimension + 1) where
  toFun i := t.enumerate.symm ⟨s.vertices i, h (s.vertices_mem i)⟩
  monotone' := fun _ _ hij => t.enumerate.symm.monotone (s.vertices.monotone hij)

lemma vertices_inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier) :
    t.vertices.comp (inclusion h) = s.vertices := by
  ext i
  exact congrArg Subtype.val (t.enumerate.apply_symm_apply _)

lemma eval_injective (s : PolyPoint.ChainIndex P) : Function.Injective (PolyPoint.eval s.vertices) := by
  intro x y h
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  have hw := congrArg (fun z : PolyPoint P => z.weights (s.vertices i)) h
  exact (PolyPoint.evalWeights_apply_image s.vertices s.vertices_injective x i).symm.trans
    (hw.trans (PolyPoint.evalWeights_apply_image s.vertices s.vertices_injective y i))

lemma map_coordinates {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier)
    (x : PolyPoint.Face s.carrier) :
    Convexity.StdSimplex.map (inclusion h) (s.coordinates x) =
      t.coordinates ⟨x.val, x.property.trans h⟩ := by
  apply t.eval_injective
  calc
    PolyPoint.eval t.vertices (Convexity.StdSimplex.map (inclusion h) (s.coordinates x)) =
        PolyPoint.eval s.vertices (s.coordinates x) := by
      rw [PolyPoint.eval_map, vertices_inclusion]
    _ = x.val := s.eval_coordinates x
    _ = _ := (t.eval_coordinates ⟨x.val, x.property.trans h⟩).symm

def faceReal (s : PolyPoint.ChainIndex P) (x : PolyPoint.Face s.carrier) : |nerve P| :=
  realizeSimplex s.vertices (s.coordinates x)

lemma continuous_faceReal (s : PolyPoint.ChainIndex P) : Continuous s.faceReal :=
  (continuous_realizeSimplex s.vertices).comp s.continuous_coordinates

lemma faceReal_inclusion {s t : PolyPoint.ChainIndex P} (h : s.carrier ⊆ t.carrier)
    (x : PolyPoint.Face s.carrier) :
    t.faceReal ⟨x.val, x.property.trans h⟩ = s.faceReal x := by
  unfold faceReal
  rw [← map_coordinates h x, realizeSimplex_map, vertices_inclusion]

end PolyPoint.ChainIndex

def polyToRealization (x : PolyPoint P) : |nerve P| :=
  x.supportIndex.faceReal ⟨x, Finset.Subset.refl _⟩

lemma polyToRealization_face (s : PolyPoint.ChainIndex P) (x : PolyPoint.Face s.carrier) :
    polyToRealization x.val = s.faceReal x := by
  exact (PolyPoint.ChainIndex.faceReal_inclusion x.property
    (⟨x.val, Finset.Subset.refl _⟩ : PolyPoint.Face x.val.supportIndex.carrier)).symm

lemma continuous_polyToRealization : Continuous (@polyToRealization P _) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  have he : (fun x : PolyPoint.Face s.carrier => polyToRealization x.val) = s.faceReal :=
    funext (polyToRealization_face s)
  exact he ▸ s.continuous_faceReal

namespace PolyPoint
local instance imageDecidableEq : DecidableEq P := Classical.decEq P

def imageIndex {n : ℕ} (a : Fin (n + 1) →o P) : ChainIndex P where
  carrier := Finset.univ.image a
  chain := by
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h)
  nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty

def imageOrdinal {n : ℕ} (a : Fin (n + 1) →o P) :
    Fin (n + 1) →o Fin ((imageIndex a).dimension + 1) where
  toFun i := (imageIndex a).enumerate.symm
    ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  monotone' := fun _ _ h => (imageIndex a).enumerate.symm.monotone (a.monotone h)

lemma image_vertices {n : ℕ} (a : Fin (n + 1) →o P) :
    (imageIndex a).vertices.comp (imageOrdinal a) = a := by
  ext i
  exact congrArg Subtype.val ((imageIndex a).enumerate.apply_symm_apply _)

end PolyPoint

lemma polyToRealization_eval {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    polyToRealization (PolyPoint.eval a x) = realizeSimplex a x := by
  let s := PolyPoint.imageIndex a
  let y : PolyPoint.Face s.carrier := ⟨PolyPoint.eval a x, PolyPoint.evalWeights_support a x⟩
  have hcoord : s.coordinates y = Convexity.StdSimplex.map (PolyPoint.imageOrdinal a) x := by
    apply s.eval_injective
    calc
      PolyPoint.eval s.vertices (s.coordinates y) = PolyPoint.eval a x :=
        s.eval_coordinates y
      _ = PolyPoint.eval (s.vertices.comp (PolyPoint.imageOrdinal a)) x := by
        rw [PolyPoint.image_vertices]
      _ = _ := (PolyPoint.eval_map s.vertices (PolyPoint.imageOrdinal a) x).symm
  calc
    polyToRealization (PolyPoint.eval a x) = s.faceReal y := polyToRealization_face s y
    _ = realizeSimplex s.vertices (Convexity.StdSimplex.map (PolyPoint.imageOrdinal a) x) :=
      congrArg (realizeSimplex s.vertices) hcoord
    _ = _ := by rw [realizeSimplex_map, PolyPoint.image_vertices]

lemma realizationToPoly_realizeSimplex {n : ℕ} (a : Fin (n + 1) →o P)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    realizationToPoly P (realizeSimplex a x) = PolyPoint.eval a x := by
  let j : CostructuredArrow uliftYoneda.{u,0,0} (nerve P) :=
    CostructuredArrow.mk ((SSet.yonedaEquiv (X := nerve P)).symm a.monotone.functor)
  have h := ConcreteCategory.congr_hom
    ((nerveRealizationIsColimit P).fac (polyCocone P) j)
    ((SimplexCategory.mk n).toTopHomeo.symm x)
  change realizationToPoly P (realizeSimplex a x) =
    PolyPoint.eval (SSet.yonedaEquiv ((SSet.yonedaEquiv (X := nerve P)).symm
      a.monotone.functor)).toOrderHom
      ((SimplexCategory.mk n).toTopHomeo ((SimplexCategory.mk n).toTopHomeo.symm x)) at h
  have hσ : (SSet.yonedaEquiv ((SSet.yonedaEquiv (X := nerve P)).symm
      a.monotone.functor)).toOrderHom = a :=
    congrArg Functor.toOrderHom ((SSet.yonedaEquiv (X := nerve P)).apply_symm_apply
      a.monotone.functor)
  exact h.trans ((congrArg (fun b => PolyPoint.eval b
      ((SimplexCategory.mk n).toTopHomeo ((SimplexCategory.mk n).toTopHomeo.symm x))) hσ).trans
    (congrArg (PolyPoint.eval a) ((SimplexCategory.mk n).toTopHomeo.apply_symm_apply x)))

lemma realizationToPoly_polyToRealization (x : PolyPoint P) :
    realizationToPoly P (polyToRealization x) = x := by
  exact (realizationToPoly_realizeSimplex x.supportIndex.vertices
    (x.supportIndex.coordinates ⟨x, Finset.Subset.refl _⟩)).trans
    (x.supportIndex.eval_coordinates ⟨x, Finset.Subset.refl _⟩)

noncomputable def polyToRealizationHom : TopCat.of (PolyPoint P) ⟶ |nerve P| :=
  TopCat.ofHom ⟨polyToRealization, continuous_polyToRealization⟩

lemma realizationToPoly_comp_polyToRealization :
    realizationToPoly P ≫ polyToRealizationHom = 𝟙 _ := by
  apply (nerveRealizationIsColimit P).hom_ext
  intro j
  ext z
  have hx := polyToRealization_eval (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeo z)
  have hh := realizationToPoly_realizeSimplex (SSet.yonedaEquiv j.hom).toOrderHom
    (j.left.toTopHomeo z)
  have he : realizeSimplex (SSet.yonedaEquiv j.hom).toOrderHom (j.left.toTopHomeo z) =
      SSet.toTop.map j.hom z := by
    simp only [realizeSimplex]
    have hσ : (SSet.yonedaEquiv j.hom).toOrderHom.monotone.functor =
        SSet.yonedaEquiv j.hom := rfl
    rw [hσ]
    have heq := (SSet.yonedaEquiv (X := nerve P)).symm_apply_apply j.hom
    have hv := congrArg (fun f : SSet.stdSimplex.obj j.left ⟶ nerve P => SSet.toTop.map f z) heq
    change SSet.toTop.map ((SSet.yonedaEquiv (X := nerve P)).symm
      (SSet.yonedaEquiv j.hom)) (j.left.toTopHomeo.symm (j.left.toTopHomeo z)) = _
    exact (congrArg (SSet.toTop.map _) (j.left.toTopHomeo.symm_apply_apply z)).trans hv
  exact (congrArg polyToRealization ((congrArg (realizationToPoly P) he).symm.trans hh)).trans
    (hx.trans he)

lemma polyToRealization_realizationToPoly (z : |nerve P|) :
    polyToRealization (realizationToPoly P z) = z :=
  ConcreteCategory.congr_hom realizationToPoly_comp_polyToRealization z

noncomputable def nerveRealizationHomeomorph : |nerve P| ≃ₜ PolyPoint P where
  toFun := realizationToPoly P
  invFun := polyToRealization
  left_inv := polyToRealization_realizationToPoly
  right_inv := realizationToPoly_polyToRealization
  continuous_toFun := (realizationToPoly P).hom.continuous
  continuous_invFun := continuous_polyToRealization

theorem nerve_compact_finite_carrier {K : Set |nerve P|} (hK : IsCompact K) :
    ∃ s : Finset P, ∀ z ∈ K, (realizationToPoly P z).weights.support ⊆ s := by
  obtain ⟨s, hs⟩ := PolyPoint.compact_finite_carrier
    (hK.image (realizationToPoly P).hom.continuous)
  exact ⟨s, fun z hz => hs _ ⟨z,hz,rfl⟩⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Simplicial Opposite PartialOrder

namespace Thomason.GeometricRecognition
namespace PolyPoint
variable {P : Type u} [PartialOrder P]
local instance barycenterDecidableEq : DecidableEq P := Classical.decEq P

def barycenter (s : NonemptyFiniteChains P) : PolyPoint P where
  weights := ∑ p ∈ s.finset, Finsupp.single p (s.finset.card : ℝ)⁻¹
  nonneg p := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun q hq => by simp [Finsupp.single_apply]; positivity)
  total := by
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_ne_zero.mpr s.nonempty))
  chain := by
    have hs : (∑ p ∈ s.finset, Finsupp.single p (s.finset.card : ℝ)⁻¹).support ⊆ s.finset := by
      intro p hp
      by_contra h
      apply Finsupp.mem_support_iff.mp hp
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      exact Finsupp.single_eq_of_ne (fun he => h (he ▸ hq))
    intro p hp q hq hpq
    exact s.comparable ⟨p,hs hp⟩ ⟨q,hs hq⟩

lemma barycenter_apply (s : NonemptyFiniteChains P) (p : P) :
    (barycenter s).weights p = if p ∈ s.finset then (s.finset.card : ℝ)⁻¹ else 0 := by
  classical
  simp [barycenter, Finsupp.finsetSum_apply, Finsupp.single_apply]

def barycentricLinear : (NonemptyFiniteChains P →₀ ℝ) →ₗ[ℝ] (P →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun s => (barycenter s).weights)

lemma barycentricLinear_apply (g : NonemptyFiniteChains P →₀ ℝ) (p : P) :
    barycentricLinear g p =
      g.sum (fun s r => r * (barycenter s).weights p) := by
  simp [barycentricLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply]

lemma barycentricLinear_total (g : NonemptyFiniteChains P →₀ ℝ) :
    (barycentricLinear g).sum (fun _ r => r) = g.sum (fun _ r => r) := by
  rw [barycentricLinear, Finsupp.linearCombination_apply,
    Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  apply Finsupp.sum_congr
  intro s hs
  rw [Finsupp.sum_smul_index (fun _ => rfl)]
  change (barycenter s).weights.sum (fun _ r => g s * r) = g s
  rw [Finsupp.sum, ← Finset.mul_sum]
  simpa only [Finsupp.sum, mul_one] using
    congrArg (fun r : ℝ => g s * r) (barycenter s).total

lemma barycentric_cone_step (f : P →₀ ℝ) (hn : ∀ p, 0 ≤ f p)
    (hc : IsChain (· ≤ ·) (f.support : Set P)) (hf : f ≠ 0) :
    ∃ (s : NonemptyFiniteChains P) (c : ℝ) (h : P →₀ ℝ),
      s.finset = f.support ∧ 0 < c ∧ (∀ p, 0 ≤ h p) ∧
      h.support ⊂ f.support ∧ f = h + c • (barycenter s).weights := by
  classical
  have hne : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image f.support f hne
  let s : NonemptyFiniteChains P :=
    ⟨f.support, hne, fun p q => hc.total p.property q.property⟩
  let c : ℝ := f p * (f.support.card : ℝ)
  let h : P →₀ ℝ := f - c • (barycenter s).weights
  have hcard : (f.support.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  have hpos : 0 < f p := lt_of_le_of_ne (hn p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  have hcpos : 0 < c := mul_pos hpos (by exact_mod_cast Finset.card_pos.mpr hne)
  have heval (q : P) : h q = if q ∈ f.support then f q - f p else 0 := by
    simp only [h, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, barycenter_apply]
    change f q - c * (if q ∈ f.support then (f.support.card : ℝ)⁻¹ else 0) = _
    split_ifs with hq
    · dsimp [c]
      rw [mul_assoc, mul_inv_cancel₀ hcard, mul_one]
    · rw [Finsupp.notMem_support_iff.mp hq]
      simp
  have hsub : h.support ⊆ f.support.erase p := by
    intro q hq
    rw [Finsupp.mem_support_iff, heval] at hq
    by_cases hqs : q ∈ f.support
    · refine Finset.mem_erase.mpr ⟨?_, hqs⟩
      intro he
      subst q
      simp [hp] at hq
    · simp [hqs] at hq
  refine ⟨s,c,h,rfl,hcpos,?_,?_,?_⟩
  · intro q
    rw [heval]
    split_ifs with hq
    · exact sub_nonneg.mpr (hmin q hq)
    · exact le_rfl
  · exact Finset.ssubset_of_subset_of_ssubset hsub (Finset.erase_ssubset hp)
  · dsimp [h]
    abel

lemma exists_barycentric_decomposition (f : P →₀ ℝ) (hn : ∀ p, 0 ≤ f p)
    (hc : IsChain (· ≤ ·) (f.support : Set P)) :
    ∃ g : NonemptyFiniteChains P →₀ ℝ,
      (∀ s, 0 ≤ g s) ∧ IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) ∧
      (∀ s ∈ g.support, s.finset ⊆ f.support) ∧ barycentricLinear g = f := by
  classical
  suffices ∀ (S : Finset P) (f : P →₀ ℝ), f.support = S →
      (∀ p, 0 ≤ f p) → IsChain (· ≤ ·) (f.support : Set P) →
      ∃ g : NonemptyFiniteChains P →₀ ℝ,
        (∀ s, 0 ≤ g s) ∧ IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) ∧
        (∀ s ∈ g.support, s.finset ⊆ f.support) ∧ barycentricLinear g = f by
    exact this _ f rfl hn hc
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro f hS hn hc
    by_cases hf : f = 0
    · subst f
      refine ⟨0, by simp, ?_, by simp, by simp⟩
      simp
    obtain ⟨s,c,h,hs,hcpos,hnn,hsub,heq⟩ := barycentric_cone_step f hn hc hf
    obtain ⟨g,hgn,hgc,hgs,hge⟩ := ih h.support (hS ▸ hsub) h rfl hnn
      (hc.mono (by simpa using hsub.subset))
    let g' : NonemptyFiniteChains P →₀ ℝ := g + Finsupp.single s c
    have hmem (t : NonemptyFiniteChains P) (ht : t ∈ g'.support) :
        t ∈ g.support ∨ t = s := by
      have hm := Finsupp.support_add ht
      rcases Finset.mem_union.mp hm with ht0 | ht0
      · exact Or.inl ht0
      · right
        by_contra htne
        exact (Finsupp.mem_support_iff.mp ht0) (Finsupp.single_eq_of_ne htne)
    have hle (t : NonemptyFiniteChains P) (ht : t ∈ g.support) : t ≤ s := by
      change t.finset ⊆ s.finset
      rw [hs]
      exact (hgs t ht).trans hsub.subset
    refine ⟨g', ?_, ?_, ?_, ?_⟩
    · intro t
      dsimp [g']
      exact add_nonneg (hgn t) (by simp [Finsupp.single_apply]; positivity)
    · intro a ha b hb hab
      rcases hmem a ha with ha0 | ha0
      · rcases hmem b hb with hb0 | hb0
        · exact hgc ha0 hb0 hab
        · exact Or.inl (hb0.symm ▸ hle a ha0)
      · rcases hmem b hb with hb0 | hb0
        · exact Or.inr (ha0.symm ▸ hle b hb0)
        · exact (hab (ha0.trans hb0.symm)).elim
    · intro t ht
      rcases hmem t ht with ht | rfl
      · exact (hgs t ht).trans hsub.subset
      · exact hs ▸ Finset.Subset.refl _
    · dsimp [g']
      rw [map_add, hge]
      rw [barycentricLinear, Finsupp.linearCombination_single]
      exact heq.symm

lemma barycentricLinear_nonneg (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) (p : P) : 0 ≤ barycentricLinear g p := by
  rw [barycentricLinear_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun s hs => mul_nonneg (hg s) ((barycenter s).nonneg p))

lemma barycentricLinear_support (g : NonemptyFiniteChains P →₀ ℝ) :
    (barycentricLinear g).support ⊆ g.support.biUnion NonemptyFiniteChains.finset := by
  classical
  intro p hp
  by_contra hnot
  apply Finsupp.mem_support_iff.mp hp
  rw [barycentricLinear_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hpnot : p ∉ s.finset := fun h => hnot (Finset.mem_biUnion.mpr ⟨s,hs,h⟩)
  simp [barycenter_apply, hpnot]

lemma flagCarrier_chain (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P))) :
    IsChain (· ≤ ·) ((S.biUnion NonemptyFiniteChains.finset : Finset P) : Set P) := by
  classical
  intro p hp q hq hpq
  obtain ⟨s,hs,hps⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨t,ht,hqt⟩ := Finset.mem_biUnion.mp hq
  rcases hc.total hs ht with hst | hts
  · exact t.comparable ⟨p,hst hps⟩ ⟨q,hqt⟩
  · exact s.comparable ⟨p,hps⟩ ⟨q,hts hqt⟩

def subdivide (x : PolyPoint (NonemptyFiniteChains P)) : PolyPoint P where
  weights := barycentricLinear x.weights
  nonneg := barycentricLinear_nonneg x.weights x.nonneg
  total := (barycentricLinear_total x.weights).trans x.total
  chain := (flagCarrier_chain x.weights.support x.chain).mono
    (fun _ hp => barycentricLinear_support x.weights hp)

lemma subdivide_surjective : Function.Surjective (@subdivide P _) := by
  intro x
  obtain ⟨g,hn,hc,hs,hg⟩ := exists_barycentric_decomposition x.weights x.nonneg x.chain
  have ht : g.sum (fun _ r => r) = 1 := by
    rw [← barycentricLinear_total, hg]
    exact x.total
  exact ⟨⟨g,hn,ht,hc⟩, PolyPoint.ext hg⟩

lemma continuous_subdivide : Continuous (@subdivide P _) := by
  classical
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  let t : ChainIndex P :=
    ⟨s.carrier.biUnion NonemptyFiniteChains.finset, flagCarrier_chain s.carrier s.chain, by
      obtain ⟨a,ha⟩ := s.nonempty
      obtain ⟨p,hp⟩ := a.nonempty
      exact ⟨p, Finset.mem_biUnion.mpr ⟨a,ha,hp⟩⟩⟩
  let f : Face s.carrier → Face t.carrier := fun x => ⟨subdivide x.val, by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp (barycentricLinear_support x.val.weights hp)
    exact Finset.mem_biUnion.mpr ⟨a,x.property ha,hpa⟩⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro p
    have he (x : Face s.carrier) :
        (f x).val.weights p = ∑ a ∈ s.carrier, x.val.weights a * (barycenter a).weights p := by
      change barycentricLinear x.val.weights p = _
      rw [barycentricLinear_apply]
      exact Finsupp.sum_of_support_subset _ x.property _ (by simp)
    have hc : Continuous (fun x : Face s.carrier =>
        ∑ a ∈ s.carrier, x.val.weights a * (barycenter a).weights p) := by
      apply continuous_finsetSum
      intro a ha
      have hca : Continuous (fun x : Face s.carrier => x.val.weights a) :=
        (continuous_apply a).comp continuous_induced_dom
      exact hca.mul continuous_const
    exact hc.congr (fun x => (he x).symm)
  exact (continuous_chainFace_val t).comp hf

end PolyPoint
end Thomason.GeometricRecognition

end

end OAI
