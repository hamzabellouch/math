import Mathlib
import OAI.CategoryTheory.Thomason.FilteredColimits

namespace OAI

/-! Globes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

def globePresentation (n : ℕ) : Presentation.{u} where
  Generator := PUnit.{u+1}
  dimension _ := n
  relations _ _ := True

noncomputable def globe (n : ℕ) : OmegaCategory.{u} := (globePresentation n).category

def globeGenerator (n : ℕ) : (globe.{u} n).Cell :=
  (globePresentation n).generator PUnit.unit

lemma globeGenerator_bounded (n : ℕ) :
    (globe.{u} n).source n (globeGenerator n) = globeGenerator n :=
  (globePresentation n).generator_bounded PUnit.unit

noncomputable def globeLift (n : ℕ) {C : OmegaCategory.{u}} (x : C.Cell)
    (hx : C.source n x = x) : Functor (globe.{u} n) C :=
  (globePresentation n).lift C ⟨fun _ => x, fun _ => hx, trivial⟩

@[simp] lemma globeLift_generator (n : ℕ) {C : OmegaCategory.{u}} (x : C.Cell)
    (hx : C.source n x = x) : (globeLift n x hx).map (globeGenerator n) = x := rfl

lemma globe_functor_ext {n : ℕ} {C : OmegaCategory.{u}} {F G : Functor (globe.{u} n) C}
    (h : F.map (globeGenerator n) = G.map (globeGenerator n)) : F = G := by
  apply (globePresentation n).functor_ext
  intro g
  cases g
  exact h

lemma globe_map_bounded {n : ℕ} {C : OmegaCategory.{u}} (F : Functor (globe.{u} n) C) :
    C.source n (F.map (globeGenerator n)) = F.map (globeGenerator n) := by
  rw [← F.map_source, globeGenerator_bounded]

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

lemma globe_functor_lift (n : ℕ) (G : Functor (globe.{u} n) (omega F)) :
    ∃ (i : J) (H : Functor (globe.{u} n) (F.obj i)),
      Functor.comp H ((cocone F).ι.app i) = G := by
  obtain ⟨i, x, hx⟩ := exists_rep F (G.map (globeGenerator n))
  have hb : ι F i ((F.obj i).source n x) = ι F i x := by
    rw [← source_ι, hx]
    exact globe_map_bounded G
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (CellDiagram F)) _ _).mp hb
  have hy : (F.obj j).source n ((F.map f).map x) = (F.map f).map x := by
    rw [← (F.map f).map_source]
    exact hf
  refine ⟨j, globeLift n _ hy, ?_⟩
  apply globe_functor_ext
  change ι F j ((F.map f).map x) = G.map (globeGenerator n)
  rw [ι_map, hx]

lemma globe_functor_equality (n : ℕ) {i : J} (G H : Functor (globe.{u} n) (F.obj i))
    (h : Functor.comp G ((cocone F).ι.app i) = Functor.comp H ((cocone F).ι.app i)) :
    ∃ (j : J) (f : i ⟶ j), Functor.comp G (F.map f) = Functor.comp H (F.map f) := by
  have he : ι F i (G.map (globeGenerator n)) = ι F i (H.map (globeGenerator n)) :=
    congrArg (fun G : Functor (globe.{u} n) (omega F) => G.map (globeGenerator n)) h
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (CellDiagram F)) _ _).mp he
  exact ⟨j, f, globe_functor_ext hf⟩

noncomputable def globeHomIsColimit (n : ℕ) :
    IsColimit ((coyoneda.obj (Opposite.op (globe.{u} n))).mapCocone (cocone F)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    obtain ⟨i, H, h⟩ := globe_functor_lift F n G
    exact ⟨i, H, h.symm⟩
  · intro i G H h
    exact globe_functor_equality F n G H h

instance globeHomPreservesColimit (n : ℕ) :
    PreservesColimit F (coyoneda.obj (Opposite.op (globe.{u} n))) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (globeHomIsColimit F n)

end FilteredColimit

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance globe_finitelyPresentable (n : ℕ) :
    IsCardinalPresentable (globe.{u} n) Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
    exact ⟨fun {F} => inferInstance⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

noncomputable def isoOfBijective {C D : OmegaCategory.{u}} (F : C ⟶ D)
    (h : Function.Bijective F.map) : C ≅ D := by
  let e := Equiv.ofBijective F.map h
  let G : Functor D C :=
    { map := e.symm
      map_source k x := by
        apply e.injective
        change e (e.symm (D.source k x)) = F.map (C.source k (e.symm x))
        rw [e.apply_symm_apply, F.map_source]
        exact congrArg (D.source k) (e.apply_symm_apply x).symm
      map_target k x := by
        apply e.injective
        change e (e.symm (D.target k x)) = F.map (C.target k (e.symm x))
        rw [e.apply_symm_apply, F.map_target]
        exact congrArg (D.target k) (e.apply_symm_apply x).symm
      map_comp k x y hxy h' := by
        apply e.injective
        change e (e.symm (D.comp k x y hxy)) = F.map (C.comp k _ _ h')
        rw [e.apply_symm_apply, F.map_comp k _ _ h' (F.map_composable h')]
        have hx : F.map (e.symm x) = x := e.apply_symm_apply x
        have hy : F.map (e.symm y) = y := e.apply_symm_apply y
        congr 1
        · exact hx.symm
        · exact hy.symm }
  exact
    { hom := F
      inv := G
      hom_inv_id := Functor.ext (funext fun x => e.symm_apply_apply x)
      inv_hom_id := Functor.ext (funext fun x => e.apply_symm_apply x) }

lemma injective_of_mono {C D : OmegaCategory.{u}} (F : C ⟶ D) [Mono F] :
    Function.Injective F.map := by
  intro x y hxy
  obtain ⟨p, hp⟩ := C.finite_dimension x
  obtain ⟨q, hq⟩ := C.finite_dimension y
  let n := max p q
  let G := globeLift n x (C.source_fixed_upwards (le_max_left p q) hp)
  let H := globeLift n y (C.source_fixed_upwards (le_max_right p q) hq)
  have h : G ≫ F = H ≫ F := globe_functor_ext hxy
  have he : G = H := (cancel_mono F).mp h
  exact congrArg (fun G : Functor (globe.{u} n) C => G.map (globeGenerator n)) he

lemma globes_separating : (ObjectProperty.ofObj (globe.{u})).IsSeparating := by
  intro C D F G h
  apply Functor.ext
  funext x
  obtain ⟨n, hn⟩ := C.finite_dimension x
  exact congrArg (fun H : Functor (globe.{u} n) D => H.map (globeGenerator n))
    (h (globe.{u} n) ⟨n⟩ (globeLift n x hn))

lemma globes_strongGenerator : (ObjectProperty.ofObj (globe.{u})).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨globes_separating, ?_⟩
  intro C D F _ h
  have hs : Function.Surjective F.map := by
    intro y
    obtain ⟨n, hn⟩ := D.finite_dimension y
    obtain ⟨G, hG⟩ := h (globe.{u} n) ⟨n⟩ (globeLift n y hn)
    exact ⟨G.map (globeGenerator n),
      congrArg (fun H : Functor (globe.{u} n) D => H.map (globeGenerator n)) hG⟩
  exact (isoOfBijective F ⟨injective_of_mono F, hs⟩).isIso_hom

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance locallyFinitelyPresentable :
    IsCardinalLocallyPresentable OmegaCategory.{u} Cardinal.aleph0.{u} := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨ObjectProperty.ofObj globe, inferInstance, globes_strongGenerator, ?_⟩
  rintro C ⟨n⟩
  exact globe_finitelyPresentable n

instance locallyPresentable : IsLocallyPresentable.{u} OmegaCategory.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J]

lemma omega_truncated (n : ℕ) (F : J ⥤ NCategory.{u} n) :
    (omega (F ⋙ nCategoryInclusion n)).IsTruncated n := by
  intro x
  obtain ⟨j, y, rfl⟩ := exists_rep (F ⋙ nCategoryInclusion n) x
  change source (F ⋙ nCategoryInclusion n) n (ι (F ⋙ nCategoryInclusion n) j y) = _
  rw [source_ι]
  exact congrArg (ι (F ⋙ nCategoryInclusion n) j) ((F.obj j).property y)

noncomputable def nCocone (n : ℕ) (F : J ⥤ NCategory.{u} n) : Cocone F where
  pt := ⟨omega (F ⋙ nCategoryInclusion n), omega_truncated n F⟩
  ι := {
    app := fun j => (cocone (F ⋙ nCategoryInclusion n)).ι.app j
    naturality := fun _ _ f => (cocone (F ⋙ nCategoryInclusion n)).ι.naturality f }

noncomputable def nIsColimit (n : ℕ) (F : J ⥤ NCategory.{u} n) : IsColimit (nCocone n F) where
  desc s := desc (F ⋙ nCategoryInclusion n) ((nCategoryInclusion n).mapCocone s)
  fac s j := (isColimit (F ⋙ nCategoryInclusion n)).fac ((nCategoryInclusion n).mapCocone s) j
  uniq s m h :=
    (isColimit (F ⋙ nCategoryInclusion n)).uniq ((nCategoryInclusion n).mapCocone s) m h

instance nInclusion_preservesFilteredColimit (n : ℕ) (F : J ⥤ NCategory.{u} n) :
    PreservesColimit F (nCategoryInclusion n) :=
  preservesColimit_of_preserves_colimit_cocone (nIsColimit n F)
    (isColimit (F ⋙ nCategoryInclusion n))

end FilteredColimit

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance nInclusion_finitelyAccessible (n : ℕ) :
    (nCategoryInclusion.{u} n).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
    exact ⟨fun {F} => inferInstance⟩

instance nCategory_locallyFinitelyPresentable (n : ℕ) :
    IsCardinalLocallyPresentable (NCategory.{u} n) Cardinal.aleph0.{u} :=
  (truncationAdjunction n).isCardinalLocallyPresentable Cardinal.aleph0.{u}

instance nCategory_locallyPresentable (n : ℕ) : IsLocallyPresentable.{u} (NCategory.{u} n) where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.SmallObject

open CategoryTheory Limits Opposite

lemma commonPresentabilityCardinal {C : Type v} [Category.{u} C]
    {ι : Type u} (X : ι → C) [∀ i, IsPresentable.{u} (X i)] :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), ∀ i, IsCardinalPresentable (X i) κ := by
  classical
  choose κ hκ hp using fun i =>
    CategoryTheory.Functor.IsAccessible.exists_cardinal (F := coyoneda.obj (Opposite.op (X i)))
  obtain ⟨k, hk, hb⟩ := HasCardinalLT.exists_regular_cardinal_forall.{u}
    (fun i => (κ i).out)
  let : Fact k.IsRegular := ⟨hk⟩
  refine ⟨k, inferInstance, fun i => ?_⟩
  let := hκ i
  let := hp i
  have hi : κ i < k := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_out] using hb i
  exact isCardinalPresentable_of_le (X i) hi.le

lemma smallObjectArgument {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{u} I] :
    MorphismProperty.HasSmallObjectArgument.{u} I := by
  obtain ⟨ι, A, B, f, rfl⟩ := (MorphismProperty.isSmall_iff_eq_ofHoms.{u} I).mp inferInstance
  obtain ⟨κ, hκ, hp⟩ := commonPresentabilityCardinal A
  let := hκ
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero hκ.out
  let := WellFoundedLT.toOrderBot κ.ord.ToType
  let : MorphismProperty.IsCardinalForSmallObjectArgument (MorphismProperty.ofHoms f) κ := {
    preservesColimit := by
      intro X Y Z W i hi p hf
      obtain ⟨j⟩ := hi
      let := hp j
      have := preservesColimitsOfShape_of_isCardinalPresentable (A j) κ κ.ord.ToType
      infer_instance }
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

lemma weakFactorizationSystem {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{u} I] :
    MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp := by
  let := smallObjectArgument I
  exact { rlp := MorphismProperty.rlp_llp_rlp I, llp := rfl }

end Thomason.SmallObject

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance boundaryImages_small {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsSmall.{u} (boundaryImages L) := by
  unfold boundaryImages
  exact MorphismProperty.isSmall_ofHoms _

instance hornImages_small {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsSmall.{u} (hornImages L) := by
  unfold hornImages
  let : ∀ n : ℕ, MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms (fun i : Fin (n+2) => L.map (SSet.horn (n+1) i).ι)) :=
    fun _ => MorphismProperty.isSmall_ofHoms _
  exact MorphismProperty.isSmall_iSup _

lemma hornImages_rlp {C : Type v} [Category.{u} C] {L : SSet.{u} ⥤ C}
    {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (hornImages L).rlp = simplicialFibrations.inverseImage R := by
  ext X Y f
  constructor
  · intro h A B i hi
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    apply (adj.hasLiftingProperty_iff _ f).mp
    apply h
    simp only [hornImages, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨j⟩⟩
  · intro h A B i hi
    simp only [hornImages, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    apply (adj.hasLiftingProperty_iff _ f).mpr
    apply h
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨j⟩⟩

lemma boundaryImages_rlp {C : Type v} [Category.{u} C] {L : SSet.{u} ⥤ C}
    {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (boundaryImages L).rlp = SSet.modelCategoryQuillen.I.rlp.inverseImage R := by
  ext X Y f
  constructor
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ f).mp (h _ ⟨n⟩)
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ f).mpr (h _ ⟨n⟩)

instance boundaryImages_smallObject {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.HasSmallObjectArgument.{u} (boundaryImages L) :=
  SmallObject.smallObjectArgument (boundaryImages L)

instance hornImages_smallObject {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.HasSmallObjectArgument.{u} (hornImages L) :=
  SmallObject.smallObjectArgument (hornImages L)

lemma boundaryImages_weakFactorization {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsWeakFactorizationSystem (boundaryImages L).rlp.llp
      (boundaryImages L).rlp := SmallObject.weakFactorizationSystem _

lemma hornImages_weakFactorization {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsWeakFactorizationSystem (hornImages L).rlp.llp
      (hornImages L).rlp := SmallObject.weakFactorizationSystem _

lemma thomasonFibrations_weakFactorization :
    MorphismProperty.IsWeakFactorizationSystem thomasonFibrations.{u}.llp thomasonFibrations := by
  have := hornImages_weakFactorization thomasonLeft.{u}
  rwa [hornImages_rlp thomasonAdjunction] at this

lemma thomasonFibrationsFinite_weakFactorization (n : ℕ) :
    MorphismProperty.IsWeakFactorizationSystem (thomasonFibrationsFinite.{u} n).llp
      (thomasonFibrationsFinite n) := by
  have := hornImages_weakFactorization (thomasonLeftFinite.{u} n)
  rwa [hornImages_rlp (thomasonFiniteAdjunction n)] at this

lemma thomasonBoundary_weakFactorization :
    MorphismProperty.IsWeakFactorizationSystem (boundaryImages thomasonLeft.{u}).rlp.llp
      (boundaryImages thomasonLeft).rlp := boundaryImages_weakFactorization _

lemma thomasonBoundaryFinite_weakFactorization (n : ℕ) :
    MorphismProperty.IsWeakFactorizationSystem (boundaryImages (thomasonLeftFinite.{u} n)).rlp.llp
      (boundaryImages (thomasonLeftFinite n)).rlp := boundaryImages_weakFactorization _

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology

variable {N : Type u} [Fintype N] [Nonempty N]

noncomputable def radius (x : I^N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |2 * (x i : ℝ) - 1|)

lemma abs_le_radius (x : I^N) (i : N) : |2 * (x i : ℝ) - 1| ≤ radius x :=
  Finset.le_sup' (fun j => |2 * (x j : ℝ) - 1|) (Finset.mem_univ i)

lemma radius_nonneg (x : I^N) : 0 ≤ radius x :=
  (abs_nonneg _).trans (abs_le_radius x (Classical.choice ‹Nonempty N›))

lemma radius_le_one (x : I^N) : radius x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  rw [abs_le]
  constructor <;> nlinarith [(x i).property.1, (x i).property.2]

lemma continuous_radius : Continuous (radius (N := N)) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ =>
    ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
      continuous_const).abs)

lemma radius_eq_one_iff (x : I^N) : radius x = 1 ↔ x ∈ Cube.boundary N := by
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => |2 * (x i : ℝ) - 1|)
    have he : |2 * (x i : ℝ) - 1| = 1 := hi.symm.trans hx
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he with he | he
    · exact ⟨i, Or.inr (Subtype.ext (by dsimp; linarith))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by dsimp; linarith))⟩
  · rintro ⟨i, hi | hi⟩ <;> apply le_antisymm (radius_le_one x)
    · simpa [hi] using (abs_le_radius x i)
    · have hh := abs_le_radius x i
      rw [hi] at hh
      norm_num at hh
      exact hh

noncomputable def denominator (q : I × I^N) : ℝ := max (1 - (q.1 : ℝ) / 2) (radius q.2)

lemma half_le_denominator (q : I × I^N) : (1 : ℝ)/2 ≤ denominator q := by
  have := q.1.property.2
  exact (by linarith : (1:ℝ)/2 ≤ 1 - (q.1:ℝ)/2).trans (le_max_left _ _)

lemma denominator_pos (q : I × I^N) : 0 < denominator q :=
  lt_of_lt_of_le (by norm_num) (half_le_denominator q)

lemma denominator_le_one (q : I × I^N) : denominator q ≤ 1 := by
  exact max_le (by linarith [q.1.property.1]) (radius_le_one q.2)

lemma continuous_denominator : Continuous (denominator (N := N)) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_radius.comp continuous_snd)

noncomputable def retractTime (q : I × I^N) : I :=
  ⟨2 + ((q.1 : ℝ) - 2) / denominator q, by
    have hd := denominator_pos q
    have hl : 1 - (q.1:ℝ)/2 ≤ denominator q := le_max_left _ _
    have hu := denominator_le_one q
    constructor
    · have : (-2 : ℝ) ≤ ((q.1:ℝ) - 2) / denominator q :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have : ((q.1:ℝ) - 2) / denominator q ≤ -1 :=
        (div_le_iff₀ hd).mpr (by linarith [q.1.property.2])
      linarith⟩

noncomputable def retractSpace (q : I × I^N) : I^N := fun i =>
  ⟨1/2 + ((q.2 i : ℝ) - 1/2) / denominator q, by
    have hd := denominator_pos q
    have hr := abs_le.mp (abs_le_radius q.2 i)
    have hl : radius q.2 ≤ denominator q := le_max_right _ _
    constructor
    · have : (-1/2 : ℝ) ≤ ((q.2 i:ℝ) - 1/2) / denominator q :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have : ((q.2 i:ℝ) - 1/2) / denominator q ≤ (1/2 : ℝ) :=
        (div_le_iff₀ hd).mpr (by linarith)
      linarith⟩

lemma continuous_retractTime : Continuous (retractTime (N := N)) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp continuous_fst).sub
    continuous_const).div continuous_denominator (fun q => ne_of_gt (denominator_pos q)))

lemma continuous_retractSpace : Continuous (retractSpace (N := N)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact continuous_const.add ((((continuous_subtype_val.comp (continuous_apply i)).comp
    continuous_snd).sub continuous_const).div continuous_denominator
      (fun q => ne_of_gt (denominator_pos q)))

def roof : Set (I × I^N) := {q | q.1 = 0 ∨ q.2 ∈ Cube.boundary N}

lemma retract_mem_roof (q : I × I^N) :
    (retractTime q, retractSpace q) ∈ roof := by
  rcases le_total (radius q.2) (1 - (q.1:ℝ)/2) with h | h
  · left
    apply Subtype.ext
    change 2 + ((q.1:ℝ)-2) / denominator q = 0
    have he : denominator q = 1 - (q.1:ℝ)/2 := max_eq_left h
    have hd := denominator_pos q
    have hh : ((q.1:ℝ)-2) / denominator q = (-2 : ℝ) :=
      (div_eq_iff (ne_of_gt hd)).mpr (by rw [he]; ring)
    rw [hh]
    norm_num
  · right
    have hd := denominator_pos q
    have he : denominator q = radius q.2 := max_eq_right h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => |2 * (q.2 i : ℝ) - 1|)
    have habs : |2 * (q.2 i : ℝ) - 1| = denominator q := hi.symm.trans he.symm
    rcases (abs_eq (le_of_lt hd)).mp habs with hi | hi
    · refine ⟨i, Or.inr (Subtype.ext ?_)⟩
      change 1/2 + ((q.2 i:ℝ)-1/2) / denominator q = 1
      have : ((q.2 i:ℝ)-1/2) / denominator q = (1/2:ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]
      norm_num
    · refine ⟨i, Or.inl (Subtype.ext ?_)⟩
      change 1/2 + ((q.2 i:ℝ)-1/2) / denominator q = 0
      have : ((q.2 i:ℝ)-1/2) / denominator q = (-1/2:ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]
      norm_num

noncomputable def retract : C(I × I^N, roof (N := N)) :=
  ⟨fun q => ⟨(retractTime q, retractSpace q), retract_mem_roof q⟩,
    (continuous_retractTime.prodMk continuous_retractSpace).subtype_mk _⟩

lemma denominator_eq_one_of_roof {q : I × I^N} (hq : q ∈ roof) : denominator q = 1 := by
  rcases hq with h | h
  · change max (1 - (q.1 : ℝ)/2) (radius q.2) = 1
    rw [h]
    norm_num
    exact radius_le_one q.2
  · rw [denominator, (radius_eq_one_iff _).mpr h]
    exact max_eq_right (by linarith [q.1.property.1])

lemma retract_fixed (q : roof (N := N)) : (retract q.val).val = q.val := by
  have hd := denominator_eq_one_of_roof q.property
  apply Prod.ext
  · apply Subtype.ext
    change 2 + ((q.val.1:ℝ)-2) / denominator q.val = (q.val.1:ℝ)
    rw [hd, div_one]
    ring
  · funext i
    apply Subtype.ext
    change 1/2 + ((q.val.2 i:ℝ)-1/2) / denominator q.val = (q.val.2 i:ℝ)
    rw [hd, div_one]
    ring

end Thomason.CubeExtension

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology

variable {N : Type u} [Fintype N] [Nonempty N]
variable {P : Type v} {X : Type w} [TopologicalSpace P] [TopologicalSpace X]

noncomputable def closedPaste {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) : C(D, X) := by
  classical
  refine ⟨s.piecewise f g, ?_⟩
  rw [← continuousOn_univ, ← hu]
  apply ContinuousOn.union_of_isClosed _ _ hs ht
  · apply f.continuous.continuousOn.congr
    intro x hx
    exact Set.piecewise_eq_of_mem s f g hx
  · apply g.continuous.continuousOn.congr
    intro x hx
    by_cases hxs : x ∈ s
    · rw [Set.piecewise_eq_of_mem s f g hxs]
      exact hfg x ⟨hxs, hx⟩
    · exact Set.piecewise_eq_of_notMem s f g hxs

lemma closedPaste_left {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) (x : D) (hx : x ∈ s) :
    closedPaste s t hs ht hu f g hfg x = f x := by
  classical
  exact Set.piecewise_eq_of_mem s f g hx

lemma closedPaste_right {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) (x : D) (hx : x ∈ t) :
    closedPaste s t hs ht hu f g hfg x = g x := by
  classical
  by_cases hxs : x ∈ s
  · rw [closedPaste_left _ _ _ _ _ _ _ _ _ hxs]
    exact hfg x ⟨hxs, hx⟩
  · exact Set.piecewise_eq_of_notMem s f g hxs

noncomputable def glue (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) :
    C(P × roof (N := N), X) :=
  closedPaste {q | q.2.val.1 = 0} {q | radius q.2.val.2 = 1}
    (isClosed_eq (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const)
    (isClosed_eq (continuous_radius.comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))) continuous_const)
    (by
      apply Set.eq_univ_of_forall
      intro q
      rcases q.2.property with hq | hq
      · exact Or.inl hq
      · exact Or.inr ((radius_eq_one_iff _).mpr hq))
    ⟨fun q => p (q.1,q.2.val.2), p.continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))⟩
    ⟨fun q => γ (q.1,q.2.val.1), γ.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))⟩
    (fun q hq => by
      dsimp at hq ⊢
      rw [hq.1]
      exact h _ _ ((radius_eq_one_iff _).mp hq.2))

lemma glue_bottom (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) (z : P) (x : I^N) :
    glue p γ h (z, ⟨(0,x), Or.inl rfl⟩) = p (z,x) :=
  closedPaste_left _ _ _ _ _ _ _ _ _ rfl

lemma glue_side (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (z : P) (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) :
    glue p γ h (z, ⟨(t,x), Or.inr hx⟩) = γ (z,t) :=
  closedPaste_right _ _ _ _ _ _ _ _ _ ((radius_eq_one_iff _).mpr hx)

noncomputable def extend (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) :
    C(P × (I × I^N), X) :=
  (glue p γ h).comp ⟨fun q => (q.1, retract q.2),
    continuous_fst.prodMk (retract.continuous.comp continuous_snd)⟩

lemma extend_bottom (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) (z : P) (x : I^N) :
    extend p γ h (z, (0,x)) = p (z,x) := by
  change glue p γ h (z, retract (0,x)) = _
  have he : retract (0,x) = ⟨(0,x), Or.inl rfl⟩ :=
    Subtype.ext (retract_fixed ⟨(0,x), Or.inl rfl⟩)
  rw [he, glue_bottom]

lemma extend_side (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (z : P) (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) :
    extend p γ h (z,(t,x)) = γ (z,t) := by
  change glue p γ h (z, retract (t,x)) = _
  have he : retract (t,x) = ⟨(t,x), Or.inr hx⟩ :=
    Subtype.ext (retract_fixed ⟨(t,x), Or.inr hx⟩)
  rw [he]
  exact glue_side p γ h z t x hx

lemma extend_natural {Y : Type*} [TopologicalSpace Y]
    (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (f : C(X,Y)) (q : P × (I × I^N)) :
    extend (f.comp p) (f.comp γ) (fun z x hx => congrArg f (h z x hx)) q =
      f (extend p γ h q) := by
  classical
  dsimp [extend, glue, closedPaste, Set.piecewise]
  split <;> rfl

noncomputable def interpolate : C(I × (I × I^N), I × I^N) :=
  ⟨fun q => (Set.Icc.convexComb (retract q.2).val.1 q.2.1 q.1,
      fun i => Set.Icc.convexComb ((retract q.2).val.2 i) (q.2.2 i) q.1), by
    have hr : Continuous (fun q : I × (I × I^N) => (retract q.2).val) :=
      continuous_subtype_val.comp (retract.continuous.comp continuous_snd)
    apply Continuous.prodMk
    · exact Set.Icc.continuous_convexComb_prod.comp
        ((continuous_fst.comp hr).prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_fst))
    · apply continuous_pi
      intro i
      exact Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (continuous_snd.comp hr)).prodMk
          (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).prodMk continuous_fst))⟩

lemma interpolate_zero (q : I × I^N) : interpolate (0,q) = (retract q).val := by
  apply Prod.ext
  · exact Set.Icc.convexComb_zero _ _
  · funext i
    exact Set.Icc.convexComb_zero _ _

lemma interpolate_one (q : I × I^N) : interpolate (1,q) = q := by
  apply Prod.ext
  · exact Set.Icc.convexComb_one _ _
  · funext i
    exact Set.Icc.convexComb_one _ _

lemma interpolate_fixed (s : I) (q : roof (N := N)) : interpolate (s,q.val) = q.val := by
  change (Set.Icc.convexComb (retract q.val).val.1 q.val.1 s,
    fun i => Set.Icc.convexComb ((retract q.val).val.2 i) (q.val.2 i) s) = q.val
  rw [retract_fixed]
  simp only [Set.Icc.convexComb_eq]

end Thomason.CubeExtension

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology Topology.Homotopy

variable {N : Type u} [Fintype N] [Nonempty N]
variable {P : Type v} {X : Type w} [TopologicalSpace P] [TopologicalSpace X]

lemma extend_congr_at {Q : Type*} [TopologicalSpace Q]
    (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (p' : C(Q × I^N, X)) (γ' : C(Q × I, X))
    (h' : ∀ z x, x ∈ Cube.boundary N → p' (z,x) = γ' (z,0))
    (z : P) (z' : Q) (hp : ∀ x, p (z,x) = p' (z',x))
    (hγ : ∀ t, γ (z,t) = γ' (z',t)) (q : I × I^N) :
    extend p γ h (z,q) = extend p' γ' h' (z',q) := by
  classical
  dsimp [extend, glue, closedPaste, Set.piecewise]
  split
  · exact hp _
  · exact hγ _

lemma extend_eq_of_restrictions (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (H : C(P × (I × I^N), X))
    (h0 : ∀ z x, H (z,(0,x)) = p (z,x))
    (hb : ∀ z t x, x ∈ Cube.boundary N → H (z,(t,x)) = γ (z,t))
    (q : P × (I × I^N)) :
    extend p γ h q = H (q.1,(retract q.2).val) := by
  classical
  let r := retract q.2
  change glue p γ h (q.1,r) = H (q.1,r.val)
  by_cases hrt : r.val.1 = 0
  · obtain ⟨⟨t,x⟩, hr⟩ := r
    dsimp at hrt
    subst t
    rw [glue_bottom]
    exact (h0 _ _).symm
  · have hrb : r.val.2 ∈ Cube.boundary N := r.property.resolve_left hrt
    obtain ⟨⟨t,x⟩, hr⟩ := r
    rw [glue_side p γ h _ _ _ hrb]
    exact (hb _ _ _ hrb).symm

noncomputable def move {a b : X} (p : GenLoop N X a) (γ : Path a b) :
    C(I × I^N, X) :=
  (extend
    ⟨fun q : Unit × I^N => p q.2, p.val.continuous.comp continuous_snd⟩
    ⟨fun q : Unit × I => γ q.2, γ.continuous.comp continuous_snd⟩
    (fun _ x hx => (p.property x hx).trans γ.source.symm)).comp
    ⟨fun q => ((),q), continuous_const.prodMk continuous_id⟩

lemma move_bottom {a b : X} (p : GenLoop N X a) (γ : Path a b) (x : I^N) :
    move p γ (0,x) = p x :=
  extend_bottom _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm) () x

lemma move_side {a b : X} (p : GenLoop N X a) (γ : Path a b)
    (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) : move p γ (t,x) = γ t :=
  extend_side _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm) () t x hx

noncomputable def transportLoop {a b : X} (γ : Path a b) (p : GenLoop N X a) :
    GenLoop N X b :=
  ⟨(move p γ).comp ⟨fun x => (1,x), continuous_const.prodMk continuous_id⟩,
    fun x hx => (move_side p γ 1 x hx).trans γ.target⟩

lemma move_eq_of_restrictions {a b : X} (p : GenLoop N X a) (γ : Path a b)
    (H : C(I × I^N, X)) (h0 : ∀ x, H (0,x) = p x)
    (hb : ∀ t x, x ∈ Cube.boundary N → H (t,x) = γ t) (q : I × I^N) :
    move p γ q = H (retract q).val :=
  extend_eq_of_restrictions _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm)
    ⟨fun z : Unit × (I × I^N) => H z.2, H.continuous.comp continuous_snd⟩
    (fun _ x => h0 x) (fun _ t x hx => hb t x hx) ((),q)

lemma transportLoop_homotopic_of_homotopy {a b : X}
    (p : GenLoop N X a) (q : GenLoop N X b) (γ : Path a b)
    (H : C(I × I^N, X)) (h0 : ∀ x, H (0,x) = p x)
    (h1 : ∀ x, H (1,x) = q x)
    (hb : ∀ t x, x ∈ Cube.boundary N → H (t,x) = γ t) :
    GenLoop.Homotopic (transportLoop γ p) q := by
  refine ⟨{ toHomotopy :=
    { toFun := fun z => H (interpolate (z.1,(1,z.2)))
      continuous_toFun := H.continuous.comp (interpolate.continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_ }
            prop' := ?_ }⟩
  · intro x
    rw [interpolate_zero]
    exact (move_eq_of_restrictions p γ H h0 hb (1,x)).symm
  · intro x
    rw [interpolate_one]
    exact h1 x
  · intro s x hx
    change H (interpolate (s,(1,x))) = move p γ (1,x)
    rw [interpolate_fixed s ⟨(1,x), Or.inr hx⟩, hb 1 x hx, move_side p γ 1 x hx]

lemma transportLoop_homotopic {a b : X} (γ : Path a b)
    {p q : GenLoop N X a} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (transportLoop γ p) (transportLoop γ q) := by
  obtain ⟨H⟩ := hpq
  let f : C(I × I^N, X) := H.toHomotopy.toContinuousMap
  let g : C(I × I, X) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  have hfg : ∀ s x, x ∈ Cube.boundary N → f (s,x) = g (s,0) := by
    intro s x hx
    exact (H.eq_fst s hx).trans ((p.property x hx).trans γ.source.symm)
  refine ⟨{ toHomotopy :=
    { toFun := fun z => extend f g hfg (z.1,(1,z.2))
      continuous_toFun := (extend f g hfg).continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_ }
            prop' := ?_ }⟩
  · intro x
    exact extend_congr_at f g hfg _ _
      (fun _ y hy => (p.property y hy).trans γ.source.symm) 0 () (fun y => H.toHomotopy.apply_zero y)
      (fun _ => rfl) (1,x)
  · intro x
    exact extend_congr_at f g hfg _ _
      (fun _ y hy => (q.property y hy).trans γ.source.symm) 1 () (fun y => H.toHomotopy.apply_one y)
      (fun _ => rfl) (1,x)
  · intro s x hx
    change extend f g hfg (s,(1,x)) = move p γ (1,x)
    rw [extend_side f g hfg s 1 x hx, move_side p γ 1 x hx]
    rfl

lemma transportLoop_reverse {a b : X} (γ : Path a b) (p : GenLoop N X a) :
    GenLoop.Homotopic (transportLoop γ.symm (transportLoop γ p)) p := by
  apply transportLoop_homotopic_of_homotopy (transportLoop γ p) p γ.symm
    ⟨fun z => move p γ (unitInterval.symm z.1,z.2), (move p γ).continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)⟩
  · intro x
    exact congrArg (fun t => move p γ (t,x)) unitInterval.symm_zero
  · intro x
    change move p γ (unitInterval.symm 1,x) = p x
    rw [unitInterval.symm_one, move_bottom]
  · intro t x hx
    exact move_side p γ (unitInterval.symm t) x hx

noncomputable def transport {a b : X} (γ : Path a b) :
    HomotopyGroup N X a → HomotopyGroup N X b :=
  Quotient.map (transportLoop γ) (fun _ _ h => transportLoop_homotopic γ h)

lemma transport_reverse {a b : X} (γ : Path a b) (p : HomotopyGroup N X a) :
    transport γ.symm (transport γ p) = p := by
  induction p using Quotient.inductionOn with
  | h p => exact Quotient.sound (transportLoop_reverse γ p)

lemma transport_bijective {a b : X} (γ : Path a b) :
    Function.Bijective (transport (N := N) γ) := by
  constructor
  · have h : Function.LeftInverse (transport (N := N) γ.symm) (transport γ) :=
      transport_reverse γ
    exact h.injective
  · have h : Function.RightInverse (transport (N := N) γ.symm) (transport γ) := by
      intro p
      simpa only [Path.symm_symm] using transport_reverse γ.symm p
    exact h.surjective

end Thomason.CubeExtension

end

end OAI
