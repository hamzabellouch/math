import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.KanSimplexContinuousFibers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import Mathlib.CategoryTheory.Limits.Types.Filtered

namespace OAI

section

/-! # Compact homotopy-fibre families factor through a finite simplicial base -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Every compact family in the genuine homotopy fibre of a realized map
factors through one finite subcomplex of its base. The entire path, both
endpoints, and the original total-space coordinate are retained exactly. -/
theorem compact_homotopyFiber_finite_base {K : Type} [TopologicalSpace K] [CompactSpace K]
    {E B : SSet.{0}} (p : E ⟶ B) (b : B.obj (.op (.mk 0)))
    (f : C(K, continuousHomotopyFiber (SSet.toTop.map p) (RealizationPrism.vertexPoint B b))) :
    ∃ (A : B.Subcomplex) (_ : SSet.Finite A.toSSet)
      (bA : A.toSSet.obj (.op (.mk 0))), bA.val = b ∧
      ∃ g : C(K, continuousHomotopyFiber (SSet.toTop.map (A.fromPreimage p))
          (RealizationPrism.vertexPoint A.toSSet bA)),
        (∀ k, (SSet.toTop.map (A.preimage p).ι).hom (g k).val.val.1 = (f k).val.val.1) ∧
        (∀ k t, (SSet.toTop.map A.ι).hom ((g k).val.val.2 t) = (f k).val.val.2 t) := by
  let v : C(K × unitInterval, SSet.toTop.obj B) :=
    ⟨fun z => (f z.1).val.val.2 z.2, by fun_prop⟩
  obtain ⟨V, hV, vV, hvV⟩ := RealizationPrism.compact_map_factors B v
  have : SSet.Finite V.toSSet := hV
  let A : B.Subcomplex := V ⊔ SSet.Subcomplex.ofSimplex b
  have hA : SSet.Finite A.toSSet := by
    let U : Bool → B.Subcomplex := fun t => if t then V else SSet.Subcomplex.ofSimplex b
    have he : A = iSup U := by
      apply le_antisymm
      · exact sup_le (le_iSup U true) (le_iSup U false)
      · apply iSup_le
        intro t
        cases t
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff U).mpr
    intro t
    cases t <;> dsimp [U] <;> infer_instance
  let bA : A.toSSet.obj (.op (.mk 0)) :=
    ⟨b, (show SSet.Subcomplex.ofSimplex b ≤ A from le_sup_right)
      _ (SSet.Subcomplex.mem_ofSimplex_obj b)⟩
  let j : V.toSSet ⟶ A.toSSet := SSet.Subcomplex.homOfLE le_sup_left
  let vA : C(K × unitInterval, SSet.toTop.obj A.toSSet) :=
    (SSet.toTop.map j).hom.comp vV
  have hvA (k : K) (t : unitInterval) :
      (SSet.toTop.map A.ι).hom (vA (k, t)) = (f k).val.val.2 t := by
    have hj : j ≫ A.ι = V.ι := rfl
    have e := congrArg (fun q => q.hom (vV (k, t))) (SSet.toTop.congr_map hj)
    rw [SSet.toTop.map_comp] at e
    exact e.trans (congrArg (fun q : C(_, _) => q (k, t)) hvV)
  let e := RealizationPrism.preimageHomeomorph p A
  let xA : C(K, SSet.toTop.obj (A.preimage p).toSSet) :=
    (⟨e.symm, e.symm.continuous⟩ :
      C(((SSet.toTop.map p).hom ⁻¹' Set.range (SSet.toTop.map A.ι).hom),
        SSet.toTop.obj (A.preimage p).toSSet)).comp ⟨fun k => ⟨(f k).val.val.1, by
      change (SSet.toTop.map p).hom (f k).val.val.1 ∈
        Set.range (SSet.toTop.map A.ι).hom
      refine ⟨vA (k, 0), ?_⟩
      exact (hvA k 0).trans (f k).val.property⟩, by
        apply Continuous.subtype_mk
        fun_prop⟩
  have hxA (k : K) :
      (SSet.toTop.map (A.preimage p).ι).hom (xA k) = (f k).val.val.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hz (k : K) : vA (k, 0) = (SSet.toTop.map (A.fromPreimage p)).hom (xA k) := by
    apply RealizationPrism.inclusion_injective B A
    have he := congrArg (fun q => q.hom (xA k))
      (RealizationPrism.fromPreimage_commutes p A)
    change (SSet.toTop.map A.ι).hom ((SSet.toTop.map (A.fromPreimage p)).hom (xA k)) =
      (SSet.toTop.map p).hom ((SSet.toTop.map (A.preimage p).ι).hom (xA k)) at he
    rw [hxA k] at he
    exact (hvA k 0).trans ((f k).val.property.trans he.symm)
  have ho (k : K) : vA (k, 1) = RealizationPrism.vertexPoint A.toSSet bA := by
    apply RealizationPrism.inclusion_injective B A
    rw [RealizationPrism.map_vertexPoint]
    exact (hvA k 1).trans (f k).property
  let g : C(K, continuousHomotopyFiber (SSet.toTop.map (A.fromPreimage p))
      (RealizationPrism.vertexPoint A.toSSet bA)) := {
    toFun k := ⟨⟨(xA k, ⟨fun t => vA (k, t), by fun_prop⟩), hz k⟩, ho k⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk xA.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : K × unitInterval => vA (z.1, z.2))
      exact vA.continuous }
  exact ⟨A, hA, bA, rfl, g, hxA, hvA⟩

end

end Thomason.Construction

end

section

/-! # Compact homotopy-fibre families have finite simplicial arrow support -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A compact family in a homotopy fibre is supported on an actual map
between finite simplicial sets. Both comparison maps are monomorphisms,
the square commutes strictly, and the entire original path is recovered. -/
theorem compact_homotopyFiber_finite_arrow {K : Type} [TopologicalSpace K] [CompactSpace K]
    {E B : SSet.{0}} (p : E ⟶ B) (b : B.obj (.op (.mk 0)))
    (f : C(K, continuousHomotopyFiber (SSet.toTop.map p) (RealizationPrism.vertexPoint B b))) :
    ∃ (A : B.Subcomplex) (_ : SSet.Finite A.toSSet)
      (L : SSet.{0}) (_ : SSet.Finite L) (j : L ⟶ E) (_ : Mono j)
      (q : L ⟶ A.toSSet) (bA : A.toSSet.obj (.op (.mk 0))),
      q ≫ A.ι = j ≫ p ∧ bA.val = b ∧
      ∃ g : C(K, continuousHomotopyFiber (SSet.toTop.map q)
          (RealizationPrism.vertexPoint A.toSSet bA)),
        (∀ k, (SSet.toTop.map j).hom (g k).val.val.1 = (f k).val.val.1) ∧
        (∀ k t, (SSet.toTop.map A.ι).hom ((g k).val.val.2 t) = (f k).val.val.2 t) := by
  obtain ⟨A, hA, bA, hbA, gA, hxA, htA⟩ := compact_homotopyFiber_finite_base p b f
  let x : C(K, SSet.toTop.obj (A.preimage p).toSSet) :=
    ⟨fun k => (gA k).val.val.1, by fun_prop⟩
  obtain ⟨S, hS, xS, hxS⟩ := RealizationPrism.compact_map_factors (A.preimage p).toSSet x
  let j : S.toSSet ⟶ E := S.ι ≫ (A.preimage p).ι
  let q : S.toSSet ⟶ A.toSSet := S.ι ≫ A.fromPreimage p
  have hq : q ≫ A.ι = j ≫ p := by
    dsimp only [q, j]
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι, Category.assoc]
  have hzero (k : K) : (gA k).val.val.2 0 = (SSet.toTop.map q).hom (xS k) := by
    have he := congrArg (fun z : C(_, _) => (SSet.toTop.map (A.fromPreimage p)).hom (z k)) hxS
    change (SSet.toTop.map (A.fromPreimage p)).hom
        ((SSet.toTop.map S.ι).hom (xS k)) =
      (SSet.toTop.map (A.fromPreimage p)).hom (gA k).val.val.1 at he
    rw [show SSet.toTop.map q = SSet.toTop.map S.ι ≫ SSet.toTop.map (A.fromPreimage p) from
      SSet.toTop.map_comp _ _]
    exact (gA k).val.property.trans he.symm
  let g : C(K, continuousHomotopyFiber (SSet.toTop.map q)
      (RealizationPrism.vertexPoint A.toSSet bA)) := {
    toFun k := ⟨⟨(xS k, (gA k).val.val.2), hzero k⟩, (gA k).property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact xS.continuous.prodMk (by fun_prop) }
  refine ⟨A, hA, S.toSSet, hS, j, inferInstance, q, bA, hq, hbA, g, ?_, htA⟩
  intro k
  change (SSet.toTop.map j).hom (xS k) = _
  rw [show SSet.toTop.map j = SSet.toTop.map S.ι ≫ SSet.toTop.map (A.preimage p).ι from
    SSet.toTop.map_comp _ _]
  have he := congrArg (fun z : C(_, _) => (SSet.toTop.map (A.preimage p).ι).hom (z k)) hxS
  exact he.trans (hxA k)

end

end Thomason.Construction

end

section

/-! # Retracts of the actual Kan base-change weak test -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- The Kan base-change property is closed under arrow retracts. The
fibration above the larger target is pulled back along its retraction. -/
instance kanBaseChangeWeak_stableUnderRetracts : kanBaseChangeWeak.IsStableUnderRetracts where
  of_retract {A B C D i j} h hj := by
    intro E p hp
    have := hp
    let U := pullback p i
    let S := pullback p (h.r.left ≫ i)
    let Q := pullback p h.r.right
    let q : Q ⟶ D := pullback.snd p h.r.right
    have : HomotopicalAlgebra.Fibration q := kan_pullback_snd_fibration p h.r.right
    have hs : IsPullback (pullback.fst p (h.r.left ≫ i))
        (pullback.snd p (h.r.left ≫ i)) p (j ≫ h.r.right) := by
      rw [← h.r_w]
      exact IsPullback.of_hasPullback _ _
    let t : S ⟶ Q := (IsPullback.of_hasPullback p h.r.right).lift
      (pullback.fst p (h.r.left ≫ i))
      (pullback.snd p (h.r.left ≫ i) ≫ j) (by
        rw [Category.assoc]
        exact hs.w)
    have ht : IsPullback t (pullback.snd p (h.r.left ≫ i)) q j :=
      IsPullback.of_right' hs (IsPullback.of_hasPullback p h.r.right)
    have htw : realizationWeakEquivalences t := hj.of_isPullback ht
    let er : E ⟶ Q := pullback.lift (𝟙 E) (p ≫ h.i.right) (by
      rw [Category.assoc, h.retract_right, Category.comp_id, Category.id_comp])
    let us : U ⟶ S := pullback.lift (pullback.fst p i)
      (pullback.snd p i ≫ h.i.left) (by
        rw [← Category.assoc, Category.assoc (pullback.snd p i) h.i.left h.r.left, h.retract_left,
          Category.comp_id, pullback.condition])
    let su : S ⟶ U := pullback.lift (pullback.fst p (h.r.left ≫ i))
      (pullback.snd p (h.r.left ≫ i) ≫ h.r.left) (by
        rw [Category.assoc, pullback.condition])
    have ht₁ : t ≫ pullback.fst p h.r.right = pullback.fst p (h.r.left ≫ i) :=
      IsPullback.lift_fst _ _ _ _
    have ht₂ : t ≫ pullback.snd p h.r.right = pullback.snd p (h.r.left ≫ i) ≫ j :=
      IsPullback.lift_snd _ _ _ _
    have hus₁ : us ≫ pullback.fst p (h.r.left ≫ i) = pullback.fst p i :=
      pullback.lift_fst _ _ _
    have hus₂ : us ≫ pullback.snd p (h.r.left ≫ i) = pullback.snd p i ≫ h.i.left :=
      pullback.lift_snd _ _ _
    have hsu₁ : su ≫ pullback.fst p i = pullback.fst p (h.r.left ≫ i) :=
      pullback.lift_fst _ _ _
    have hsu₂ : su ≫ pullback.snd p i = pullback.snd p (h.r.left ≫ i) ≫ h.r.left :=
      pullback.lift_snd _ _ _
    have her : er ≫ pullback.fst p h.r.right = 𝟙 E := pullback.lift_fst _ _ _
    have her₂ : er ≫ pullback.snd p h.r.right = p ≫ h.i.right := pullback.lift_snd _ _ _
    have hut : us ≫ t = pullback.fst p i ≫ er := by
      apply pullback.hom_ext
      · rw [Category.assoc, ht₁, hus₁, Category.assoc, her, Category.comp_id]
      · rw [Category.assoc, ht₂, ← Category.assoc, hus₂, Category.assoc, h.i_w, Category.assoc, her₂]
        simp only [← Category.assoc, pullback.condition]
    have hsur : su ≫ pullback.fst p i = t ≫ pullback.fst p h.r.right :=
      hsu₁.trans ht₁.symm
    have hus : us ≫ su = 𝟙 U := by
      apply pullback.hom_ext
      · rw [Category.assoc, hsu₁, hus₁, Category.id_comp]
      · rw [Category.assoc, hsu₂, ← Category.assoc, hus₂, Category.assoc,
          h.retract_left, Category.comp_id, Category.id_comp]
    let H : RetractArrow (pullback.fst p i) t := {
      i := Arrow.homMk us er hut
      r := Arrow.homMk su (pullback.fst p h.r.right) hsur
      retract := by
        apply Arrow.hom_ext
        · exact hus
        · exact her }
    exact MorphismProperty.of_retract H htw

end

end Thomason.Construction

end

section

/-! # Countable cellular closure of the Kan base-change test -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

instance kanBaseChangeWeak_multiplicative : kanBaseChangeWeak.IsMultiplicative where
  id_mem X := by
    intro E p _
    exact realizationWeakEquivalences.of_isIso _
  comp_mem _ _ hi hj := kanBaseChangeWeak_comp hi hj

private theorem sequence_map_mono_and_weak (F : ℕ ⥤ SSet.{0})
    (hm : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n, kanBaseChangeWeak (F.map (homOfLE (Nat.le_succ n)))) :
    ∀ n m (h : n ≤ m), Mono (F.map (homOfLE h)) ∧ kanBaseChangeWeak (F.map (homOfLE h)) := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base =>
    simp only [homOfLE_refl, F.map_id]
    exact ⟨inferInstance, kanBaseChangeWeak.id_mem _⟩
  | succ m h ih =>
    have he : F.map (homOfLE (h.trans (Nat.le_succ m))) =
        F.map (homOfLE h) ≫ F.map (homOfLE (Nat.le_succ m)) := by
      rw [← F.map_comp]
      rfl
    rw [he]
    have := ih.1
    have := hm m
    exact ⟨inferInstance, kanBaseChangeWeak_comp ih.2 (hw m)⟩

/-- A colimit of a monic simplicial sequence has monic structure maps. -/
theorem simplicial_sequence_leg_mono (F : ℕ ⥤ SSet.{0}) {c : Cocone F}
    (hc : IsColimit c) (hm : ∀ n m (h : n ≤ m), Mono (F.map (homOfLE h))) (n : ℕ) :
    Mono (c.ι.app n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y he
  have hce := isColimitOfPreserves (SSet.evaluation.obj d) hc
  obtain ⟨m, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hce x y).mp he
  have : Mono (F.map f) := hm n m (leOfHom f)
  have : Mono ((F.map f).app d) := inferInstance
  exact (CategoryTheory.mono_iff_injective _).mp this hf

/-- Countable monic sequences preserve the actual Kan base-change weak test.
The colimit is replaced by its increasing image subcomplexes only inside
this proof; its original initial structure map is the conclusion. -/
theorem kanBaseChangeWeak_sequence (F : ℕ ⥤ SSet.{0}) {c : Cocone F}
    (hc : IsColimit c) (hm : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n, kanBaseChangeWeak (F.map (homOfLE (Nat.le_succ n)))) :
    kanBaseChangeWeak (c.ι.app 0) := by
  have hall := sequence_map_mono_and_weak F hm hw
  have hm' : ∀ n, Mono (c.ι.app n) :=
    simplicial_sequence_leg_mono F hc (fun n m h => (hall n m h).1)
  let R : ℕ → c.pt.Subcomplex := fun n => SSet.Subcomplex.range (c.ι.app n)
  have hR : Monotone R := by
    intro n m h
    change SSet.Subcomplex.range (c.ι.app n) ≤ SSet.Subcomplex.range (c.ι.app m)
    rw [← c.w (homOfLE h)]
    exact Subfunctor.range_comp_le _ _
  have hcover : iSup R = ⊤ := by
    apply top_unique
    intro d x _
    obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (SSet.evaluation.obj d) hc) x
    rw [Subfunctor.iSup_obj, Set.mem_iUnion]
    exact ⟨n, y, hy⟩
  let e (n : ℕ) : F.obj n ≅ (R n).toSSet := by
    have := hm' n
    let t := SSet.Subcomplex.toRange (c.ι.app n)
    have : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι (c.ι.app n))
    have : IsIso t := isIso_of_mono_of_epi t
    exact asIso t
  have he (n : ℕ) : (e n).hom ≫ (R n).ι = c.ι.app n := rfl
  have hr : kanBaseChangeWeak (R 0).ι := by
    apply kanBaseChangeWeak_exhaustion R hR hcover
    intro n
    have hh : F.map (homOfLE (Nat.zero_le n)) ≫ (e n).hom =
        (e 0).hom ≫ SSet.Subcomplex.homOfLE (hR (Nat.zero_le n)) := by
      apply (cancel_mono (R n).ι).mp
      rw [Category.assoc, he]
      change F.map (homOfLE (Nat.zero_le n)) ≫ c.ι.app n = (e 0).hom ≫ (R 0).ι
      rw [he, c.w]
    exact (kanBaseChangeWeak.arrow_mk_iso_iff
      (Arrow.isoMk (e 0) (e n) hh.symm)).mp (hall 0 n (Nat.zero_le n)).2
  rw [← he 0]
  exact kanBaseChangeWeak.comp_mem _ _ (kanBaseChangeWeak.of_isIso _) hr

end

end Thomason.Construction

end

section

/-! # Every anodyne extension is weak after Kan base change

The proof uses the actual countable horn presentation and the constructed
closure operations. No acyclic-Kan or right-properness hypothesis is used.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen

noncomputable section

abbrev kanWeakMonomorphisms : MorphismProperty SSet.{0} :=
  monomorphisms SSet.{0} ⊓ kanBaseChangeWeak

instance kanWeakMonomorphisms_cobaseChange : kanWeakMonomorphisms.IsStableUnderCobaseChange where
  of_isPushout sq hf := by
    have := hf.1
    exact ⟨(monomorphisms SSet).of_isPushout sq hf.1,
      kanBaseChangeWeak_pushout sq.flip hf.2⟩

instance kanWeakMonomorphisms_coproducts : IsStableUnderCoproducts.{0} kanWeakMonomorphisms where
  isStableUnderCoproductsOfShape α := IsStableUnderCoproductsOfShape.mk kanWeakMonomorphisms α (by
    intro A B _ _ i hi
    have : ∀ a, Mono (i a) := fun a => (hi a).1
    exact ⟨inferInstance, kanBaseChangeWeak_sigma i (fun a => (hi a).2)⟩)

instance kanWeakMonomorphisms_countable :
    kanWeakMonomorphisms.IsStableUnderTransfiniteCompositionOfShape ℕ where
  le := by
    rintro A B f ⟨h⟩
    have hm (n : ℕ) : Mono (h.F.map (homOfLE (Nat.le_succ n))) :=
      (h.map_mem n (not_isMax n)).1
    have hw (n : ℕ) : kanBaseChangeWeak (h.F.map (homOfLE (Nat.le_succ n))) :=
      (h.map_mem n (not_isMax n)).2
    have hl := kanBaseChangeWeak_sequence h.F h.isColimit hm hw
    have hmall : ∀ n m (hnm : n ≤ m), Mono (h.F.map (homOfLE hnm)) := by
      intro n m hnm
      induction m, hnm using Nat.le_induction with
      | base => simpa only [homOfLE_refl, h.F.map_id] using (inferInstance : Mono (𝟙 (h.F.obj n)))
      | succ m hnm ih =>
        have he : h.F.map (homOfLE (hnm.trans (Nat.le_succ m))) =
            h.F.map (homOfLE hnm) ≫ h.F.map (homOfLE (Nat.le_succ m)) := by
          rw [← h.F.map_comp]
          rfl
        rw [he]
        have := hm m
        have := ih
        infer_instance
    have : Mono (h.incl.app 0) := simplicial_sequence_leg_mono h.F h.isColimit hmall 0
    rw [← h.fac]
    exact ⟨inferInstance, kanBaseChangeWeak.comp_mem _ _ (kanBaseChangeWeak.of_isIso _) hl⟩

/-- Every horn generator has the required strengthened weak property. -/
theorem horn_generators_kanWeak : J.{0} ≤ kanWeakMonomorphisms := by
  intro A B i hi
  refine ⟨J_le_monomorphisms i hi, ?_⟩
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact horn_kanBaseChangeWeak n k

/-- Arbitrary anodyne extensions become actual realization weak equivalences
on pullback along Kan fibrations. -/
theorem anodyne_kanBaseChangeWeak : SSet.anodyneExtensions.{0} ≤ kanWeakMonomorphisms := by
  rw [SSet.anodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]
  rw [retracts_le_iff]
  apply (transfiniteCompositionsOfShape_monotone ℕ ?_).trans
    (transfiniteCompositionsOfShape_le kanWeakMonomorphisms ℕ)
  rw [pushouts_le_iff, coproducts_le_iff]
  exact horn_generators_kanWeak

/-- The original canonical pullback map satisfies the actual weak test. -/
theorem kan_pullback_anodyne_weak {A B E : SSet.{0}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (pullback.fst p i) :=
  (anodyne_kanBaseChangeWeak i hi).2 E p inferInstance

end

end Thomason.Construction

end

section

/-! # Comparing an extension of a fibration to its original base -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- The actual comparison to the restriction of a larger total space. -/
def kanExtensionComparison {E F B C : SSet.{0}} (p : E ⟶ B) (i : B ⟶ C)
    (j : E ⟶ F) (q : F ⟶ C) (h : j ≫ q = p ≫ i) : E ⟶ pullback q i :=
  pullback.lift j p h

@[reassoc]
theorem kanExtensionComparison_fst {E F B C : SSet.{0}} (p : E ⟶ B) (i : B ⟶ C)
    (j : E ⟶ F) (q : F ⟶ C) (h : j ≫ q = p ≫ i) :
    kanExtensionComparison p i j q h ≫ pullback.fst q i = j := pullback.lift_fst _ _ _

@[reassoc]
theorem kanExtensionComparison_snd {E F B C : SSet.{0}} (p : E ⟶ B) (i : B ⟶ C)
    (j : E ⟶ F) (q : F ⟶ C) (h : j ≫ q = p ≫ i) :
    kanExtensionComparison p i j q h ≫ pullback.snd q i = p := pullback.lift_snd _ _ _

/-- Extending both base and total space by anodyne maps gives an actual weak
comparison with the restriction, when the new projection is Kan. -/
theorem kanExtensionComparison_mono_weak {E F B C : SSet.{0}}
    (p : E ⟶ B) (i : B ⟶ C) (j : E ⟶ F) (q : F ⟶ C)
    (h : j ≫ q = p ≫ i) (hi : SSet.anodyneExtensions i)
    (hj : SSet.anodyneExtensions j) [HomotopicalAlgebra.Fibration q] :
    Mono (kanExtensionComparison p i j q h) ∧
      realizationWeakEquivalences (kanExtensionComparison p i j q h) := by
  have : Mono j := (anodyne_mono_realization_weak j hj).1
  constructor
  · exact mono_of_mono_fac (kanExtensionComparison_fst p i j q h)
  · apply realizationWeakEquivalences.of_postcomp _ (pullback.fst q i)
      (kan_pullback_anodyne_weak i hi q)
    rw [kanExtensionComparison_fst]
    exact anodyne_realization_weak j hj

/-- Every map over an anodyne extension of its base admits such a
comparison. This uses only the algebraic horn factorization. -/
theorem exists_kan_anodyne_extension {E B C : SSet.{0}} (p : E ⟶ B)
    (i : B ⟶ C) (hi : SSet.anodyneExtensions i) :
    ∃ (F : SSet.{0}) (j : E ⟶ F) (q : F ⟶ C),
      SSet.anodyneExtensions j ∧ HomotopicalAlgebra.Fibration q ∧
      ∃ h : j ≫ q = p ≫ i,
        Mono (kanExtensionComparison p i j q h) ∧
        realizationWeakEquivalences (kanExtensionComparison p i j q h) := by
  have := horn_weakFactorizationSystem
  let d := MorphismProperty.factorizationData SSet.anodyneExtensions J.rlp (p ≫ i)
  have hq : HomotopicalAlgebra.Fibration d.p := (fibration_iff _).mpr d.hp
  have := hq
  exact ⟨d.Z, d.i, d.p, d.hi, hq, d.fac,
    kanExtensionComparison_mono_weak p i d.i d.p d.fac hi d.hi⟩

end

end Thomason.Construction

end

section

/-! # Finite relative approximation in an anodyne preimage of a Kan fibration -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- The actual preimage inclusion of an anodyne subcomplex is weak. -/
theorem kan_anodyne_preimage_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (A : B.Subcomplex) (hA : SSet.anodyneExtensions A.ι) :
    realizationWeakEquivalences (A.preimage p).ι :=
  (anodyne_kanBaseChangeWeak A.ι hA).2.of_isPullback (subcomplex_preimage_isPullback A p)

/-- A finite relative lifting problem into the total realization can be
moved into an anodyne preimage, keeping the prescribed boundary exactly.
Both the lift and the whole relative homotopy lie in finite subcomplexes. -/
theorem finite_relative_kan_preimage_approximation {E B K L : SSet.{0}} [L.Finite]
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (A : B.Subcomplex) (hA : SSet.anodyneExtensions A.ι)
    (i : K ⟶ L) [Mono i] (a : K ⟶ (A.preimage p).toSSet)
    (b : SSet.toTop.obj L ⟶ SSet.toTop.obj E)
    (h : SSet.toTop.map a ≫ SSet.toTop.map (A.preimage p).ι = SSet.toTop.map i ≫ b) :
    ∃ (S : (A.preimage p).toSSet.Subcomplex) (T : E.Subcomplex),
      SSet.Finite S.toSSet ∧ SSet.Finite T.toSSet ∧
      ∃ (g : S.toSSet ⟶ T.toSSet) (a' : K ⟶ S.toSSet)
        (c : SSet.toTop.obj L ⟶ SSet.toTop.obj S.toSSet)
        (b' : SSet.toTop.obj L ⟶ SSet.toTop.obj T.toSSet),
        g ≫ T.ι = S.ι ≫ (A.preimage p).ι ∧ a' ≫ S.ι = a ∧
        SSet.toTop.map i ≫ c = SSet.toTop.map a' ∧
        b' ≫ SSet.toTop.map T.ι = b ∧
        Nonempty ((c ≫ SSet.toTop.map g).hom.HomotopyRel b'.hom
          (Set.range (SSet.toTop.map i).hom)) :=
  finite_relative_lift_with_homotopy_support i (A.preimage p).ι
    (kan_anodyne_preimage_weak p A hA) a b h

end

end Thomason.Construction

end

end OAI
