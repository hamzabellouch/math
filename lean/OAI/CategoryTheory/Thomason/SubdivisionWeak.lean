import Mathlib
import OAI.CategoryTheory.Thomason.ExtensionAnodyne

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

noncomputable def conicalFlagExtension (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a ≤ c a) (hp : ∀ a : A, p ≤ c a)
    (f : MeetingChains A →o A) : NonemptyFiniteChains E →o A := by
  classical
  let old (s : NonemptyFiniteChains E) := ∀ a ∈ s.finset, a ∈ A
  let meet (s : NonemptyFiniteChains E) := ∃ a ∈ s.finset, a ∈ A
  let cert (s : NonemptyFiniteChains E) (hs : old s) : MeetingChains A :=
    ⟨s, chainLast s, chainGreatest_mem s, hs _ (chainGreatest_mem s)⟩
  let r (s : NonemptyFiniteChains E) : A :=
    if hs : old s then f (cert s hs)
    else if hs : meet s then c (f ⟨s, hs⟩) else p
  refine ⟨r, fun s t hst => ?_⟩
  by_cases ht : old t
  · have hs : old s := fun a ha => ht a (hst ha)
    dsimp [r]
    rw [dite_eq_left hs, dite_eq_left ht]
    exact f.monotone hst
  · by_cases hs : old s
    · have htm : meet t := by
        obtain ⟨a, ha⟩ := s.nonempty
        exact ⟨a, hst ha, hs a ha⟩
      dsimp [r]
      rw [dite_eq_left hs, dite_eq_right ht, dite_eq_left htm]
      exact (f.monotone hst).trans (hc _)
    · by_cases hsm : meet s
      · have htm : meet t := by
          obtain ⟨a, ha, haA⟩ := hsm
          exact ⟨a, hst ha, haA⟩
        dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_left hsm, dite_eq_left htm]
        exact c.monotone (f.monotone hst)
      · dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_right hsm]
        split_ifs with htm
        · exact hp _
        · exact le_rfl

lemma conicalFlagExtension_old (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a ≤ c a) (hp : ∀ a : A, p ≤ c a)
    (f : MeetingChains A →o A) (s : NonemptyFiniteChains E)
    (hs : ∀ a ∈ s.finset, a ∈ A) (hm : ∃ a ∈ s.finset, a ∈ A) :
    conicalFlagExtension A p c hc hp f s = f ⟨s, hm⟩ := by
  classical
  simp only [conicalFlagExtension, OrderHom.coe_mk, dite_eq_left hs]

lemma hornFaces_downward {n : ℕ} (k : Fin (n+1))
    {s t : NonemptyFiniteChains (ULift.{u} (Fin (n+1)))} (h : s ≤ t)
    (ht : t ∈ HornFaces n k) : s ∈ HornFaces n k := by
  obtain ⟨a, hak, ha⟩ := ht
  exact ⟨a, hak, fun hs => ha (h hs)⟩

noncomputable def hornFlagOldVertices {n : ℕ} (k : Fin (n+1)) :
    MeetingChains (HornFaces.{u} n k) →o HornFaces.{u} n k where
  toFun s := ⟨(chainIntersection _ s).val.map chainLast, by
    apply hornFaces_downward k (t := chainLast (chainIntersection _ s).val)
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := ((chainIntersection _ s).val.mem_map_iff chainLast a).mp ha
      exact (le_chainGreatest (chainIntersection _ s).val hb) (chainGreatest_mem b)
    · exact (chainIntersection _ s).property _ (chainGreatest_mem _)⟩
  monotone' _ _ h := (NonemptyFiniteChains.orderHomMap chainLast).monotone
    ((chainIntersection _).monotone h)

lemma hornFlagOldVertices_old {n : ℕ} (k : Fin (n+1))
    (s : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))))
    (hs : ∀ a ∈ s.finset, a ∈ HornFaces n k) (hm : ∃ a ∈ s.finset, a ∈ HornFaces n k) :
    (hornFlagOldVertices k ⟨s, hm⟩).val = s.map chainLast := by
  classical
  change (chainIntersection _ ⟨s, hm⟩).val.map chainLast = s.map chainLast
  congr 1
  apply NonemptyFiniteChains.ext
  exact Finset.filter_eq_self.mpr hs

noncomputable def hornFlagExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) →o HornFaces.{u} n k :=
  conicalFlagExtension _ (hornFacePoint hn k) (hornFaceCone k)
    (le_hornFaceCone k) (hornFacePoint_le_cone hn k) (hornFlagOldVertices k)

lemma hornFlagExtension_old {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    (s : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))))
    (hs : ∀ a ∈ s.finset, a ∈ HornFaces n k) :
    (hornFlagExtension hn k s).val = s.map chainLast := by
  let hm : ∃ a ∈ s.finset, a ∈ HornFaces n k :=
    ⟨chainLast s, chainGreatest_mem _, hs _ (chainGreatest_mem _)⟩
  rw [hornFlagExtension, conicalFlagExtension_old _ _ _ _ _ _ _ hs hm]
  exact hornFlagOldVertices_old k s hs hm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

lemma sd_lastVertex_nerve :
    SSet.sd.map (lastVertex.app (nerve E)) ≫ sdNerveMap =
      sdTwiceNerveIso.hom ≫ nerveMap
        (NonemptyFiniteChains.orderHomMap (chainLast (X := E))).monotone.functor := by
  rw [← lastVertex_nerve, SSet.sd.map_comp, Category.assoc, sdNerveMap_naturality]
  rfl

noncomputable def orderedSdExtension (K : (nerve E).Subcomplex)
    (r : NonemptyFiniteChains (NonemptyFiniteChains E) →o AllowedChains K) :
    (SSet.sd ⋙ SSet.sd).obj (nerve E) ⟶ SSet.sd.obj (K : SSet) :=
  sdTwiceNerveIso.hom ≫ nerveMap r.monotone.functor ≫ (sdSubcomplexIso K).inv

lemma orderedSdExtension_restriction (K : (nerve E).Subcomplex)
    (r : NonemptyFiniteChains (NonemptyFiniteChains E) →o AllowedChains K)
    (hr : ∀ s : NonemptyFiniteChains (AllowedChains K),
      (r (s.map (OrderHom.Subtype.val _))).val =
        (s.map (OrderHom.Subtype.val _)).map chainLast) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ orderedSdExtension K r =
      SSet.sd.map (lastVertex.app (K : SSet)) := by
  let j := nerveMap (NonemptyFiniteChains.orderHomMap (allowedChainInclusion K)).monotone.functor
  let v := nerveMap (NonemptyFiniteChains.orderHomMap (chainLast (X := E))).monotone.functor
  have he : j ≫ nerveMap r.monotone.functor ≫ allowedChainsForget K = j ≫ v := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact hr (x.obj i)
  apply (cancel_mono ((sdSubcomplexIso K).hom ≫ allowedChainsForget K)).mp
  change (_ ≫ (_ ≫ _ ≫ _)) ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (SSet.sd ⋙ SSet.sd).map K.ι ≫ sdTwiceNerveIso.hom ≫
      nerveMap r.monotone.functor ≫ allowedChainsForget K = _
  calc
    _ = (sdTwiceSubcomplexIso K).hom ≫ j ≫ nerveMap r.monotone.functor ≫
        allowedChainsForget K := by
      rw [← Category.assoc, sdTwiceSubcomplexIso_naturality]
      rfl
    _ = (sdTwiceSubcomplexIso K).hom ≫ j ≫ v := by rw [he]
    _ = (SSet.sd ⋙ SSet.sd).map K.ι ≫ sdTwiceNerveIso.hom ≫ v := by
      rw [← Category.assoc _ sdTwiceNerveIso.hom v, sdTwiceSubcomplexIso_naturality]
      rfl
    _ = SSet.sd.map (SSet.sd.map K.ι) ≫
        SSet.sd.map (lastVertex.app (nerve E)) ≫ sdNerveMap := by
      rw [sd_lastVertex_nerve]
      rfl
    _ = SSet.sd.map (lastVertex.app (K : SSet)) ≫ SSet.sd.map K.ι ≫ sdNerveMap := by
      rw [← Category.assoc, ← SSet.sd.map_comp, lastVertex.naturality,
        SSet.sd.map_comp, Category.assoc]
      rfl
    _ = _ := by rw [sdSubcomplexMap_naturality]; rfl

noncomputable def hornFlagExtensionAllowed {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) →o
      AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)) :=
  (hornFacesIso k).symm.toOrderEmbedding.toOrderHom.comp (hornFlagExtension hn k)

lemma hornFlagExtensionAllowed_old {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    (s : NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)))) :
    (hornFlagExtensionAllowed hn k (s.map (OrderHom.Subtype.val _))).val =
      (s.map (OrderHom.Subtype.val _)).map chainLast := by
  apply hornFlagExtension_old
  intro a ha
  obtain ⟨b, _, rfl⟩ := (s.mem_map_iff _ a).mp ha
  exact (hornFaces_allowed_iff k b.val).mp b.property

noncomputable def sdHornExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    (SSet.sd ⋙ SSet.sd).obj (SSet.stdSimplex.{u}.obj ⦋n⦌) ⟶ SSet.sd.obj (SSet.horn n k : SSet) :=
  (SSet.sd ⋙ SSet.sd).map (SSet.stdSimplex.isoNerve n).hom ≫
    orderedSdExtension _ (hornFlagExtensionAllowed hn k) ≫
      SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).inv

lemma sdHornExtension_restriction {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    (SSet.sd ⋙ SSet.sd).map (SSet.horn.{u} n k).ι ≫ sdHornExtension hn k =
      SSet.sd.map (lastVertex.app (SSet.horn n k : SSet)) := by
  rw [sdHornExtension, ← Category.assoc, ← Functor.map_comp]
  have h : (SSet.horn.{u} n k).ι ≫ (SSet.stdSimplex.isoNerve n).hom =
      (orderedSimplexSubcomplexIso (SSet.horn n k)).hom ≫
        (orderedSimplexSubcomplex (SSet.horn n k)).ι := rfl
  rw [h, Functor.map_comp, Category.assoc, ← Category.assoc _ (orderedSdExtension _ _) _,
    orderedSdExtension_restriction _ _ (hornFlagExtensionAllowed_old hn k)]
  change SSet.sd.map (SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).hom) ≫
    SSet.sd.map (lastVertex.app _) ≫ SSet.sd.map (orderedSimplexSubcomplexIso (SSet.horn n k)).inv = _
  rw [← Category.assoc, ← SSet.sd.map_comp, lastVertex.naturality,
    SSet.sd.map_comp, Category.assoc, ← SSet.sd.map_comp, Functor.id_map]
  erw [Iso.hom_inv_id, SSet.sd.map_id, Category.comp_id]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial

lemma exComparison_double_mate {A X : SSet.{u}} (a : A ⟶ SSet.ex.obj X) :
    (SSet.sdExAdjunction.comp SSet.sdExAdjunction).homEquiv A X
      (SSet.sd.map (lastVertex.app A) ≫ (SSet.sdExAdjunction.homEquiv A X).symm a) =
      a ≫ exComparison.app (SSet.ex.obj X) := by
  change SSet.sdExAdjunction.homEquiv A (SSet.ex.obj X)
    (SSet.sdExAdjunction.homEquiv (SSet.sd.obj A) X _) = _
  rw [SSet.sdExAdjunction.homEquiv_naturality_left]
  erw [Equiv.apply_symm_apply, SSet.sdExAdjunction.homEquiv_naturality_right]
  exact (exComparison.naturality a).symm

noncomputable def exHornExtension {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    {X : SSet.{u}} (a : (SSet.horn n k : SSet.{u}) ⟶ SSet.ex.obj X) :
    SSet.stdSimplex.obj ⦋n⦌ ⟶ SSet.ex.obj (SSet.ex.obj X) :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).homEquiv _ _
    (sdHornExtension hn k ≫ (SSet.sdExAdjunction.homEquiv _ _).symm a)

lemma exHornExtension_restriction {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    {X : SSet.{u}} (a : (SSet.horn n k : SSet.{u}) ⟶ SSet.ex.obj X) :
    (SSet.horn n k).ι ≫ exHornExtension hn k a = a ≫ exComparison.app (SSet.ex.obj X) := by
  rw [exHornExtension, ← Adjunction.homEquiv_naturality_left,
    ← Category.assoc, sdHornExtension_restriction, exComparison_double_mate]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Simplicial

noncomputable abbrev exStage (X : SSet.{u}) : ℕ → SSet.{u} :=
  Nat.rec X (fun _ Y => SSet.ex.obj Y)

noncomputable def exSequence (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  Functor.ofSequence (X := exStage X) (fun n => exComparison.app (exStage X n))

noncomputable def exInfinity (X : SSet.{u}) : SSet.{u} := colimit (exSequence X)

noncomputable def exInfinityInclusion (X : SSet.{u}) (n : ℕ) :
    exStage X n ⟶ exInfinity X := colimit.ι (exSequence X) n

@[reassoc]
lemma exInfinityInclusion_step (X : SSet.{u}) (n : ℕ) :
    exComparison.app (exStage X n) ≫ exInfinityInclusion X (n+1) =
      exInfinityInclusion X n := by
  have h := colimit.w (exSequence X) (homOfLE (n.le_add_right 1))
  change _ ≫ exInfinityInclusion X (n+1) = exInfinityInclusion X n at h
  erw [Functor.ofSequence_map_homOfLE_succ] at h
  exact h

noncomputable def exInfinityComparison (X : SSet.{u}) : X ⟶ exInfinity X :=
  exInfinityInclusion X 0

lemma exInfinityComparison_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (exInfinityComparison X) := by
  apply SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ
  refine ⟨{
    F := exSequence X
    isoBot := Iso.refl _
    incl := (colimit.cocone (exSequence X)).ι
    isColimit := colimit.isColimit _
    fac := Category.id_comp _
    map_mem := ?_ }⟩
  intro n _
  change SSet.anodyneExtensions ((exSequence X).map (homOfLE (Nat.le_succ n)))
  change SSet.anodyneExtensions ((Functor.ofSequence (X := exStage X)
    (fun n => exComparison.app (exStage X n))).map (homOfLE (n.le_add_right 1)))
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact exComparison_anodyne (exStage X n)

lemma exInfinityComparison_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (exInfinityComparison X) :=
  TopologicalHorn.anodyne_weak_equivalence _ (exInfinityComparison_anodyne X)

lemma exInfinity_horn_filling (X : SSet.{u}) {n : ℕ} (k : Fin (n+2))
    (a : (SSet.horn (n+1) k : SSet.{u}) ⟶ exInfinity X) :
    ∃ b : SSet.stdSimplex.obj ⦋n+1⦌ ⟶ exInfinity X, (SSet.horn (n+1) k).ι ≫ b = a := by
  let : PreservesFilteredColimitsOfSize.{0,0}
      (coyoneda.obj (Opposite.op (SSet.horn (n+1) k : SSet.{u}))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨m, p, hp⟩ := Limits.exists_hom_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) a
  let q : (SSet.horn (n+1) k : SSet.{u}) ⟶ SSet.ex.obj (exStage X m) :=
    p ≫ exComparison.app (exStage X m)
  refine ⟨exHornExtension (by omega) k q ≫ exInfinityInclusion X (m+2), ?_⟩
  erw [← Category.assoc, exHornExtension_restriction, Category.assoc]
  change q ≫ (exComparison.app (exStage X (m+1)) ≫ exInfinityInclusion X ((m+1)+1)) = a
  rw [exInfinityInclusion_step]
  dsimp [q]
  erw [Category.assoc, exInfinityInclusion_step]
  exact hp

lemma exInfinity_kan (X : SSet.{u}) : SSet.KanComplex (exInfinity X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  obtain ⟨φ,hφ⟩ := exInfinity_horn_filling X i hf.desc
  refine ⟨φ, fun j hj => ?_⟩
  have h := congrArg (fun t => SSet.horn.ι i j hj ≫ t) hφ
  simpa only [← Category.assoc, SSet.horn.ι_ι, SSet.horn.IsCompatible.ι_desc] using h

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

noncomputable def exStageMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∀ n, exStage X n ⟶ exStage Y n :=
  Nat.rec f (fun _ g => SSet.ex.map g)

@[simp]
lemma exStageMap_id (X : SSet.{u}) (n : ℕ) : exStageMap (𝟙 X) n = 𝟙 (exStage X n) := by
  induction n with
  | zero => rfl
  | succ n ih => change SSet.ex.map (exStageMap (𝟙 X) n) = _; rw [ih]; exact SSet.ex.map_id _

@[simp]
lemma exStageMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    exStageMap (f ≫ g) n = exStageMap f n ≫ exStageMap g n := by
  induction n with
  | zero => rfl
  | succ n ih => change SSet.ex.map (exStageMap (f ≫ g) n) = _; rw [ih, Functor.map_comp]; rfl

noncomputable def exSequenceMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    exSequence X ⟶ exSequence Y := NatTrans.ofSequence (exStageMap f) (by
  intro n
  dsimp only [exSequence]
  erw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
  exact (exComparison.naturality (exStageMap f n)).symm)

noncomputable def exSequenceFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) where
  obj := exSequence
  map := exSequenceMap
  map_id X := by apply NatTrans.ext; funext n; exact exStageMap_id X n
  map_comp f g := by apply NatTrans.ext; funext n; exact exStageMap_comp f g n

noncomputable def exInfinityFunctor : SSet.{u} ⥤ SSet.{u} := exSequenceFunctor ⋙ colim

@[reassoc]
lemma exInfinityInclusion_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    exInfinityInclusion X n ≫ exInfinityFunctor.map f =
      exStageMap f n ≫ exInfinityInclusion Y n :=
  ι_colimMap (exSequenceMap f) n

noncomputable def exInfinityUnit : 𝟭 SSet.{u} ⟶ exInfinityFunctor where
  app := exInfinityComparison
  naturality {_ _} f := (exInfinityInclusion_naturality f 0).symm

lemma exInfinity_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences (exInfinityFunctor.map f) ↔ simplicialWeakEquivalences f := by
  have he := exInfinityUnit.naturality f
  constructor
  · intro h
    exact simplicialWeakEquivalences.of_postcomp f (exInfinityComparison Y)
      (exInfinityComparison_weak Y)
      (he.symm ▸ simplicialWeakEquivalences.comp_mem _ _ (exInfinityComparison_weak X) h)
  · intro h
    exact simplicialWeakEquivalences.of_precomp (exInfinityComparison X) (exInfinityFunctor.map f)
      (exInfinityComparison_weak X)
      (he ▸ simplicialWeakEquivalences.comp_mem _ _ h (exInfinityComparison_weak Y))

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

instance exStage_preservesLimits (n : ℕ) :
    PreservesLimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := by
  induction n with
  | zero =>
      change PreservesLimits (𝟭 SSet.{u})
      infer_instance
  | succ n ih =>
      let : PreservesLimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := ih
      change PreservesLimits ((exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) ⋙ SSet.ex)
      infer_instance

instance exSequence_preservesLimits : PreservesLimits exSequenceFunctor.{u} :=
  preservesLimits_of_evaluation _ (fun _ => inferInstance)

instance sequentialSSetColim_preservesFiniteLimits :
    PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  apply preservesFiniteLimits_of_evaluation
  intro n
  exact preservesFiniteLimits_of_natIso (preservesColimitNatIso
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)).symm

instance exInfinity_preservesFiniteLimits : PreservesFiniteLimits exInfinityFunctor.{u} := by
  unfold exInfinityFunctor
  infer_instance

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Opposite

instance finiteNonemptyChains (E : Type u) [PartialOrder E] [Finite E] :
    Finite (PartialOrder.NonemptyFiniteChains E) :=
  Finite.of_injective PartialOrder.NonemptyFiniteChains.finset (fun _ _ h =>
    PartialOrder.NonemptyFiniteChains.ext h)

instance finiteOrderNerve (E : Type u) [PartialOrder E] [Finite E] : (nerve E).Finite where
  finite := Finite.of_equiv (PartialOrder.NonemptyFiniteChains E) nerveNondegenerateChains.toEquiv.symm

noncomputable def exEvaluationIso (n : SimplexCategoryᵒᵖ) :
    SSet.ex.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n ≅
      coyoneda.obj (op (SimplexCategory.sd.obj n.unop)) :=
  NatIso.ofComponents (fun _ => Equiv.ulift.toIso) (by intro X Y f; rfl)

instance ex_preservesFilteredColimits : PreservesFilteredColimits SSet.ex.{u} where
  preserves_filtered_colimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    have : SSet.Finite (SimplexCategory.sd.{u}.obj n.unop) := by
      change SSet.Finite (nerve (PartialOrder.NonemptyFiniteChains (ULift (Fin (n.unop.len+1)))))
      infer_instance
    exact preservesColimitsOfShape_of_natIso (exEvaluationIso n).symm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

instance exStage_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := by
  induction n with
  | zero =>
      change PreservesFilteredColimits (𝟭 SSet.{u})
      infer_instance
  | succ n ih =>
      let : PreservesFilteredColimits (exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) := ih
      change PreservesFilteredColimits ((exSequenceFunctor.{u} ⋙ (evaluation ℕ SSet).obj n) ⋙ SSet.ex)
      infer_instance

instance exSequence_preservesFilteredColimits : PreservesFilteredColimits exSequenceFunctor.{u} where
  preserves_filtered_colimits _J _ _ :=
    preservesColimitsOfShape_of_evaluation _ _ (fun _ => inferInstance)

instance exInfinity_preservesFilteredColimits : PreservesFilteredColimits exInfinityFunctor.{u} := by
  unfold exInfinityFunctor
  infer_instance

instance exInfinity_preservesMonomorphisms : exInfinityFunctor.{u}.PreservesMonomorphisms := by
  infer_instance

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance street_preservesFilteredColimits : PreservesFilteredColimits streetNerveFunctor.{u} where
  preserves_filtered_colimits _ _ _ := inferInstance

instance finiteInclusion_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (OmegaCategory.nCategoryInclusion.{u} n) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mp inferInstance

instance streetFinite_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimits (streetNerveFinite.{u} n) := by
  change PreservesFilteredColimits (OmegaCategory.nCategoryInclusion n ⋙ streetNerveFunctor)
  infer_instance

instance thomasonRight_preservesFilteredColimits :
    PreservesFilteredColimits thomasonRight.{u} := by
  unfold thomasonRight
  infer_instance

instance thomasonFiniteRight_preservesFiltered (n : ℕ) :
    PreservesFilteredColimits (thomasonRightFinite.{u} n) := by
  unfold thomasonRightFinite
  infer_instance

instance thomasonRight_finitelyAccessible : Functor.IsFinitelyAccessible.{u} thomasonRight.{u} :=
  Functor.isFinitelyAccessible_iff_preservesFilteredColimits.mpr inferInstance

instance thomasonRightFinite_finitelyAccessible (n : ℕ) :
    Functor.IsFinitelyAccessible.{u} (thomasonRightFinite.{u} n) :=
  Functor.isFinitelyAccessible_iff_preservesFilteredColimits.mpr inferInstance

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance thomasonLeft_finitelyPresentable (X : SSet.{u}) [X.Finite] :
    IsFinitelyPresentable.{u} (thomasonLeft.obj X) :=
  thomasonAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 X

instance thomasonLeftFinite_finitelyPresentable (n : ℕ) (X : SSet.{u}) [X.Finite] :
    IsFinitelyPresentable.{u} ((thomasonLeftFinite n).obj X) :=
  (thomasonFiniteAdjunction n).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 X

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory NormalizedChains DirectedComplex

def topPrism (E : Type u) [PartialOrder E] [OrderTop E] : RelativePrismData E ∅ where
  lowerSet := by intro a b _hab ha; exact ha
  f := OrderHom.id
  g := OrderHom.const E ⊤
  below _ := le_top
  agree _ h := False.elim h
  constant _ _ _ _ := rfl

def posetPointMap (E : Type u) [PartialOrder E] : E →o PUnit.{u+1} :=
  OrderHom.const E PUnit.unit

def posetTopMap (E : Type u) [PartialOrder E] [OrderTop E] : PUnit.{u+1} →o E :=
  OrderHom.const _ ⊤

lemma posetPoint_top (E : Type u) [PartialOrder E] [OrderTop E] :
    (posetPointMap E).comp (posetTopMap E) = OrderHom.id := by ext x

lemma posetTop_point (E : Type u) [PartialOrder E] [OrderTop E] :
    (posetTopMap E).comp (posetPointMap E) = OrderHom.const E ⊤ := rfl

noncomputable def tableTopContraction (E : Type u) [PartialOrder E] [OrderTop E] :
    SSet.Homotopy (𝟙 (streetNerve (complex E).nu))
      (streetNerveMap (complexMap (posetPointMap E)).nu ≫
        streetNerveMap (complexMap (posetTopMap E)).nu) := by
  have H := (topPrism E).tableNerveHomotopy
  change SSet.Homotopy (streetNerveMap (complexMap OrderHom.id).nu)
    (streetNerveMap (complexMap (OrderHom.const E ⊤)).nu) at H
  rw [complexMap_id] at H
  rw [← posetTop_point E, complexMap_comp] at H
  exact H

lemma tablePoint_weakEquivalence (E : Type u) [PartialOrder E] [OrderTop E] :
    simplicialWeakEquivalences (streetNerveMap (complexMap (posetPointMap E)).nu) := by
  apply simplicialWeakEquivalence_of_simplicial_retract _
    (streetNerveMap (complexMap (posetTopMap E)).nu)
  · change streetNerveMap (DirectedComplex.Hom.comp (complexMap (posetTopMap E))
      (complexMap (posetPointMap E))).nu = _
    rw [← complexMap_comp, posetPoint_top, complexMap_id]
    rfl
  · exact tableTopContraction E

lemma tableMap_weakEquivalence_of_top {E D : Type u}
    [PartialOrder E] [OrderTop E] [PartialOrder D] [OrderTop D] (f : E →o D) :
    simplicialWeakEquivalences (streetNerveMap (complexMap f).nu) := by
  apply simplicialWeakEquivalences.of_postcomp _
    (streetNerveMap (complexMap (posetPointMap D)).nu) (tablePoint_weakEquivalence D)
  change simplicialWeakEquivalences (streetNerveMap
    (DirectedComplex.Hom.comp (complexMap f) (complexMap (posetPointMap D))).nu)
  rw [← complexMap_comp]
  exact tablePoint_weakEquivalence E

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

lemma word_length_le_one_of_subsingleton {E : Type u} [PartialOrder E] [Subsingleton E]
    (w : Word E) : w.val.length ≤ 1 := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      have hab : a < b := (List.pairwise_cons.mp hl).1 b (by simp)
      exact False.elim ((ne_of_lt hab) (Subsingleton.elim a b))

lemma grade_pos_zero_of_subsingleton {E : Type u} [PartialOrder E] [Subsingleton E]
    {p : ℕ} (hp : 1 < p) (x : grade (E := E) p) : x = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  change x.val w = 0
  by_contra h
  have he := (mem_grade_iff p x.val).mp x.property w h
  have := word_length_le_one_of_subsingleton w
  omega

instance table_subsingleton {E : Type u} [PartialOrder E] [Subsingleton E] :
    Subsingleton (Table (complex E)) where
  allEq x y := by
    apply Table.ext
    funext p b
    cases p with
    | zero =>
      apply Subtype.ext
      obtain ⟨a, ha⟩ := table_zero_row_vertex x b
      obtain ⟨a', ha'⟩ := table_zero_row_vertex y b
      rw [ha, ha', Subsingleton.elim a a']
    | succ p =>
      exact (grade_pos_zero_of_subsingleton (by omega) _).trans
        (grade_pos_zero_of_subsingleton (by omega) _).symm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits NormalizedChains

noncomputable def tablePointTerminal : IsTerminal (complex PUnit.{u+1}).nu := by
  letI : Subsingleton (complex PUnit.{u+1}).nu.Cell :=
    inferInstanceAs (Subsingleton (DirectedComplex.Table (complex PUnit.{u+1})))
  exact IsTerminal.ofUniqueHom (fun C =>
    { map := fun _ => vertexTable PUnit.unit
      map_source _ _ := Subsingleton.elim _ _
      map_target _ _ := Subsingleton.elim _ _
      map_comp _ _ _ _ _ := Subsingleton.elim _ _ })
    (by intro C F; apply OmegaCategory.Functor.ext; funext x; exact Subsingleton.elim _ _)

noncomputable def tablePointNerveTerminal :
    IsTerminal (streetNerve (complex PUnit.{u+1}).nu) := by
  letI := categorificationAdjunction.{u}.rightAdjoint_preservesLimits
  exact tablePointTerminal.isTerminalObj streetNerveFunctor _

noncomputable def tablePointNerveIso : streetNerve (complex PUnit.{u+1}).nu ≅
    SSet.stdSimplex.obj (SimplexCategory.mk 0) :=
  tablePointNerveTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

lemma tableNerve_terminal_weakEquivalence (E : Type u) [PartialOrder E] [OrderTop E] :
    simplicialWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (streetNerve (complex E).nu)) := by
  have he : SSet.stdSimplex.isTerminalObj₀.from (streetNerve (complex E).nu) =
      streetNerveMap (complexMap (posetPointMap E)).nu ≫ tablePointNerveIso.hom :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _ (tablePoint_weakEquivalence E)
    (simplicialWeakEquivalences.of_isIso _)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex

variable (E : Type u) [PartialOrder E]

def orderULiftUp : E →o ULift.{v} E where
  toFun := ULift.up
  monotone' _ _ h := h

def orderULiftDown : ULift.{v} E →o E where
  toFun := ULift.down
  monotone' _ _ h := h

lemma orderULiftUp_down : (orderULiftDown.{u,v} E).comp (orderULiftUp E) = OrderHom.id := rfl
lemma orderULiftDown_up : (orderULiftUp.{u,v} E).comp (orderULiftDown E) = OrderHom.id := by
  ext x
  cases x
  rfl

noncomputable def complexULiftIso : OmegaCategory.ulift.{u,v} (complex E).nu ≅
    (complex (ULift.{v} E)).nu where
  hom := OmegaCategory.Functor.comp (OmegaCategory.uliftDown _)
    (complexMap (orderULiftUp E)).nu
  inv := OmegaCategory.Functor.comp (complexMap (orderULiftDown E)).nu
    (OmegaCategory.uliftUp _)
  hom_inv_id := by
    apply OmegaCategory.Functor.ext
    funext x
    have he : DirectedComplex.Hom.comp (complexMap (orderULiftUp.{u,v} E))
        (complexMap (orderULiftDown E)) = DirectedComplex.Hom.id (complex E) := by
      rw [← complexMap_comp, orderULiftUp_down, complexMap_id]
    have h := congrArg (fun f => f.nu.map x.down) he
    change ULift.up ((complexMap (orderULiftDown E)).nu.map
      ((complexMap (orderULiftUp E)).nu.map x.down)) = x
    change (complexMap (orderULiftDown E)).nu.map
      ((complexMap (orderULiftUp E)).nu.map x.down) = x.down at h
    exact congrArg ULift.up h
  inv_hom_id := by
    apply OmegaCategory.Functor.ext
    funext x
    have he : DirectedComplex.Hom.comp (complexMap (orderULiftDown.{u,v} E))
        (complexMap (orderULiftUp E)) = DirectedComplex.Hom.id (complex (ULift.{v} E)) := by
      rw [← complexMap_comp, orderULiftDown_up, complexMap_id]
    exact congrArg (fun f => f.nu.map x) he

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits NormalizedChains

noncomputable def categorificationSimplexIso (n : SimplexCategory) :
    categorification.{u}.obj (SSet.stdSimplex.obj n) ≅ raisedOrientals.obj n :=
  ((asIso ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals.{u})).symm).app n

lemma raisedOriental_terminal_weakEquivalence (n : SimplexCategory) :
    simplicialWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (streetNerve (raisedOrientals.{u}.obj n))) := by
  let e : raisedOrientals.{u}.obj n ≅ (complex (ULift.{u} (Fin (n.len+1)))).nu :=
    complexULiftIso (Fin (n.len+1))
  have he : SSet.stdSimplex.isTerminalObj₀.from (streetNerve (raisedOrientals.obj n)) =
      streetNerveFunctor.map e.hom ≫ SSet.stdSimplex.isTerminalObj₀.from _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _
    (simplicialWeakEquivalences.of_isIso (streetNerveFunctor.mapIso e).hom)
    (tableNerve_terminal_weakEquivalence (ULift.{u} (Fin (n.len+1))))

lemma categorificationSimplex_terminal_weakEquivalence (n : SimplexCategory) :
    simplicialWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (streetNerve (categorification.{u}.obj (SSet.stdSimplex.obj n)))) := by
  have he : SSet.stdSimplex.isTerminalObj₀.from
      (streetNerve (categorification.obj (SSet.stdSimplex.obj n))) =
      streetNerveFunctor.map (categorificationSimplexIso n).hom ≫
        SSet.stdSimplex.isTerminalObj₀.from _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _
    (simplicialWeakEquivalences.of_isIso
      (streetNerveFunctor.mapIso (categorificationSimplexIso n)).hom)
    (raisedOriental_terminal_weakEquivalence n)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits Simplicial MonoidalCategory PartialOrder

variable (E : Type u) [PartialOrder E] [OrderTop E]

noncomputable def nerveTopSimplex {n : ℕ} (s : (nerve E) _⦋n⦌)
    (θ : Fin (n+1) →o Fin 2) : Fin (n+1) →o E where
  toFun i := if θ i = 0 then s.obj i else ⊤
  monotone' i j hij := by
    classical
    by_cases hj : θ j = 0
    · have hi : θ i = 0 := by
        apply le_antisymm
        · simpa only [hj] using θ.monotone hij
        · exact Fin.zero_le _
      simpa only [hi, hj, ite_true] using s.monotone hij
    · simp only [hj, ite_false]
      exact le_top

noncomputable def nerveTopVertex : (Δ[0] : SSet.{u}) ⟶ nerve E where
  app m := ↾fun _ => (OrderHom.const (Fin (m.unop.len+1)) (⊤ : E)).monotone.functor
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    rfl

noncomputable def nerveTopCylinder : nerve E ⊗ Δ[1] ⟶ nerve E where
  app m := ↾fun x => (nerveTopSimplex E x.1
    (SSet.stdSimplex.objEquiv x.2).toOrderHom).monotone.functor
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    rfl

noncomputable def nerveTopHomotopy : SSet.Homotopy (𝟙 (nerve E))
    (SSet.stdSimplex.isTerminalObj₀.from (nerve E) ≫ nerveTopVertex E) where
  h := nerveTopCylinder E
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    change (if (0 : Fin 2) = 0 then x.obj i else ⊤) = x.obj i
    simp
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    change (if (1 : Fin 2) = 0 then x.obj i else ⊤) = ⊤
    simp
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, θ⟩
    exact False.elim hx

lemma nerveTop_terminal_weakEquivalence :
    simplicialWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve E)) :=
  simplicialWeakEquivalence_of_simplicial_retract _ (nerveTopVertex E)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _) (nerveTopHomotopy E)

lemma standardSimplex_terminal_weakEquivalence (n : ℕ) :
    simplicialWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) := by
  have he : SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) =
      (SSet.stdSimplex.isoNerve n).hom ≫ SSet.stdSimplex.isTerminalObj₀.from _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _ (simplicialWeakEquivalences.of_isIso _)
    (nerveTop_terminal_weakEquivalence (ULift.{u} (Fin (n+1))))

lemma categorificationUnit_simplex_weakEquivalence (n : SimplexCategory) :
    simplicialWeakEquivalences (categorificationAdjunction.{u}.unit.app
      (SSet.stdSimplex.obj n)) := by
  apply simplicialWeakEquivalences.of_postcomp _ (SSet.stdSimplex.isTerminalObj₀.from _)
    (categorificationSimplex_terminal_weakEquivalence n)
  have he : categorificationAdjunction.{u}.unit.app (SSet.stdSimplex.obj n) ≫
      SSet.stdSimplex.isTerminalObj₀.from _ =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply (congrArg (fun (f : SSet.stdSimplex.obj n ⟶ (Δ[0] : SSet.{u})) =>
    simplicialWeakEquivalences f) he).mpr
  cases n
  exact standardSimplex_terminal_weakEquivalence _

end Thomason

end

end OAI
