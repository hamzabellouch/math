import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Gray.TopologicalIntervalCylinder
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.StrongGenerator

namespace OAI

section

/-! # Extracting chains from actual oriental-valued simplices

The normalized-chain presentation identifies strict maps from an oriental
to a directed realization with positive augmented chain maps. This uses the
atom-generation premise.
-/

namespace Thomason.Construction.SimplexAtomsInput

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex

noncomputable section

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- The positive chain map represented by an actual Street simplex. -/
def chainOfSimplex {K : DirectedComplex.{0}} {m : ℕ}
    (F : h.object m ⟶ K.realization) :
    (directedComplex m (h.squared m)) ⟶ K :=
  Hom.comp (a.fromSimplexChains m) (StrictOmegaCategory.Abelianization.evaluateHom F)

/-- Realizing this extracted chain map recovers the entire strict functor. -/
theorem chainOfSimplex_realization {K : DirectedComplex.{0}} {m : ℕ}
    (F : h.object m ⟶ K.realization) :
    (a.chainOfSimplex F).realization = F := by
  change (a.fromSimplexChains m).realization ≫
    (StrictOmegaCategory.Abelianization.evaluateHom F).realization = F
  rw [← a.unit_eq_realized_inverse m]
  exact StrictOmegaCategory.Abelianization.unit_evaluate F

/-- Extraction respects precomposition by every simplex operator. -/
theorem chainOfSimplex_precomp {K : DirectedComplex.{0}} {l m : ℕ}
    (f : Fin (l+1) →o Fin (m+1)) (F : h.object m ⟶ K.realization) :
    a.chainOfSimplex (h.map f ≫ F) = Hom.comp
      (directedMap (h.squared l) (h.squared m) f (h.naturality f))
        (a.chainOfSimplex F) := by
  let b : directedComplex l (h.squared l) ⟶
      StrictOmegaCategory.Abelianization.complex (h.object l) := a.fromSimplexChains l
  let c : directedComplex m (h.squared m) ⟶
      StrictOmegaCategory.Abelianization.complex (h.object m) := a.fromSimplexChains m
  let u : directedComplex l (h.squared l) ⟶ directedComplex m (h.squared m) :=
    directedMap (h.squared l) (h.squared m) f (h.naturality f)
  let v : StrictOmegaCategory.Abelianization.complex (h.object l) ⟶
      StrictOmegaCategory.Abelianization.complex (h.object m) :=
    StrictOmegaCategory.Abelianization.map (h.map f)
  let q : StrictOmegaCategory.Abelianization.complex (h.object m) ⟶ K :=
    StrictOmegaCategory.Abelianization.evaluateHom F
  have hn : u ≫ c = b ≫ v :=
    a.abelianizationCosimplicialIso.inv.naturality (SimplexCategory.Hom.mk f)
  change b ≫ StrictOmegaCategory.Abelianization.evaluateHom (h.map f ≫ F) =
    u ≫ (c ≫ q)
  calc
    _ = b ≫ (v ≫ q) := congrArg (fun z => b ≫ z)
      (StrictOmegaCategory.Abelianization.evaluate_naturality (h.map f) F).symm
    _ = (b ≫ v) ≫ q := (Category.assoc _ _ _).symm
    _ = (u ≫ c) ≫ q := congrArg (fun z => z ≫ q) hn.symm
    _ = _ := Category.assoc _ _ _

/-- Extraction respects postcomposition by positive chain maps. -/
theorem chainOfSimplex_postcomp {K L : DirectedComplex.{0}} {m : ℕ}
    (F : h.object m ⟶ K.realization) (g : K ⟶ L) :
    a.chainOfSimplex (F ≫ g.realization) = a.chainOfSimplex F ≫ g := by
  have he : StrictOmegaCategory.Abelianization.evaluateHom (F ≫ g.realization) =
      Hom.comp (StrictOmegaCategory.Abelianization.evaluateHom F) g := by
    apply DirectedComplex.Hom.ext_app
    intro p z
    have hp : StrictOmegaCategory.Abelianization.evaluate (F ≫ g.realization) p =
        (g.app p).comp (StrictOmegaCategory.Abelianization.evaluate F p) := by
      apply StrictOmegaCategory.Abelianization.hom_ext
      intro x
      simp only [AddMonoidHom.comp_apply,
        StrictOmegaCategory.Abelianization.evaluate_generator]
      rfl
    exact DFunLike.congr_fun hp z
  change a.fromSimplexChains m ≫ _ = (a.fromSimplexChains m ≫ _) ≫ g
  rw [he, Category.assoc]
  rfl

end

end Thomason.Construction.SimplexAtomsInput

end

section

/-! # Weak-equivalence gluing for actual full Street covers

The three local maps are strict functors into the two full pieces and
their full intersection. Their composites with the original inclusions
must be the specified global map. The actual Street subcomplex and
simplicial gluing theorem then prove its Street equivalence.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- The local-to-global weak-equivalence bridge for an actual full cover. -/
theorem weakEquivalence_of_fullStreet_cover
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    {X C : StrictOmegaCategory.{0}} (S T : Set C)
    (hc : h.fullStreetSubcomplex C S ⊔ h.fullStreetSubcomplex C T = ⊤)
    (f : X ⟶ C) (fS : X ⟶ C.fullOn S) (fT : X ⟶ C.fullOn T)
    (fI : X ⟶ C.fullOn (S ∩ T))
    (hS : fS ≫ C.fullInclusion S = f) (hT : fT ≫ C.fullInclusion T = f)
    (hI : fI ≫ C.fullInclusion (S ∩ T) = f)
    (wS : h.streetWeakEquivalences fS) (wT : h.streetWeakEquivalences fT)
    (wI : h.streetWeakEquivalences fI) : h.streetWeakEquivalences f := by
  have := kq.weakEquivalences_retracts
  let s := h.fullStreetSubcomplex C S
  let t := h.fullStreetSubcomplex C T
  let u := h.fullStreetSubcomplex C (S ∩ T)
  let i : u.toSSet ⟶ s.toSSet := SSet.Subcomplex.homOfLE
    (show u ≤ s from fun _ _ hf x => ⟨(hf x).1.1, (hf x).2.1⟩)
  let j : u.toSSet ⟶ t.toSSet := SSet.Subcomplex.homOfLE
    (show u ≤ t from fun _ _ hf x => ⟨(hf x).1.2, (hf x).2.2⟩)
  let aS := h.streetNerve.map fS ≫ (h.fullStreetIso C S).hom
  let aT := h.streetNerve.map fT ≫ (h.fullStreetIso C T).hom
  let aI := h.streetNerve.map fI ≫ (h.fullStreetIso C (S ∩ T)).hom
  have haS : aS ≫ s.ι = h.streetNerve.map f := by
    dsimp [aS, s]
    rw [Category.assoc, h.fullStreetIso_hom_ι, ← h.streetNerve.map_comp, hS]
  have haT : aT ≫ t.ι = h.streetNerve.map f := by
    dsimp [aT, t]
    rw [Category.assoc, h.fullStreetIso_hom_ι, ← h.streetNerve.map_comp, hT]
  have haI : aI ≫ u.ι = h.streetNerve.map f := by
    dsimp [aI, u]
    rw [Category.assoc, h.fullStreetIso_hom_ι, ← h.streetNerve.map_comp, hI]
  have hi : aI ≫ i = aS := by
    apply (cancel_mono s.ι).mp
    change (aI ≫ i) ≫ s.ι = aS ≫ s.ι
    rw [Category.assoc]
    exact haI.trans haS.symm
  have hj : aI ≫ j = aT := by
    apply (cancel_mono t.ι).mp
    change (aI ≫ j) ≫ t.ι = aT ≫ t.ι
    rw [Category.assoc]
    exact haI.trans haT.symm
  have wS' : realizationWeakEquivalences aS :=
    realizationWeakEquivalences.comp_mem _ _ wS
      (realizationWeakEquivalences.of_isIso _)
  have wT' : realizationWeakEquivalences aT :=
    realizationWeakEquivalences.comp_mem _ _ wT
      (realizationWeakEquivalences.of_isIso _)
  have wI' : realizationWeakEquivalences aI :=
    realizationWeakEquivalences.comp_mem _ _ wI
      (realizationWeakEquivalences.of_isIso _)
  exact g.common_source (h.fullStreetSubcomplex_isPushout C S T hc)
    aI aS aT (h.streetNerve.map f) hi hj haS haT wI' wS' wT'

/-- In particular the hypotheses on the cover can be checked on objects
using the original binary labels of two full sieves. -/
theorem weakEquivalence_of_sieveStreet_cover
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {X C : StrictOmegaCategory.{0}} (p q : C ⟶ StrictPoset.category (Fin 2))
    (hc : ∀ x : Objects C, p.toFun x.val = StrictPoset.identity 0 ∨
      q.toFun x.val = StrictPoset.identity 0)
    (f : X ⟶ C) (fS : X ⟶ labelFiber p 0) (fT : X ⟶ labelFiber q 0)
    (fI : X ⟶ C.fullOn
      ({x | p.toFun x = StrictPoset.identity 0} ∩ {x | q.toFun x = StrictPoset.identity 0}))
    (hS : fS ≫ labelFiberInclusion p 0 = f) (hT : fT ≫ labelFiberInclusion q 0 = f)
    (hI : fI ≫ C.fullInclusion _ = f)
    (wS : h.streetWeakEquivalences fS) (wT : h.streetWeakEquivalences fT)
    (wI : h.streetWeakEquivalences fI) : h.streetWeakEquivalences f :=
  h.weakEquivalence_of_fullStreet_cover g kq _ _ (h.sieve_street_cover p q hc)
    f fS fT fI hS hT hI wS wT wI

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Local finite presentability of strict omega-categories

The actual finite globes are finitely presentable, form a small strong
generator, and the required small colimits have already been constructed.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance globeCoyoneda_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op (Globe.category n))) where
  preserves_filtered_colimits _J := inferInstance

instance globe_finitelyPresentable (n : ℕ) : IsFinitelyPresentable.{0} (Globe.category n) :=
  isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr inferInstance

instance locallyFinitelyPresentable : IsCardinalLocallyPresentable.{0} StrictOmegaCategory.{0}
    Cardinal.aleph0 := by
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator _ _).mpr
  refine ⟨globes, inferInstance, globes_isStrongGenerator, ?_⟩
  rintro _ ⟨n⟩
  exact globe_finitelyPresentable n

instance locallyPresentable : IsLocallyPresentable.{0} StrictOmegaCategory.{0} where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance⟩

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Strict categories with finitely many cells are finitely presentable

A finite cell family and its finitely many nontrivial face and composition
equations descend to one stage of a filtered diagram. Above a uniform
dimension bound the equations are identities.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem finite_cells_dimension_bound (C : StrictOmegaCategory.{0}) [Finite C] :
    ∃ N, ∀ x : C, C.DimensionLE N x := by
  classical
  let := Fintype.ofFinite C
  choose n hn using C.finite_dimension
  refine ⟨Finset.univ.sup n, fun x => C.dimensionLE_mono ?_ (hn x)⟩
  exact Finset.le_sup (f := n) (Finset.mem_univ x)

theorem comp_self_of_dimensionLE (C : StrictOmegaCategory.{0}) {n : ℕ} {x : C}
    (hx : C.DimensionLE n x) (h : C.target n x = C.source n x) :
    C.comp n x x h = x := by
  have hh : C.target n (C.source n x) = C.source n x := by rw [hx.1, hx.2]
  simpa only [hx.1] using C.left_unit n x hh

namespace FilteredColimit

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0}) [IsFiltered J]

theorem finite_representatives {A : Type} [Finite A] (x : A → Carrier F) :
    ∃ (j : J) (v : A → F.obj j), ∀ a, ι F j (v a) = x a := by
  classical
  let := Fintype.ofFinite A
  let e := Fintype.equivFin A
  obtain ⟨j, v, hv⟩ := exists_representatives_fin F (Fintype.card A)
    (fun i => x (e.symm i))
  exact ⟨j, fun a => v (e a), fun a => by simpa using hv (e a)⟩

theorem finite_equations {A : Type} [Finite A] {j : J} (x y : A → F.obj j)
    (h : ∀ a, ι F j (x a) = ι F j (y a)) :
    ∃ (k : J) (f : j ⟶ k), ∀ a, (F.map f).toFun (x a) = (F.map f).toFun (y a) := by
  classical
  let := Fintype.ofFinite A
  let e := Fintype.equivFin A
  obtain ⟨k, f, hf⟩ := eventually_eq_fin F (Fintype.card A)
    (fun i => x (e.symm i)) (fun i => y (e.symm i)) (fun i => h (e.symm i))
  exact ⟨k, f, fun a => by simpa using hf (e a)⟩

/-- A finite strict functor into the constructed colimit descends exactly. -/
theorem finite_hom_descends (C : StrictOmegaCategory.{0}) [Finite C]
    (f : C ⟶ category F) :
    ∃ (j : J) (g : C ⟶ F.obj j), g ≫ leg F j = f := by
  classical
  obtain ⟨N, hN⟩ := finite_cells_dimension_bound C
  obtain ⟨j, v, hv⟩ := finite_representatives F f.toFun
  let A := Bool × Fin (N + 1) × C
  have he (a : A) :
      ι F j (v (C.face a.1 a.2.1 a.2.2)) =
        ι F j ((F.obj j).face a.1 a.2.1 (v a.2.2)) := by
    rw [hv, ← face_ι, hv]
    exact f.map_face _ _ _
  obtain ⟨k, u, hu⟩ := finite_equations F _ _ he
  let w : C → F.obj k := fun x => (F.map u).toFun (v x)
  have hw (x : C) : ι F k (w x) = f.toFun x := (ι_map F u (v x)).trans (hv x)
  have wf (a : Bool) (n : ℕ) (hn : n ≤ N) (x : C) :
      w (C.face a n x) = (F.obj k).face a n (w x) := by
    exact (hu (a, ⟨n, by omega⟩, x)).trans ((F.map u).map_face a n (v x))
  have wd (x : C) : (F.obj k).DimensionLE N (w x) := by
    constructor
    · change (F.obj k).face false N (w x) = w x
      rw [← wf false N le_rfl x]
      exact congrArg w (hN x).1
    · change (F.obj k).face true N (w x) = w x
      rw [← wf true N le_rfl x]
      exact congrArg w (hN x).2
  let B := {b : Fin (N + 1) × C × C // C.target b.1 b.2.1 = C.source b.1 b.2.2}
  have wm (b : B) : (F.obj k).target b.val.1 (w b.val.2.1) =
      (F.obj k).source b.val.1 (w b.val.2.2) := by
    change (F.obj k).face true b.val.1 (w b.val.2.1) =
      (F.obj k).face false b.val.1 (w b.val.2.2)
    rw [← wf true _ (Nat.le_of_lt_succ b.val.1.isLt),
      ← wf false _ (Nat.le_of_lt_succ b.val.1.isLt)]
    exact congrArg w b.property
  let lhs : B → F.obj k := fun b =>
    w (C.comp b.val.1 b.val.2.1 b.val.2.2 b.property)
  let rhs : B → F.obj k := fun b =>
    (F.obj k).comp b.val.1 (w b.val.2.1) (w b.val.2.2) (wm b)
  have hc (b : B) : ι F k (lhs b) = ι F k (rhs b) := by
    dsimp only [lhs, rhs]
    have hmstage : face F true b.val.1 (ι F k (w b.val.2.1)) =
        face F false b.val.1 (ι F k (w b.val.2.2)) := by
      rw [face_ι, face_ι]
      exact congrArg (ι F k) (wm b)
    rw [hw, ← comp_ι F b.val.1 k (w b.val.2.1) (w b.val.2.2) (wm b) hmstage]
    have hm : (category F).target b.val.1 (f.toFun b.val.2.1) =
        (category F).source b.val.1 (f.toFun b.val.2.2) :=
      (f.map_face true _ _).symm.trans
        ((congrArg f.toFun b.property).trans (f.map_face false _ _))
    change f.toFun (C.comp b.val.1 b.val.2.1 b.val.2.2 b.property) =
      (category F).comp b.val.1 (ι F k (w b.val.2.1)) (ι F k (w b.val.2.2)) _
    simpa only [hw] using f.map_comp _ _ _ b.property hm
  obtain ⟨l, q, hq⟩ := finite_equations F lhs rhs hc
  let z : C → F.obj l := fun x => (F.map q).toFun (w x)
  have zf (a : Bool) (n : ℕ) (hn : n ≤ N) (x : C) :
      z (C.face a n x) = (F.obj l).face a n (z x) := by
    exact (congrArg (F.map q).toFun (wf a n hn x)).trans ((F.map q).map_face a n (w x))
  have zd (x : C) : (F.obj l).DimensionLE N (z x) := (F.map q).dimensionLE (wd x)
  have zface (a : Bool) (n : ℕ) (x : C) :
      z (C.face a n x) = (F.obj l).face a n (z x) := by
    by_cases hn : n ≤ N
    · exact zf a n hn x
    · have hcn := C.dimensionLE_mono (by omega : N ≤ n) (hN x)
      have hzn := (F.obj l).dimensionLE_mono (by omega : N ≤ n) (zd x)
      cases a <;> simp only [hcn.1, hcn.2, hzn.1, hzn.2]
  let g : C ⟶ F.obj l := {
    toFun := z
    map_face := zface
    map_comp := by
      intro n x y h h'
      by_cases hn : n ≤ N
      · let b : B := ⟨(⟨n, by omega⟩, x, y), h⟩
        exact (hq b).trans ((F.map q).map_comp n (w x) (w y) (wm b) h')
      · have hcnx := C.dimensionLE_mono (by omega : N ≤ n) (hN x)
        have hcny := C.dimensionLE_mono (by omega : N ≤ n) (hN y)
        have hxy : x = y := hcnx.2.symm.trans (h.trans hcny.1)
        subst y
        have hzn := (F.obj l).dimensionLE_mono (by omega : N ≤ n) (zd x)
        rw [comp_self_of_dimensionLE C hcnx h,
          comp_self_of_dimensionLE (F.obj l) hzn h'] }
  refine ⟨l, g, ?_⟩
  apply Hom.ext
  funext x
  exact (ι_map F q (w x)).trans (hw x)

noncomputable def finiteHomIsColimit (C : StrictOmegaCategory.{0}) [Finite C] :
    IsColimit ((coyoneda.obj (Opposite.op C)).mapCocone (cocone F)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro f
    obtain ⟨j, g, hg⟩ := finite_hom_descends F C f
    exact ⟨j, g, hg.symm⟩
  · intro j f g hfg
    change C ⟶ F.obj j at f g
    have he (x : C) : ι F j (f.toFun x) = ι F j (g.toFun x) := by
      exact congrArg (fun h : C ⟶ category F => h.toFun x) hfg
    obtain ⟨k, u, hu⟩ := finite_equations F f.toFun g.toFun he
    refine ⟨k, u, ?_⟩
    apply Hom.ext
    funext x
    exact hu x

end FilteredColimit

instance finiteCellsCoyoneda_preservesFilteredColimitsOfShape
    (C : StrictOmegaCategory.{0}) [Finite C] {J : Type} [Category.{0} J] [IsFiltered J] :
    PreservesColimitsOfShape J (coyoneda.obj (Opposite.op C)) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (FilteredColimit.isColimit F) (FilteredColimit.finiteHomIsColimit F C)

instance finiteCellsCoyoneda_preservesFilteredColimits
    (C : StrictOmegaCategory.{0}) [Finite C] :
    PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op C)) where
  preserves_filtered_colimits _J := inferInstance

instance finiteCells_finitelyPresentable (C : StrictOmegaCategory.{0}) [Finite C] :
    IsFinitelyPresentable.{0} C :=
  isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr inferInstance

end

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Finitely many cells in each actual oriental

The sum of the vertex indices defines a nonnegative weight on each basis.
Its value on every positive-dimensional basis boundary is strictly positive.
Consequently augmentation one bounds all entries of a globular table.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

noncomputable section

private theorem alternating_nonneg {n : ℕ} (f : Fin n → ℤ)
    (hf : Antitone f) (hn : ∀ i, 0 ≤ f i) :
    0 ≤ ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) * f i := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hn 0
  | more n ih _ =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have ht := ih (fun i => f i.succ.succ)
      (fun i j hij => hf (Fin.succ_le_succ_iff.mpr (Fin.succ_le_succ_iff.mpr hij)))
      (fun i => hn _)
    have h01 : f (Fin.succ (0 : Fin (n+1))) ≤ f 0 := hf (Fin.zero_le _)
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at *
    have he : (∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) * -1 * -1 * f i.succ.succ) =
        ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) * f i.succ.succ := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    linarith

def vertexWeight {m p : ℕ} (s : Basis m p) : ℤ := ∑ i : Fin (p + 1), (s i : ℕ)

def chainWeight (m p : ℕ) : Chains m p →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ vertexWeight

def chainMass (m p : ℕ) : Chains m p →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem chainWeight_single {m p : ℕ} (s : Basis m p) (z : ℤ) :
    chainWeight m p (Finsupp.single s z) = z * vertexWeight s := by
  simp [chainWeight]

@[simp] theorem chainMass_single {m p : ℕ} (s : Basis m p) (z : ℤ) :
    chainMass m p (Finsupp.single s z) = z := by
  simp [chainMass]

theorem vertexWeight_nonneg {m p : ℕ} (s : Basis m p) : 0 ≤ vertexWeight s :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem vertexWeight_le {m p : ℕ} (s : Basis m p) :
    vertexWeight s ≤ (p + 1 : ℕ) * (m : ℤ) := by
  calc
    vertexWeight s ≤ ∑ _i : Fin (p + 1), (m : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast Nat.le_of_lt_succ (s i).isLt
    _ = _ := by simp

theorem vertexWeight_delete {m p : ℕ} (s : Basis m (p + 1)) (i : Fin (p + 2)) :
    vertexWeight (deleteVertex s i) = vertexWeight s - (s i : ℕ) := by
  have h := Fin.sum_univ_succAbove (fun j => (s j : ℤ)) i
  change (∑ j : Fin (p+1), (s (i.succAbove j) : ℤ)) = _
  dsimp only [vertexWeight] at h ⊢
  linarith

theorem boundary_weight_positive {m p : ℕ} (s : Basis m (p + 1)) :
    1 ≤ chainWeight m p (differentialBasis m p s) := by
  have hf : StrictAnti (fun i : Fin (p + 2) => vertexWeight (deleteVertex s i)) := by
    intro i j hij
    dsimp only
    rw [vertexWeight_delete, vertexWeight_delete]
    have hs : (s i : ℤ) < (s j : ℤ) := by exact_mod_cast s.strictMono hij
    linarith
  have hn (i : Fin (p + 2)) : 0 ≤ vertexWeight (deleteVertex s i) :=
    vertexWeight_nonneg _
  have ht := alternating_nonneg
    (fun i : Fin p => vertexWeight (deleteVertex s i.succ.succ))
    (fun i j hij => hf.antitone (Fin.succ_le_succ_iff.mpr (Fin.succ_le_succ_iff.mpr hij)))
    (fun i => hn _)
  have h01 : vertexWeight (deleteVertex s (Fin.succ (0 : Fin (p+1)))) <
      vertexWeight (deleteVertex s 0) := hf (Fin.succ_pos _)
  rw [differentialBasis, map_sum]
  simp only [chainWeight_single]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at *
  have he : (∑ i : Fin p, (-1 : ℤ) ^ (i : ℕ) * -1 * -1 *
      vertexWeight (deleteVertex s i.succ.succ)) =
      ∑ i : Fin p, (-1 : ℤ) ^ (i : ℕ) * vertexWeight (deleteVertex s i.succ.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

theorem chainWeight_nonneg {m p : ℕ} {x : Chains m p} (hx : x ∈ positive m p) :
    0 ≤ chainWeight m p x := by
  classical
  simp only [chainWeight, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hx s) (vertexWeight_nonneg s))

theorem chainMass_nonneg {m p : ℕ} {x : Chains m p} (hx : x ∈ positive m p) :
    0 ≤ chainMass m p x := by
  classical
  simp only [chainMass, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one]
  exact Finset.sum_nonneg (fun s _ => hx s)

theorem coefficient_le_mass {m p : ℕ} {x : Chains m p} (hx : x ∈ positive m p)
    (s : Basis m p) : x s ≤ chainMass m p x := by
  classical
  by_cases hs : x s = 0
  · rw [hs]
    exact chainMass_nonneg hx
  · simp only [chainMass, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one]
    exact Finset.single_le_sum (fun t _ => hx t) (Finsupp.mem_support_iff.mpr hs)

theorem chainWeight_le_mass {m p : ℕ} {x : Chains m p} (hx : x ∈ positive m p) :
    chainWeight m p x ≤ ((p + 1 : ℕ) * (m : ℤ)) * chainMass m p x := by
  classical
  simp only [chainWeight, chainMass, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simpa only [mul_one, one_mul, mul_comm] using
    mul_le_mul_of_nonneg_left (vertexWeight_le s) (hx s)

theorem chainMass_le_boundaryWeight {m p : ℕ} {x : Chains m (p+1)}
    (hx : x ∈ positive m (p+1)) : chainMass m (p+1) x ≤ chainWeight m p (differential m p x) := by
  classical
  have he : (chainWeight m p).comp (differential m p) =
      Finsupp.linearCombination ℤ (fun s => chainWeight m p (differentialBasis m p s)) := by
    ext s
    simp
  change chainMass m (p+1) x ≤ ((chainWeight m p).comp (differential m p)) x
  rw [he]
  simp only [chainMass, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one]
  apply Finset.sum_le_sum
  intro s _
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (boundary_weight_positive s) (hx s)

def tableMassBound (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | p+1 => (p+1) * m * tableMassBound m p

theorem cell_mass_le {m : ℕ} {hsq : BoundarySquared m}
    (x : DirectedComplex.Cell (directedComplex m hsq)) (a : Bool) (p : ℕ) :
    chainMass m p (x.table a p) ≤ tableMassBound m p := by
  induction p generalizing a with
  | zero =>
    have he : chainMass m 0 = augmentation m := rfl
    rw [he]
    exact le_of_eq (x.augmentation a)
  | succ p ih =>
    have hb := chainMass_le_boundaryWeight (x.positive a (p+1))
    change chainMass m (p+1) (x.table a (p+1)) ≤
      chainWeight m p ((directedComplex m hsq).differential p (x.table a (p+1))) at hb
    rw [x.boundary, map_sub] at hb
    have hn := chainWeight_nonneg (x.positive false p)
    have hw := chainWeight_le_mass (x.positive true p)
    have hi := mul_le_mul_of_nonneg_left (ih true)
      (show 0 ≤ (p+1 : ℕ) * (m : ℤ) by positivity)
    simpa only [tableMassBound, Nat.cast_mul] using
      hb.trans ((sub_le_self _ hn).trans (hw.trans hi))

theorem cell_coefficient_bounds {m : ℕ} {hsq : BoundarySquared m}
    (x : DirectedComplex.Cell (directedComplex m hsq)) (a : Bool) (p : ℕ) (s : Basis m p) :
    0 ≤ x.table a p s ∧ x.table a p s ≤ tableMassBound m p :=
  ⟨x.positive a p s, (coefficient_le_mass (x.positive a p) s).trans (cell_mass_le x a p)⟩

def finiteCellCode {m : ℕ} {hsq : BoundarySquared m}
    (x : DirectedComplex.Cell (directedComplex m hsq)) :
    (a : Bool) → (p : Fin (m+1)) → Basis m p → Fin (tableMassBound m p + 1) :=
  fun a p s => ⟨(x.table a p s).toNat, by
    have h := cell_coefficient_bounds x a p s
    omega⟩

theorem finiteCellCode_injective {m : ℕ} {hsq : BoundarySquared m} :
    Function.Injective (@finiteCellCode m hsq) := by
  intro x y h
  apply DirectedComplex.Cell.ext
  funext a p
  by_cases hp : p ≤ m
  · apply Finsupp.ext
    intro s
    have he := congrArg (fun c => (c a ⟨p, by omega⟩ s).val) h
    have hx := (cell_coefficient_bounds x a p s).1
    have hy := (cell_coefficient_bounds y a p s).1
    dsimp only [finiteCellCode] at he
    omega
  · exact (NormalizedSimplexIdentities.chains_eq_zero_above (by omega) _).trans
      (NormalizedSimplexIdentities.chains_eq_zero_above (by omega) _).symm

instance oriental_finite (m : ℕ) (hsq : BoundarySquared m) : Finite (oriental m hsq) :=
  Finite.of_injective finiteCellCode finiteCellCode_injective

instance oriental_finitelyPresentable (m : ℕ) (hsq : BoundarySquared m) :
    CategoryTheory.IsFinitelyPresentable.{0} (oriental m hsq) := inferInstance

end

end Thomason.Construction.SimplexComplex

end

end OAI
