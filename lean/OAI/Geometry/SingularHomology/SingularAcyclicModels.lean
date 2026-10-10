import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyConstant

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace Problem340.SingularAcyclicModels

abbrev singularFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat ℝ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)

abbrev degree (n : ℕ) : TopCat.{0} ⥤ ModuleCat ℝ :=
  ((Functor.postcompose₂.obj
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n)).obj
      (singularChainComplexFunctor (ModuleCat ℝ))).obj (ModuleCat.of ℝ ℝ)

abbrev complex : ChainComplex (TopCat.{0} ⥤ ModuleCat ℝ) ℕ where
  X := degree
  d i j :=
    { app X := (singularFunctor.obj X).d i j
      naturality X Y f := (singularFunctor.map f).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext X
    exact (singularFunctor.obj X).shape i j hij
  d_comp_d' i j k hij hjk := by
    apply NatTrans.ext
    funext X
    exact (singularFunctor.obj X).d_comp_d i j k

abbrev model (n : ℕ) : TopCat.{0} := SimplexCategory.toTop.obj ⦋n⦌

instance contractible_model (n : ℕ) : ContractibleSpace (model n) := by
  let : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    RealSimplex.contractible
  change ContractibleSpace (ULift (Convexity.StdSimplex ℝ (Fin (n + 1))))
  exact Homeomorph.ulift.contractibleSpace

lemma model_exact (n k : ℕ) : (singularFunctor.obj (model n)).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact realSingularHomology_subsingleton_of_contractible (k + 1) (by omega) (model n)

def liftCycle (n k : ℕ) (φ : complex.X n ⟶ complex.X (k + 1))
    (hφ : φ ≫ complex.d (k + 1) k = 0) :
    complex.X n ⟶ complex.X (k + 2) := by
  let adj := singularChainComplexFunctorAdjunction (ModuleCat ℝ) n
  let a := (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 1))) φ
  have ha : a ≫ (singularFunctor.obj (model n)).d (k + 1) k = 0 := by
    have h := congrArg (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree k)) hφ
    rw [adj.homEquiv_naturality_right, adj.homAddEquiv_zero] at h
    exact h
  have hs : ((singularFunctor.obj (model n)).sc' (k + 2) (k + 1) k).Exact := by
    apply ((singularFunctor.obj (model n)).exactAt_iff' (k + 2) (k + 1) k
      (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k)).mp
    exact model_exact n k
  exact (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 2))).symm
    (hs.liftFromProjective a ha)

lemma liftCycle_comp (n k : ℕ) (φ : complex.X n ⟶ complex.X (k + 1))
    (hφ : φ ≫ complex.d (k + 1) k = 0) :
    liftCycle n k φ hφ ≫ complex.d (k + 2) (k + 1) = φ := by
  let adj := singularChainComplexFunctorAdjunction (ModuleCat ℝ) n
  apply (adj.homEquiv (ModuleCat.of ℝ ℝ) (degree (k + 1))).injective
  rw [adj.homEquiv_naturality_right]
  unfold liftCycle
  dsimp only [adj]
  erw [Equiv.apply_symm_apply]
  exact ShortComplex.Exact.liftFromProjective_comp _ _ _

def homotopyZero (e : complex ⟶ complex) (he : e.f 0 = 0) : Homotopy e 0 := by
  have h1 : e.f 1 ≫ complex.d 1 0 = 0 := by
    rw [e.comm, he, comp_zero]
  refine Homotopy.mkInductive e 0 ?_ (liftCycle 1 0 (e.f 1) h1) ?_ ?_
  · simpa only [zero_comp] using he
  · simp only [comp_zero, zero_add]
    exact (liftCycle_comp 1 0 (e.f 1) h1).symm
  · intro n p
    rcases p with ⟨a, b, hab⟩
    let φ := e.f (n + 2) - complex.d (n + 2) (n + 1) ≫ b
    have hφ : φ ≫ complex.d (n + 2) (n + 1) = 0 := by
      dsimp [φ]
      rw [Preadditive.sub_comp, Category.assoc, e.comm, hab,
        Preadditive.comp_add, ← Category.assoc,
        complex.d_comp_d, zero_comp, zero_add]
      exact sub_self _
    refine ⟨liftCycle (n + 2) (n + 1) φ hφ, ?_⟩
    rw [liftCycle_comp]
    dsimp [φ]
    abel

def homotopyOfDegreeZero (f g : complex ⟶ complex) (h : f.f 0 = g.f 0) :
    Homotopy f g :=
  Homotopy.equivSubZero.symm (homotopyZero (f - g) (by simp [h]))

def transpose (f : singularFunctor ⟶ singularFunctor) : complex ⟶ complex where
  f n :=
    { app X := (f.app X).f n
      naturality X Y g := congrArg (fun k => k.f n) (f.naturality g) }
  comm' i j hij := by
    apply NatTrans.ext
    funext X
    exact (f.app X).comm i j

def naturalHomotopy (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0) :
    Homotopy (transpose f) (transpose g) :=
  homotopyOfDegreeZero (transpose f) (transpose g) (by
    apply NatTrans.ext
    funext Y
    exact h Y)

def homotopyApp (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0) (X : TopCat.{0}) :
    Homotopy (f.app X) (g.app X) where
  hom i j := ((naturalHomotopy f g h).hom i j).app X
  zero i j hij := congrArg (fun k => k.app X) ((naturalHomotopy f g h).zero i j hij)
  comm i := congrArg (fun k => k.app X) ((naturalHomotopy f g h).comm i)

lemma homotopyApp_naturality (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0)
    {X Y : TopCat.{0}} (u : X ⟶ Y) (i j : ℕ) :
    (singularFunctor.map u).f i ≫ (homotopyApp f g h Y).hom i j =
      (homotopyApp f g h X).hom i j ≫ (singularFunctor.map u).f j :=
  ((naturalHomotopy f g h).hom i j).naturality u

lemma homologyMap_eq (f g : singularFunctor ⟶ singularFunctor)
    (h : ∀ X, (f.app X).f 0 = (g.app X).f 0) (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (f.app X) n =
      HomologicalComplex.homologyMap (g.app X) n :=
  (homotopyApp f g h X).homologyMap_eq n

def operator (s : ∀ n, degree n ⟶ degree n)
    (hs : ∀ n, s (n + 1) ≫ complex.d (n + 1) n =
      complex.d (n + 1) n ≫ s n) : singularFunctor ⟶ singularFunctor where
  app X :=
    { f n := (s n).app X
      comm' i j hij := by
        obtain rfl : j + 1 = i := hij
        exact congrArg (fun k => k.app X) (hs j) }
  naturality X Y u := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (s n).naturality u

def operatorHomotopy (s : ∀ n, degree n ⟶ degree n)
    (hs : ∀ n, s (n + 1) ≫ complex.d (n + 1) n =
      complex.d (n + 1) n ≫ s n) (hzero : s 0 = 𝟙 (degree 0)) :
    Homotopy (transpose (operator s hs)) (transpose (𝟙 singularFunctor)) :=
  naturalHomotopy (operator s hs) (𝟙 singularFunctor) (fun X =>
    congrArg (fun k => k.app X) hzero)

end Problem340.SingularAcyclicModels

end

end OAI
