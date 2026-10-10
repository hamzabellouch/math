import Mathlib

namespace OAI

section

section

open CategoryTheory Limits MonoidalCategory SimplicialObject AlgebraicTopology
namespace FreeChains

abbrev A := ModuleCat.{0} ℤ
abbrev Z : A := ModuleCat.of ℤ ℤ
abbrev c := ComplexShape.down ℕ

noncomputable def forward (X : Type) : (sigmaConst.obj Z).obj X ⟶ (ModuleCat.free ℤ).obj X :=
  Sigma.desc (fun x => ModuleCat.ofHom (Finsupp.lsingle x))
noncomputable def backward (X : Type) : (ModuleCat.free ℤ).obj X ⟶ (sigmaConst.obj Z).obj X :=
  ModuleCat.freeDesc (↾fun x => (Sigma.ι (fun _ : X => Z) x) (1:ℤ))
@[reassoc (attr := simp)] lemma ι_forward (X : Type) (x : X) :
    Sigma.ι (fun _ : X => Z) x ≫ forward X = ModuleCat.ofHom (Finsupp.lsingle x) :=
  Sigma.ι_comp_desc _ _
@[simp] lemma backward_mk (X : Type) (x : X) :
    backward X (ModuleCat.freeMk x)=(Sigma.ι (fun _ : X => Z) x) (1:ℤ) := by
  simp [backward]

noncomputable def iso (X : Type) : (sigmaConst.obj Z).obj X ≅ (ModuleCat.free ℤ).obj X where
  hom := forward X
  inv := backward X
  hom_inv_id := by
    apply Sigma.hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    have h := congrArg (fun f : Z ⟶ (ModuleCat.free ℤ).obj X => f (1:ℤ)) (ι_forward X x)
    change backward X (forward X ((Sigma.ι (fun _ : X => Z) x) (1:ℤ))) = _
    rw [show forward X ((Sigma.ι (fun _ : X => Z) x) (1:ℤ))=ModuleCat.freeMk x from h]
    exact backward_mk X x
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro x
    change forward X (backward X (ModuleCat.freeMk x)) = ModuleCat.freeMk x
    rw [backward_mk]
    exact congrArg (fun f : Z ⟶ (ModuleCat.free ℤ).obj X => f (1:ℤ)) (ι_forward X x)

noncomputable def naturalIso : sigmaConst.obj Z ≅ ModuleCat.free ℤ :=
  NatIso.ofComponents iso (by
    intro X Y f
    apply Sigma.hom_ext
    intro x
    dsimp only [iso,sigmaConst]
    erw [Sigma.ι_comp_map'_assoc]
    rw [Category.id_comp,ι_forward,ι_forward_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change Finsupp.single (f x) 1 = (ModuleCat.free ℤ).map f (ModuleCat.freeMk x)
    exact (ModuleCat.free_map_apply f x).symm)

noncomputable def complex (X : SSet) : ChainComplex A ℕ :=
  AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)
noncomputable def complexIso (X : SSet) : SSet.chainComplex X Z ≅ complex X :=
  (alternatingFaceMapComplex A).mapIso (Functor.isoWhiskerLeft X naturalIso)

end FreeChains

end

section

open CategoryTheory Limits Classical
namespace AdditiveFinite

variable {R : Type} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
    (A : ModuleCat R) [Module.Free R A] [Module.Finite R A]

noncomputable abbrev basis := Module.finBasis R A
noncomputable abbrev I := Fin (Module.finrank R A)
noncomputable def incl (i : I A) : ModuleCat.of R R ⟶ A :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R A (basis A i))
noncomputable def proj (i : I A) : A ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom ((basis A).coord i)
omit [IsNoetherianRing R] in
lemma sum_proj_incl : ∑ i : I A, proj A i ≫ incl A i = 𝟙 A := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [proj,incl]

omit [IsNoetherianRing R] in
lemma isZero (h : IsZero (F.obj (ModuleCat.of R R))) : IsZero (F.obj A) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← F.map_id, ← sum_proj_incl A,F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [F.map_comp,h.eq_zero_of_tgt (F.map (proj A i)),zero_comp]

lemma finite [Module.Finite R (F.obj (ModuleCat.of R R))] :
    Module.Finite R (F.obj A) := by
  let φ : F.obj A →ₗ[R] (I A → F.obj (ModuleCat.of R R)) :=
    LinearMap.pi (fun i => (F.map (proj A i)).hom)
  apply Module.Finite.of_injective φ
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hp : ∀i : I A, (F.map (proj A i)).hom x=0 := fun i => congrFun hx i
  have he : ∑ i : I A, (F.map (proj A i) ≫ F.map (incl A i))=𝟙 _ := by
    simp only [← F.map_comp, ← F.map_sum,sum_proj_incl,F.map_id]
  have ht := congrArg (fun t => t.hom x) he
  simpa [hp] using ht.symm

end AdditiveFinite

end

section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K : ChainComplex (ModuleCat.{0} R) ℕ)

noncomputable def functor : ModuleCat.{0} R ⥤ ChainComplex (ModuleCat.{0} R) ℕ where
  obj A := ((tensorRight A).mapHomologicalComplex c).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{0} R)).map f) c).app K
  map_id A := by apply HomologicalComplex.Hom.ext; funext n; change K.X n ◁ 𝟙 A=𝟙 _; simp
  map_comp f g := by apply HomologicalComplex.Hom.ext; funext n; change K.X n ◁ (f≫g)=(K.X n ◁ f)≫(K.X n ◁ g); simp

instance : (functor K).Additive where
  map_add := by
    intros
    apply HomologicalComplex.Hom.ext
    funext n
    exact MonoidalPreadditive.whiskerLeft_add _ _

noncomputable def unitIso : (functor K).obj (ModuleCat.of R R) ≅ K :=
  (NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{0} R)) c).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app K

noncomputable def homologyFunctor (n : ℕ) : ModuleCat.{0} R ⥤ ModuleCat.{0} R :=
  functor K ⋙ HomologicalComplex.homologyFunctor _ c n

instance (n : ℕ) : (homologyFunctor K n).Additive := by
  unfold homologyFunctor
  infer_instance

noncomputable def homologyUnitIso (n : ℕ) :
    (homologyFunctor K n).obj (ModuleCat.of R R) ≅ K.homology n :=
  (HomologicalComplex.homologyFunctor _ c n).mapIso (unitIso K)

lemma shortExact [∀n,Module.Flat R (K.X n)] {S : ShortComplex (ModuleCat.{0} R)}
    (hS : S.ShortExact) : (S.map (functor K)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  change (S.map (tensorLeft (K.X n))).ShortExact
  exact hS.map_of_exact _

lemma free_finite [Nontrivial R] [IsNoetherianRing R] (A : ModuleCat.{0} R)
    [Module.Free R A] [Module.Finite R A] (n : ℕ)
    [Module.Finite R (K.homology n)] : Module.Finite R ((homologyFunctor K n).obj A) := by
  have : Module.Finite R ((homologyFunctor K n).obj (ModuleCat.of R R)) :=
    Module.Finite.equiv (homologyUnitIso K n).symm.toLinearEquiv
  exact AdditiveFinite.finite _ _

lemma free_isZero [Nontrivial R] [IsNoetherianRing R] (A : ModuleCat.{0} R)
    [Module.Free R A] [Module.Finite R A] (n : ℕ)
    (h : IsZero (K.homology n)) : IsZero ((homologyFunctor K n).obj A) := by
  exact AdditiveFinite.isZero _ _ (h.of_iso (homologyUnitIso K n))

end TensorCoefficient

end

end

end OAI
