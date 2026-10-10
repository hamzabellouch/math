import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.Basic
import OAI.AlgebraicGeometry.LogKodaira.Specialization
import OAI.AlgebraicGeometry.LogKodaira.LocalCanonical

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

def logarithmicNumerator
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :=
  letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  letI : Algebra Γ(Y.scheme, U.1) ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  letI : Algebra Γ(Y.scheme, U.1) F.variety.scheme.functionField :=
    ((algebraMap ℂ F.variety.scheme.functionField).comp
      (complexPointEvaluation y U.1 hy)).toAlgebra
  letI : Algebra Γ(X.scheme, V.1) F.variety.scheme.functionField :=
    (chartToFunctionField F.inclusion V.1).toAlgebra
  letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (appLE_constants f.hom f.over_base U.1 V.1 e c).symm
  letI : IsScalarTower Γ(Y.scheme, U.1) ℂ F.variety.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower Γ(Y.scheme, U.1) Γ(X.scheme, V.1) F.variety.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  fun (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
    (n r m : ℕ)
    (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
      (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
    (t : Γ(X.scheme, V.1)) =>
    letI := hsm
    LogarithmicSpecialization.logarithmicSpecialize ℂ Γ(Y.scheme, U.1)
      Γ(X.scheme, V.1) ℂ F.variety.scheme.functionField n r m b c t
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem fiber_affine_chart_pushout
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1) (V : X.scheme.affineOpens)
    (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) :
    IsAffineOpen (F.inclusion ⁻¹ᵁ V.1) ∧
      IsPushout (f.hom.appLE U.1 V.1 e)
        (CommRingCat.ofHom (complexPointEvaluation y U.1 hy))
        (F.inclusion.app V.1)
        (CommRingCat.ofHom (F.variety.constants (F.inclusion ⁻¹ᵁ V.1))) := by
  let W := F.inclusion ⁻¹ᵁ V.1
  let C : complexBase.Opens := ⊤
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  let : IsAffine C.toScheme := isAffineOpen_top complexBase
  have hW : W = F.inclusion ⁻¹ᵁ V.1 ⊓ F.variety.structural ⁻¹ᵁ C := by simp [W, C]
  have hp := Scheme.Hom.isPullback_resLE F.square
    (complexPoint_preimage_top y U.1 hy) e hW
  let : IsAffine W.toScheme := IsAffine.of_isPullback hp
  refine ⟨‹IsAffine W.toScheme›, ?_⟩
  have hr := isPushout_appTop_of_isPullback hp
  refine hr.of_iso U.1.topIso V.1.topIso
    (C.topIso ≪≫ Scheme.ΓSpecIso (CommRingCat.of ℂ)) W.topIso ?_ ?_ ?_ ?_
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom,
      Category.assoc]
    rfl
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Scheme.Hom.appLE_eq_app]
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change C.topIso.hom ≫ F.variety.structural.appLE C W _ =
      C.topIso.hom ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ F.variety.structural.appLE C W _
    simp

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

lemma exterior_fiber_target_tower
    (A B S C K : Type*) [CommRing A] [CommRing B] [CommRing S] [CommRing C] [CommRing K]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra A K]
    [Algebra B C] [Algebra B K] [Algebra C K] [Algebra S C] [Algebra S K]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsScalarTower A B K] [IsScalarTower A S K]
    [IsScalarTower S C K] [IsScalarTower B C K] (r : ℕ) :
    ((exteriorDifferentialMap S S C K r).restrictScalars B).comp
      (exteriorDifferentialMap A S B C r) = exteriorDifferentialMap A S B K r := by
  have hd : ((KaehlerDifferential.map S S C K).restrictScalars B).comp
      (KaehlerDifferential.map A S B C) = KaehlerDifferential.map A S B K := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B C K]
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    exteriorDifferentialMap, exteriorScalarMap_wedge]
  congr 1
  funext i
  exact LinearMap.congr_fun hd (v i)

lemma specialization_target_tower
    (R A B S C K : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C] [CommRing K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra A K]
    [Algebra B C] [Algebra B K] [Algebra C K] [Algebra S C] [Algebra S K]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsScalarTower A B K] [IsScalarTower A S K]
    [IsScalarTower S C K] [IsScalarTower B C K]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    ((pluricanonicalMap S S C K r m).restrictScalars B).comp
      (specializePluricanonical R A B S C n r m b c) =
      specializePluricanonical R A B S K n r m b c := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change pluricanonicalMap S S C K r m
      (specializePluricanonical R A B S C n r m b c (PiTensorProduct.tprod B v)) =
    specializePluricanonical R A B S K n r m b c (PiTensorProduct.tprod B v)
  simp only [specializePluricanonical, pluricanonicalMap,
    tensorScalarMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.coe_restrictScalars]
  congr 1
  funext i
  exact LinearMap.congr_fun (exterior_fiber_target_tower A B S C K r)
    (basedRelativeCanonicalEquiv R A B n r b c (v i))

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

theorem local_specialization_regular
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), chartToFunctionField F.inclusion V.1 t ≠ 0 →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (n + F.variety.dimension) m,
        (chartToFunctionField F.inclusion V.1 t)^m •
          logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q ∈
        F.variety.regularPluriformLattice
          ⟨F.inclusion ⁻¹ᵁ V.1, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  intro hsm n m b c t ht q
  let := hsm
  let W := F.inclusion ⁻¹ᵁ V.1
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let C := Γ(F.variety.scheme, W)
  let K := F.variety.scheme.functionField
  let : Algebra A ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  let : Algebra A C := ((F.variety.constants W).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B C := (F.inclusion.app V.1).hom.toAlgebra
  let : Algebra A K := ((algebraMap ℂ K).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B K := (chartToFunctionField F.inclusion V.1).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  let : IsScalarTower A ℂ C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => by
    exact (congrArg (fun g : A ⟶ C => g a)
      (fiber_affine_chart_pushout f y F U hy V e).2.w).symm
  let : IsScalarTower A ℂ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  let : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn := LinearMap.congr_fun
    (CanonicalSpecialization.specialization_target_tower ℂ A B ℂ C K
      n F.variety.dimension m b c) q
  have hcancel : (chartToFunctionField F.inclusion V.1 t)^m •
      logarithmicNumerator f y F U hy V e hsm n F.variety.dimension m b c t q =
      CanonicalSpecialization.specializePluricanonical ℂ A B ℂ K
        n F.variety.dimension m b c q := by
    change (chartToFunctionField F.inclusion V.1 t)^m •
      (((chartToFunctionField F.inclusion V.1 t)^m)⁻¹ •
        CanonicalSpecialization.specializePluricanonical ℂ A B ℂ K
          n F.variety.dimension m b c q) = _
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero m ht), one_smul]
  rw [hcancel]
  have hmem : pluricanonicalMap ℂ ℂ C K F.variety.dimension m
      (CanonicalSpecialization.specializePluricanonical ℂ A B ℂ C
        n F.variety.dimension m b c q) ∈
      F.variety.regularPluriformLattice
        ⟨W, (fiber_affine_chart_pushout f y F U hy V e).1⟩ m := by
    change _ ∈ Submodule.span C _
    rw [← LocalCanonical.range_pluricanonicalPullback ℂ C K F.variety.dimension m]
    exact ⟨_, rfl⟩
  exact hn ▸ hmem

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma chartToFunctionField_restrict
    {X F : SmoothProjectiveVariety} (i : F.scheme ⟶ X.scheme)
    (V V' : X.scheme.Opens) (h : V' ≤ V)
    [Nonempty (i ⁻¹ᵁ V)] [Nonempty (i ⁻¹ᵁ V')] (a : Γ(X.scheme, V)) :
    chartToFunctionField i V' (X.scheme.presheaf.map (homOfLE h).op a) =
      chartToFunctionField i V a := by
  have hn := congrArg (fun g : Γ(X.scheme, V) ⟶ Γ(F.scheme, i ⁻¹ᵁ V') => g a)
    (i.naturality (homOfLE h).op)
  change F.scheme.germToFunctionField (i ⁻¹ᵁ V')
    (i.app V' (X.scheme.presheaf.map (homOfLE h).op a)) = _
  have hn' : i.app V' (X.scheme.presheaf.map (homOfLE h).op a) =
      F.scheme.presheaf.map
        (homOfLE (show i ⁻¹ᵁ V' ≤ i ⁻¹ᵁ V from fun z hz => h hz)).op (i.app V a) := hn
  rw [hn']
  exact F.scheme.presheaf.germ_res_apply
    (homOfLE (show i ⁻¹ᵁ V' ≤ i ⁻¹ᵁ V from fun z hz => h hz))
    (genericPoint F.scheme) _ (i.app V a)

lemma constants_restrict (X : SmoothProjectiveVariety)
    (V V' : X.scheme.Opens) (h : V' ≤ V) [Nonempty V] [Nonempty V'] (a : ℂ) :
    X.scheme.presheaf.map (homOfLE h).op (X.constants V a) = X.constants V' a := by
  apply X.scheme.germToFunctionField_injective V'
  change algebraMap Γ(X.scheme, V') X.scheme.functionField
      (X.scheme.presheaf.map (homOfLE h).op (X.constants V a)) =
    algebraMap Γ(X.scheme, V') X.scheme.functionField (X.constants V' a)
  exact (X.scheme.presheaf.germ_res_apply (homOfLE h) (genericPoint X.scheme) _ _).trans
    ((X.germ_constants V a).trans (X.germ_constants V' a).symm)

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

theorem specialization_refinement
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V V' : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) (hV : V'.1 ≤ V.1)
    [Nonempty V.1] [Nonempty V'.1]
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] [Nonempty (F.inclusion ⁻¹ᵁ V'.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
      (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
      (hsm' : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V'.1))
      (n r m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (c' : Module.Basis (Fin r) Γ(X.scheme, V'.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V'.1)))
      (t : Γ(X.scheme, V.1)) (t' : Γ(X.scheme, V'.1)),
      chartToFunctionField F.inclusion V.1 t ≠ 0 →
      chartToFunctionField F.inclusion V'.1 t' ≠ 0 →
      ∀ (q : Pluricanonical ℂ Γ(X.scheme, V.1) (n+r) m)
        (q' : Pluricanonical ℂ Γ(X.scheme, V'.1) (n+r) m),
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField (n+r) m t q =
        logarithmicPullback ℂ Γ(X.scheme, V'.1) X.scheme.functionField (n+r) m t' q' →
      logarithmicNumerator f y F U hy V e hsm n r m b c t q =
        logarithmicNumerator f y F U hy V' (hV.trans e) hsm' n r m b c' t' q' := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V'.1) :=
    (f.hom.appLE U.1 V'.1 (hV.trans e)).hom.toAlgebra
  intro hsm hsm' n r m b c c' t t' ht ht' q q' heq
  let := hsm
  let := hsm'
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let B' := Γ(X.scheme, V'.1)
  let K := X.scheme.functionField
  let C := F.variety.scheme.functionField
  let : Algebra B B' := (X.scheme.presheaf.map (homOfLE hV).op).hom.toAlgebra
  let : Algebra A ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  let : Algebra A C := ((algebraMap ℂ C).comp
    (complexPointEvaluation y U.1 hy)).toAlgebra
  let : Algebra B C := (chartToFunctionField F.inclusion V.1).toAlgebra
  let : Algebra B' C := (chartToFunctionField F.inclusion V'.1).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  let : IsScalarTower ℂ A B' := IsScalarTower.of_algebraMap_eq fun a =>
    (appLE_constants f.hom f.over_base U.1 V'.1 (hV.trans e) a).symm
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a =>
    (congrArg (fun g : A ⟶ B' => g a)
      (f.hom.appLE_map e (homOfLE hV).op)).symm
  let : IsScalarTower ℂ B B' := IsScalarTower.of_algebraMap_eq fun a =>
    (constants_restrict X V.1 V'.1 hV a).symm
  let : IsScalarTower B B' K := IsScalarTower.of_algebraMap_eq fun a =>
    (X.scheme.presheaf.germ_res_apply (homOfLE hV) (genericPoint X.scheme) _ a).symm
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  let : IsScalarTower A B' C := IsScalarTower.of_algebraMap_eq fun a =>
    (fiber_chart_base_scalar f y F U.1 hy V'.1 (hV.trans e) a).symm
  let : IsScalarTower A ℂ C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B B' C := IsScalarTower.of_algebraMap_eq fun a =>
    (chartToFunctionField_restrict F.inclusion V.1 V'.1 hV a).symm
  let := functionField_isFractionRing_of_isAffineOpen X.scheme V'.1 V'.2
  have hpb : logarithmicPullback ℂ B' K (n+r) m (algebraMap B B' t)
      (pluricanonicalMap ℂ ℂ B B' (n+r) m q) = logarithmicPullback ℂ B' K (n+r) m t' q' :=
    (logarithmicPullback_naturality ℂ B B' K (n+r) m t q).trans heq
  have htref : algebraMap B' C (algebraMap B B' t) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply B B' C]
    exact ht
  have he := logarithmic_specialization_equation_independent ℂ A B' K ℂ C
    n r m b c' (algebraMap B B' t) t' htref ht'
    (pluricanonicalMap ℂ ℂ B B' (n+r) m q) q' hpb
  have hn := logarithmicSpecialize_naturality ℂ A B B' ℂ C n r m b c c' t q
  exact hn.symm.trans he

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI
