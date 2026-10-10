import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.CanonicalShapiro

namespace OAI

section

section

open CategoryTheory CategoryTheory.Limits Finsupp Representation Rep
universe u
namespace HomologyConjugation
variable {k G : Type u} [CommRing k] [Group G]

noncomputable def rightBarLift (c : G) (n : ℕ) :
    Rep.free k G (Fin n → G) ⟶ Rep.free k G (Fin n → G) :=
  Rep.freeLift k G _ (fun x => Finsupp.single ((MulAut.conj c) ∘ x)
    (MonoidAlgebra.single c⁻¹ 1))

@[simp] lemma rightBarLift_single (c : G) (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (rightBarLift (k:=k) c n).hom (single x (MonoidAlgebra.single g r)) =
      single ((MulAut.conj c) ∘ x) (MonoidAlgebra.single (g*c⁻¹) r) := by
  simp [rightBarLift, Representation.freeLift_single_single]

lemma bar_d_weighted (n : ℕ) (x : Fin (n+1) → G) (g : G) (r : k) :
    (Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single g r)) =
      single (fun i => x i.succ) (MonoidAlgebra.single (g*x 0) r) +
        ∑j : Fin (n+1), single (Fin.contractNth j (·*·) x)
          (MonoidAlgebra.single g (r*((-1:k)^(j.val+1)))) := by
  simp [Rep.barComplex.d, ← Representation.IntertwiningMap.toLinearMap_apply,
    smul_add, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]

lemma rightBarLift_d (c : G) (n : ℕ) :
    Rep.barComplex.d k G n ≫ rightBarLift c n =
      rightBarLift c (n+1) ≫ Rep.barComplex.d k G n := by
  apply Rep.free_ext
  intro x
  change (rightBarLift (k:=k) c n).hom
      ((Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single 1 1))) =
    (Rep.barComplex.d k G n).hom
      ((rightBarLift (k:=k) c (n+1)).hom (single x (MonoidAlgebra.single 1 1)))
  rw [Rep.barComplex.d_single, rightBarLift_single, bar_d_weighted]
  simp only [map_add, map_sum]
  apply congrArg₂ (·+·)
  · rw [rightBarLift_single]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [rightBarLift_single]
    congr 1
    · exact Fin.comp_contractNth (·*·) (·*·) (map_mul (MulAut.conj c)) j x
    · simp

noncomputable def rightBarMap (c : G) : Rep.barComplex k G ⟶ Rep.barComplex k G where
  f n := rightBarLift c n
  comm' i j h := by subst h; simpa [ChainComplex.of.d] using (rightBarLift_d (k:=k) c j).symm

lemma rightBarMap_π (c : G) :
    rightBarMap (k:=k) c ≫ (Rep.barResolution k G).π = (Rep.barResolution k G).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution k G).π.f 0).hom
      ((rightBarLift c 0).hom (single x (MonoidAlgebra.single 1 1))) =
    ((Rep.barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single 1 1))
  rw [rightBarLift_single, CanonicalShapiro.bar_π_zero_single, CanonicalShapiro.bar_π_zero_single]

noncomputable def rightBarHomotopy (c : G) :
    Homotopy (rightBarMap (k:=k) c) (𝟙 (Rep.barComplex k G)) :=
  ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial k G k))
    (P:=Rep.barResolution k G) (Q:=Rep.barResolution k G) _ _
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact rightBarMap_π (k:=k) c) (by dsimp only [Rep.barResolution]; simp)

noncomputable def conjugationCoeff (c : G) (A : Rep.{u} k G) :
    A ⟶ Rep.res (MulAut.conj c).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ c, by
    intro g
    ext a
    simp [MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, mul_assoc]⟩

@[simp] lemma conjugationCoeff_apply (c : G) (A : Rep.{u} k G) (a : A) :
    (conjugationCoeff c A).hom a = A.ρ c a := rfl

lemma chainsIso_inv_weighted (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) (g : G) (r : k) :
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      (Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single g r))) = single x (r • A.ρ g⁻¹ a) := by
  change Rep.coinvariantsTensorFreeToFinsupp A _ _ = _
  exact Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a x g r

lemma conjugation_factorization (c : G) (A : Rep.{u} k G) [DecidableEq G] :
    groupHomology.chainsMap (MulAut.conj c).toMonoidHom (conjugationCoeff c A) =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map (rightBarMap c) ≫
      (groupHomology.inhomogeneousChainsIso A).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change (groupHomology.chainsMap (MulAut.conj c).toMonoidHom (conjugationCoeff c A)).f n (single x a) = _
  rw [groupHomology.chainsMap_f_single]
  change single ((MulAut.conj c) ∘ x) (A.ρ c a) =
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      ((((Rep.coinvariantsTensor k G).obj A).map (rightBarLift c n))
        ((groupHomology.inhomogeneousChainsIso A).hom.f n (single x a)))
  rw [CanonicalShapiro.chainsIso_hom_single, CanonicalShapiro.coinvariantsTensor_map_mk,
    rightBarLift_single, chainsIso_inv_weighted]
  simp

lemma map_conjugation (c : G) (A : Rep.{u} k G) (n : ℕ) :
    groupHomology.map (MulAut.conj c).toMonoidHom (conjugationCoeff c A) n =
      𝟙 (groupHomology A n) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj A
  have hh := ((F.mapHomotopy (rightBarHomotopy (k:=k) c)).compLeft
    (groupHomology.inhomogeneousChainsIso A).hom).compRight
    (groupHomology.inhomogeneousChainsIso A).inv
  have hm : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 (Rep.barComplex k G)) = 𝟙 _ :=
    (F.mapHomologicalComplex _).map_id _
  rw [hm] at hh
  have he : Homotopy (groupHomology.chainsMap (MulAut.conj c).toMonoidHom
      (conjugationCoeff c A)) (𝟙 _) := by
    rw [conjugation_factorization]
    simpa only [Category.id_comp, Iso.hom_inv_id, Category.assoc] using hh
  exact he.homologyMap_eq n |>.trans (HomologicalComplex.homologyMap_id _ _)

variable {H : Type u} [Group H]

lemma map_after_conjugation (f : H →* G) {B : Rep.{u} k H} {A : Rep.{u} k G}
    (φ : B ⟶ Rep.res f A) (c : G) (n : ℕ) :
    groupHomology.map ((MulAut.conj c).toMonoidHom.comp f)
      (φ ≫ (Rep.resFunctor.{u,u,u,u} f).map (conjugationCoeff c A)) n =
      groupHomology.map f φ n := by
  rw [groupHomology.map_comp, map_conjugation, Category.comp_id]

lemma map_eq_of_centralizer (f : H →* G) {B : Rep.{u} k H} {A : Rep.{u} k G}
    (φ ψ : B ⟶ Rep.res f A) (c : G) (hc : ∀h,c*f h=f h*c)
    (hψ : ∀b,ψ.hom b=A.ρ c (φ.hom b)) (n : ℕ) :
    groupHomology.map f ψ n = groupHomology.map f φ n := by
  have he : (MulAut.conj c).toMonoidHom.comp f=f := by
    ext h
    change c * f h * c⁻¹=f h
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have ht := groupHomology.map_congr (A:=B) (B:=A) (n:=n)
    (f:=(MulAut.conj c).toMonoidHom.comp f) (g:=f)
    (φ:=φ ≫ (Rep.resFunctor.{u,u,u,u} f).map (conjugationCoeff c A)) (ψ:=ψ) he
    (by apply LinearMap.ext; intro b; exact (hψ b).symm)
  exact ht.symm.trans (map_after_conjugation f φ c n)

end HomologyConjugation

end

end

end OAI
