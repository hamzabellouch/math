import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.LinearForms

namespace OAI

section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance incidenceTensorRing {K R F σ : Type*}
    [CommRing K] [CommRing R] [CommRing F] [Algebra K R]
    [Algebra (MvPolynomial σ K) F] (I : Ideal (MvPolynomial σ R)) :
    CommRing (F ⊗[MvPolynomial σ K] (MvPolynomial σ R ⧸ I)) :=
  Algebra.TensorProduct.instCommRing

local instance incidenceTensorAlgebra {K R F σ : Type*}
    [CommRing K] [CommRing R] [CommRing F] [Algebra K R]
    [Algebra (MvPolynomial σ K) F] (I : Ideal (MvPolynomial σ R)) :
    Algebra F (F ⊗[MvPolynomial σ K] (MvPolynomial σ R ⧸ I)) :=
  Algebra.TensorProduct.leftAlgebra

theorem universalHyperplane_geometricGeneric_domain
    {K R F E σ : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    [Fintype σ] [Field F] [Field E]
    [Algebra (MvPolynomial σ K) F] [Algebra F E]
    [Module.Flat (MvPolynomial σ K) F]
    (v : σ → R) (hv : Ideal.span (Set.range v) = ⊤)
    (s : MvPolynomial σ R ⧸ Ideal.span {homogeneousLinearForm v}) (hs : s ≠ 0)
    [IsDomain (E ⊗[F] (F ⊗[MvPolynomial σ K] Localization.Away s))] :
    IsDomain (E ⊗[F] (F ⊗[MvPolynomial σ K]
      (MvPolynomial σ R ⧸ Ideal.span {homogeneousLinearForm v}))) := by
  let : IsDomain (MvPolynomial σ R ⧸ Ideal.span {homogeneousLinearForm v}) :=
    universalHyperplane_isDomain v hv
  exact geometricGeneric_domain_of_nonempty_localization s hs

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

omit [Fintype σ] in
lemma mvC_nonZeroDivisor (a : R) (ha : a ∈ R⁰) : C (σ := σ) a ∈ (MvPolynomial σ R)⁰ := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro p hp
  ext d
  apply ha.1
  rw [mul_comm] at hp
  have hh := congrArg (fun polynomial : MvPolynomial σ R => polynomial.coeff d) hp
  simpa only [coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using hh

lemma homogeneousLinearForm_regular_of_coefficient (v : σ → R) (i : σ)
    (hi : v i ∈ R⁰) : homogeneousLinearForm v ∈ (MvPolynomial σ R)⁰ := by
  let e := separateLinearVariable (R := R) i
  have hreg : e (homogeneousLinearForm v) ∈
      (Polynomial (MvPolynomial {j : σ // j ≠ i} R))⁰ := by
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    rw [separateLinearVariable_coeff_one]
    exact mvC_nonZeroDivisor _ hi
  apply mem_nonZeroDivisors_iff_right.mpr
  intro q hq
  apply e.injective
  rw [map_zero]
  apply hreg.2
  simpa only [map_mul, map_zero] using congrArg e hq

lemma quotient_regular_of_dvd (a b : R)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    Ideal.Quotient.mk (Ideal.span {a}) b ∈ (R ⧸ Ideal.span {a})⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.mem_span_singleton]
  apply hab
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact hx

lemma linearForm_coefficient_saturated (a : R) (v : σ → R) (j : σ)
    (hab : ∀ r : R, a ∣ v j * r → a ∣ r)
    (p : MvPolynomial σ R) (hp : C a ∣ homogeneousLinearForm v * p) : C a ∣ p := by
  let I := Ideal.span ({a} : Set R)
  let m : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hm : map m (homogeneousLinearForm v * p) = 0 := by
    obtain ⟨q, hq⟩ := hp
    rw [hq]
    have hma : m a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    simp only [map_mul, map_C, hma, map_zero, zero_mul]
  have hq := homogeneousLinearForm_regular_of_coefficient (fun i => m (v i)) j
    (quotient_regular_of_dvd a (v j) hab)
  have hp0 : map m p = 0 := by
    apply hq.1
    simpa only [homogeneousLinearForm, map_mul, map_sum, map_C, map_X] using hm
  rw [C_dvd_iff_dvd_coeff]
  intro d
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hh := congrArg (fun polynomial : MvPolynomial σ (R ⧸ I) => polynomial.coeff d) hp0
  simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using hh

theorem homogeneousLinearForm_isPrime_of_regularPair [IsDomain R]
    (v : σ → R) (i j : σ) (hji : j ≠ i) (hi : v i ≠ 0)
    (hij : ∀ r : R, v i ∣ v j * r → v i ∣ r) :
    (Ideal.span {homogeneousLinearForm v} : Ideal (MvPolynomial σ R)).IsPrime := by
  let e := separateLinearVariable (R := R) i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {homogeneousLinearForm v}
  have ha : C (σ := {j : σ // j ≠ i}) (v i) ≠ 0 := by simpa using hi
  have hprime : (J.map e.toRingHom).IsPrime := by
    rw [show J = Ideal.span {homogeneousLinearForm v} from rfl,
      Ideal.map_span, Set.image_singleton]
    change (Ideal.span {e (homogeneousLinearForm v)}).IsPrime
    rw [separateLinearVariable_eq]
    apply linear_ideal_isPrime _ _ ha
    intro p hp
    exact linearForm_coefficient_saturated (v i)
      (fun j : {j : σ // j ≠ i} => v j) ⟨j, hji⟩ hij p hp
  have hcon : (J.map e.toRingHom).comap e.toRingHom = J :=
    Ideal.comap_map_of_bijective _ e.bijective
  change J.IsPrime
  rw [← hcon]
  exact hprime.comap _

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A B σ : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

def mvPolynomialMapOver (f : A →ₐ[R] B) : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ B) where
  __ := MvPolynomial.map f.toRingHom
  commutes' p := by
    change MvPolynomial.map f.toRingHom (MvPolynomial.map (algebraMap R A) p) =
      MvPolynomial.map (algebraMap R B) p
    rw [MvPolynomial.map_map]
    have hf : f.toRingHom.comp (algebraMap R A) = algebraMap R B := by
      ext z
      exact f.commutes z
    rw [hf]

@[simp] lemma mvPolynomialMapOver_C (f : A →ₐ[R] B) (a : A) :
    mvPolynomialMapOver (σ := σ) f (C a) = C (f a) := map_C f.toRingHom a
@[simp] lemma mvPolynomialMapOver_X (f : A →ₐ[R] B) (i : σ) :
    mvPolynomialMapOver f (X i) = X i := map_X f.toRingHom i

def mvPolynomialTensorTo : ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ (A ⊗[R] B)) :=
  Algebra.TensorProduct.lift (mvPolynomialMapOver Algebra.TensorProduct.includeLeft)
    (mvPolynomialMapOver Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)

abbrev mvPolynomialTensorCoeff : (A ⊗[R] B) →ₐ[R] ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] _).restrictScalars R).comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (((Algebra.TensorProduct.includeRight : (MvPolynomial σ B) →ₐ[(MvPolynomial σ R)] _).restrictScalars R).comp (IsScalarTower.toAlgHom R B (MvPolynomial σ B)))
    (fun _ _ => Commute.all _ _)

def mvPolynomialTensorFrom : (MvPolynomial σ (A ⊗[R] B)) →ₐ[R]
    (MvPolynomial σ A ⊗[MvPolynomial σ R] MvPolynomial σ B) where
  __ := MvPolynomial.eval₂Hom mvPolynomialTensorCoeff.toRingHom
    (fun i => (X i : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B))
  commutes' r := by
    change MvPolynomial.eval₂Hom mvPolynomialTensorCoeff.toRingHom _
      (C (algebraMap R (A ⊗[R] B) r)) = _
    rw [eval₂Hom_C]
    exact mvPolynomialTensorCoeff.commutes r

lemma mvPolynomialTensorTo_left (p : (MvPolynomial σ A)) :
    mvPolynomialTensorTo (p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p := by
  simp [mvPolynomialTensorTo]

lemma mvPolynomialTensorTo_right (p : (MvPolynomial σ B)) :
    mvPolynomialTensorTo ((1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] p) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) p := by
  simp [mvPolynomialTensorTo]

@[simp] lemma mvPolynomialTensorFrom_C_tmul (a : A) (b : B) :
    mvPolynomialTensorFrom (C (a ⊗ₜ[R] b)) = (C a) ⊗ₜ[(MvPolynomial σ R)] (C b) := by
  simp [mvPolynomialTensorFrom, mvPolynomialTensorCoeff]

@[simp] lemma mvPolynomialTensorFrom_X (i : σ) :
    mvPolynomialTensorFrom (R := R) (A := A) (B := B) (X i) =
      (X i : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B) := by
  simp [mvPolynomialTensorFrom]

lemma mvPolynomialTensorTo_tmul (p : MvPolynomial σ A) (q : MvPolynomial σ B) :
    mvPolynomialTensorTo (R := R) (p ⊗ₜ[MvPolynomial σ R] q) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p *
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) q :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

lemma mvPolynomialTensorFrom_left :
    mvPolynomialTensorFrom.comp ((mvPolynomialMapOver
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).restrictScalars R) =
      (Algebra.TensorProduct.includeLeft : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)).restrictScalars R := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro a
    change mvPolynomialTensorFrom
      (mvPolynomialMapOver Algebra.TensorProduct.includeLeft (C a)) =
      (C a) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B)
    rw [mvPolynomialMapOver_C]
    change mvPolynomialTensorFrom (C (a ⊗ₜ[R] (1 : B))) = _
    simp
  · intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mvPolynomialMapOver_X]
    change mvPolynomialTensorFrom (X i) = X i ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))
    simp [mvPolynomialTensorFrom]

lemma mvPolynomialTensorFrom_right :
    mvPolynomialTensorFrom.comp ((mvPolynomialMapOver
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R) =
      (Algebra.TensorProduct.includeRight : (MvPolynomial σ B) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)).restrictScalars R := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro b
    change mvPolynomialTensorFrom
      (mvPolynomialMapOver Algebra.TensorProduct.includeRight (C b)) =
      (1 : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (C b)
    rw [mvPolynomialMapOver_C]
    change mvPolynomialTensorFrom (C ((1 : A) ⊗ₜ[R] b)) = _
    simp
  · intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mvPolynomialMapOver_X]
    change mvPolynomialTensorFrom (X i) = (1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] (X i)
    rw [show mvPolynomialTensorFrom (X i) = (X i : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B)) by
      simp [mvPolynomialTensorFrom]]
    have h := Algebra.TensorProduct.algebraMap_apply'
      (R := (MvPolynomial σ R)) (A := (MvPolynomial σ A)) (B := (MvPolynomial σ B)) (X i)
    simpa using h

lemma mvPolynomialTensorFrom_to :
    mvPolynomialTensorFrom.comp (mvPolynomialTensorTo.restrictScalars R) =
      AlgHom.id R ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) := by
  apply AlgHom.ext
  intro t
  change mvPolynomialTensorFrom (mvPolynomialTensorTo t) = t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    rw [mvPolynomialTensorTo_tmul, map_mul]
    have hl := DFunLike.congr_fun (mvPolynomialTensorFrom_left (R := R) (A := A) (B := B)) p
    have hr := DFunLike.congr_fun (mvPolynomialTensorFrom_right (R := R) (A := A) (B := B)) q
    change mvPolynomialTensorFrom (mvPolynomialMapOver Algebra.TensorProduct.includeLeft p) =
      p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B)) at hl
    change mvPolynomialTensorFrom (mvPolynomialMapOver Algebra.TensorProduct.includeRight q) =
      (1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] q at hr
    rw [hl, hr]
    simp

lemma mvPolynomialTensorTo_from :
    (mvPolynomialTensorTo.restrictScalars R).comp mvPolynomialTensorFrom =
      AlgHom.id R (MvPolynomial σ (A ⊗[R] B)) := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro t
    change mvPolynomialTensorTo (mvPolynomialTensorFrom (C t)) = C t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [mvPolynomialTensorFrom_C_tmul]
      rw [mvPolynomialTensorTo, Algebra.TensorProduct.lift_tmul]
      rw [mvPolynomialMapOver_C, mvPolynomialMapOver_C, ← C_mul]
      change C ((a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)) = C (a ⊗ₜ[R] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · intro i
    change mvPolynomialTensorTo (R := R) (A := A) (B := B)
      (mvPolynomialTensorFrom (R := R) (A := A) (B := B) (X i)) = X i
    rw [mvPolynomialTensorFrom_X, mvPolynomialTensorTo_left, mvPolynomialMapOver_X]

def mvPolynomialTensorEquiv : ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) ≃ₐ[R] (MvPolynomial σ (A ⊗[R] B)) :=
  AlgEquiv.ofAlgHom (mvPolynomialTensorTo.restrictScalars R) mvPolynomialTensorFrom
    mvPolynomialTensorTo_from mvPolynomialTensorFrom_to

@[simp] lemma mvPolynomialTensorEquiv_left (p : (MvPolynomial σ A)) :
    mvPolynomialTensorEquiv (p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p :=
  mvPolynomialTensorTo_left p

@[simp] lemma mvPolynomialTensorEquiv_right (p : (MvPolynomial σ B)) :
    mvPolynomialTensorEquiv ((1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] p) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) p :=
  mvPolynomialTensorTo_right p

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

theorem tensor_polynomial_relation {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra R[X] A] [IsScalarTower R R[X] A] :
    Nonempty (((A ⊗[R] A) ⧸ Ideal.span
      {algebraMap R[X] A X ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] algebraMap R[X] A X})
        ≃ₐ[R] (A ⊗[R[X]] A)) := by
  let a := algebraMap R[X] A X
  let T := A ⊗[R] A
  let D := A ⊗[R[X]] A
  let I : Ideal T := Ideal.span {a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a}
  let Q := T ⧸ I
  let q : T →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let l : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeRight
  have he : l a = r a := by
    apply sub_eq_zero.mp
    change q (a ⊗ₜ[R] 1) - q (1 ⊗ₜ[R] a) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hp : l.toRingHom.comp (algebraMap R[X] A) =
      r.toRingHom.comp (algebraMap R[X] A) := by
    apply Polynomial.ringHom_ext
    · intro z
      change l (algebraMap R[X] A (C z)) = r (algebraMap R[X] A (C z))
      change l (algebraMap R[X] A (algebraMap R R[X] z)) =
        r (algebraMap R[X] A (algebraMap R R[X] z))
      rw [← IsScalarTower.algebraMap_apply]
      rw [l.commutes, r.commutes]
    · exact he
  let lp : A →ₐ[R[X]] Q := ⟨l.toRingHom, fun _ => rfl⟩
  let rp : A →ₐ[R[X]] Q := ⟨r.toRingHom, fun z => (DFunLike.congr_fun hp z).symm⟩
  let g : D →ₐ[R] Q := (Algebra.TensorProduct.lift lp rp
    (fun _ _ => Commute.all _ _)).restrictScalars R
  let dl : A →ₐ[R] D := (Algebra.TensorProduct.includeLeft : A →ₐ[R[X]] D).restrictScalars R
  let dr : A →ₐ[R] D := (Algebra.TensorProduct.includeRight : A →ₐ[R[X]] D).restrictScalars R
  let f : T →ₐ[R] D := Algebra.TensorProduct.lift dl dr (fun _ _ => Commute.all _ _)
  have hft (x y : A) : f (x ⊗ₜ[R] y) = x ⊗ₜ[R[X]] y := by
    change (x ⊗ₜ[R[X]] (1 : A)) * ((1 : A) ⊗ₜ[R[X]] y) = _
    simp
  have hgt (x y : A) : g (x ⊗ₜ[R[X]] y) = q (x ⊗ₜ[R] y) := by
    change q (x ⊗ₜ[R] (1 : A)) * q ((1 : A) ⊗ₜ[R] y) = _
    rw [← map_mul]
    apply congrArg q
    change (x ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] y) = x ⊗ₜ[R] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : I ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    rintro z rfl
    change f (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] a) = 0
    rw [map_sub, hft, hft]
    apply sub_eq_zero.mpr
    change (algebraMap R[X] A X) ⊗ₜ[R[X]] (1 : A) =
      (1 : A) ⊗ₜ[R[X]] (algebraMap R[X] A X)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let fq : Q →ₐ[R] D := Ideal.Quotient.liftₐ I f hf
  have hfq (t : T) : fq (q t) = f t := rfl
  have hgf : g.comp fq = AlgHom.id R Q := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro t
    change g (fq (q t)) = q t
    rw [hfq]
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hft, hgt]
  have hfg : fq.comp g = AlgHom.id R D := by
    apply AlgHom.ext
    intro t
    change fq (g t) = t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hgt, hfq, hft]
  exact ⟨AlgEquiv.ofAlgHom fq g hfg hgf⟩

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable

theorem hyperplaneFamily_double_isDomain {K A σ : Type*} [Field K]
    [CommRing A] [Algebra K A] [Fintype σ] [IsDomain (A ⊗[K] A)]
    [Algebra (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    [IsScalarTower (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    (v : σ → A)
    (heq : algebraMap (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A) Polynomial.X =
      homogeneousLinearForm v)
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    IsDomain (MvPolynomial σ A ⊗[Polynomial (MvPolynomial σ K)] MvPolynomial σ A) := by
  let T := MvPolynomial σ A ⊗[MvPolynomial σ K] MvPolynomial σ A
  let w : T := homogeneousLinearForm v ⊗ₜ[MvPolynomial σ K] (1 : MvPolynomial σ A) -
    (1 : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ K] homogeneousLinearForm v
  let I : Ideal T := Ideal.span {w}
  let d : σ → A ⊗[K] A := fun t => v t ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v t
  let J : Ideal (MvPolynomial σ (A ⊗[K] A)) := Ideal.span {homogeneousLinearForm d}
  let e := mvPolynomialTensorEquiv (R := K) (A := A) (B := A) (σ := σ)
  have hw : e w = homogeneousLinearForm d := by
    simp only [e, w, map_sub, mvPolynomialTensorEquiv_left, mvPolynomialTensorEquiv_right,
      homogeneousLinearForm, map_sum, map_mul, mvPolynomialMapOver_C, mvPolynomialMapOver_X,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [d]
    rw [map_sub]
    ring
  have hmap : I.map e.toRingHom = J := by
    change (Ideal.span {w}).map e.toRingHom = J
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {e w} = Ideal.span {homogeneousLinearForm d}
    rw [hw]
  have hJ : J.IsPrime := homogeneousLinearForm_isPrime_of_regularPair d i j hji hi hij
  have hI : I.IsPrime := by
    have hh := hJ.comap e.toRingHom
    rw [← hmap] at hh
    have hc := I.comap_map_of_bijective e.toRingHom e.bijective
    rw [hc] at hh
    exact hh
  let : I.IsPrime := hI
  let : IsDomain (T ⧸ I) := Ideal.Quotient.isDomain I
  obtain ⟨f⟩ := tensor_polynomial_relation (R := MvPolynomial σ K) (A := MvPolynomial σ A)
  rw [heq] at f
  exact f.symm.injective.isDomain f.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral

noncomputable section

end
end

end OAI
