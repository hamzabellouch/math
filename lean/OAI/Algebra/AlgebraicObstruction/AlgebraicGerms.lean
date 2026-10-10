import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.EtaleCharts

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α ι : Type} [Field K] [Finite α] [Fintype ι]

theorem common_chart_finite (v : ι → MvPowerSeries α K)
    (hv : ∀ i, Nonempty (LocalEtaleExpansion (v i))) :
    ∃ E : AffineEtaleChart K α, ∀ i, v i ∈ E.localExpansion.range := by
  obtain ⟨E,hE⟩ := common_affine_chart (Finset.univ.image v) (by
    intro φ hφ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hφ
    exact hv i)
  exact ⟨E,fun i ↦ E.localRange (hE _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))⟩

theorem germ_span_witness (v : ι → MvPowerSeries α K) (x : MvPowerSeries α K)
    (hv : ∀ i, Nonempty (LocalEtaleExpansion (v i)))
    (hx : Nonempty (LocalEtaleExpansion x))
    (hm : x ∈ Ideal.span (Set.range v)) :
    ∃ c : ι → MvPowerSeries α K, x = ∑ i, c i * v i ∧
      ∀ i, Nonempty (LocalEtaleExpansion (c i)) := by
  let w : Option ι → MvPowerSeries α K := fun e ↦ e.elim x v
  have hw : ∀ e, Nonempty (LocalEtaleExpansion (w e)) := by
    rintro (_ | i)
    · exact hx
    · exact hv i
  obtain ⟨E,hE⟩ := common_chart_finite w hw
  obtain ⟨xE,hxE⟩ := hE none
  change E.localExpansion xE = x at hxE
  have hvs : ∀ i, ∃ vi : E.LocalRing, E.localExpansion vi = v i := fun i ↦ hE (some i)
  choose vE hvE using hvs
  let I : Ideal E.LocalRing := Ideal.span (Set.range vE)
  let := E.localFaithfullyFlat
  have hI : I.map (algebraMap E.LocalRing (MvPowerSeries α K)) =
      Ideal.span (Set.range v) := by
    change (Ideal.span (Set.range vE)).map _ = _
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    exact congrArg Set.range (funext hvE)
  have hmE : xE ∈ I := by
    apply (BoundaryOnly.FormalObstruction.AlgebraicReplacement.etale_expansion_mem_iff (K := K) (α := α) I xE).mp
    rw [hI]
    change E.localExpansion xE ∈ _
    rw [hxE]
    exact hm
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmE
  refine ⟨fun i ↦ E.localExpansion (c i), ?_, fun i ↦ ⟨E.localGerm (c i)⟩⟩
  have hc' := congrArg E.localExpansion hc
  simp only [map_sum,map_mul,hvE] at hc'
  exact hxE.symm.trans hc'.symm

theorem germ_mul {x y : MvPowerSeries α K}
    (hx : Nonempty (LocalEtaleExpansion x)) (hy : Nonempty (LocalEtaleExpansion y)) :
    Nonempty (LocalEtaleExpansion (x*y)) := by
  let v : Bool → MvPowerSeries α K := fun b ↦ if b then x else y
  have hv : ∀ b, Nonempty (LocalEtaleExpansion (v b)) := by
    rintro (_ | _) <;> assumption
  obtain ⟨E,hE⟩ := common_chart_finite v hv
  obtain ⟨a,ha⟩ := hE true
  obtain ⟨b,hb⟩ := hE false
  change E.localExpansion a = x at ha
  change E.localExpansion b = y at hb
  have he : E.localExpansion (a*b) = x*y := by rw [map_mul,ha,hb]
  rw [← he]
  exact ⟨E.localGerm (a*b)⟩

theorem germ_square_witness (v : ι → MvPowerSeries α K) (x : MvPowerSeries α K)
    (hv : ∀ i, Nonempty (LocalEtaleExpansion (v i)))
    (hx : Nonempty (LocalEtaleExpansion x))
    (hm : x ∈ (Ideal.span (Set.range v))^2) :
    ∃ b : ι → ι → MvPowerSeries α K, x = ∑ i, ∑ j, b i j * v i * v j ∧
      ∀ i j, Nonempty (LocalEtaleExpansion (b i j)) := by
  have hI : (Ideal.span (Set.range v))^2 =
      Ideal.span (Set.range (fun ij : ι × ι ↦ v ij.1 * v ij.2)) := by
    rw [pow_two, Ideal.span_mul_span]
    congr 1
    ext z
    constructor
    · rintro ⟨a,⟨i,rfl⟩,b,⟨j,rfl⟩,rfl⟩
      exact ⟨(i,j),rfl⟩
    · rintro ⟨⟨i,j⟩,rfl⟩
      exact ⟨v i,⟨i,rfl⟩,v j,⟨j,rfl⟩,rfl⟩
  rw [hI] at hm
  obtain ⟨b,hb,hg⟩ := germ_span_witness (fun ij : ι × ι ↦ v ij.1 * v ij.2) x
    (fun ij ↦ germ_mul (hv ij.1) (hv ij.2)) hx hm
  refine ⟨fun i j ↦ b (i,j),?_,fun i j ↦ hg (i,j)⟩
  simpa only [Fintype.sum_prod_type,mul_assoc] using hb

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
open TensorProduct
variable {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

def extendDerivation (d : Derivation R S S) : Derivation R T T :=
  (((Algebra.linearMap S T).compDer d).liftKaehlerDifferential.liftBaseChange T ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

@[simp] theorem extendDerivation_algebraMap (d : Derivation R S S) (s : S) :
    extendDerivation (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  change ((Algebra.linearMap S T).compDer d).liftKaehlerDifferential.liftBaseChange T
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

theorem etale_derivation_ext [AddCommGroup M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R T M] [IsScalarTower S T M] [IsScalarTower R S M]
    (d e : Derivation R T M)
    (h : ∀ s : S, d (algebraMap S T s) = e (algebraMap S T s)) : d = e := by
  let k := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T
  have hl : d.liftKaehlerDifferential ∘ₗ k.toLinearMap =
      e.liftKaehlerDifferential ∘ₗ k.toLinearMap := by
    ext s
    simp [k,KaehlerDifferential.mapBaseChange_tmul,KaehlerDifferential.map_D,h]
  ext t
  obtain ⟨z,hz⟩ := k.surjective (KaehlerDifferential.D R T t)
  have hh := congrArg (fun f : T ⊗[S] KaehlerDifferential R S →ₗ[T] M ↦ f z) hl
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,hz,
    Derivation.liftKaehlerDifferential_comp_D] using hh

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {K α : Type} [Field K] [Finite α]

omit [Finite α] in
lemma polynomial_pderiv_expansion [Finite α] (p : MvPolynomial α K) (i : α) :
    pderiv i p.toMvPowerSeries = (MvPolynomial.pderiv i p).toMvPowerSeries := by
  classical
  induction p using MvPolynomial.induction_on with
  | C k => simp
  | add p q hp hq => simpa only [MvPolynomial.coe_add,map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
      simp only [MvPolynomial.coe_mul,MvPolynomial.coe_add,Derivation.leibniz,smul_eq_mul,
        MvPolynomial.pderiv_X,MvPolynomial.coe_X,pderiv_X,hp,Pi.single_apply]
      split_ifs <;> simp_all

noncomputable instance AffineEtaleChart.localCoeffAlgebra (E : AffineEtaleChart K α) :
    Algebra K E.LocalRing := Algebra.compHom E.LocalRing (algebraMap K (MvPolynomial α K))

instance AffineEtaleChart.localCoeffTower (E : AffineEtaleChart K α) :
    IsScalarTower K (MvPolynomial α K) E.LocalRing :=
  IsScalarTower.of_algebraMap_eq' rfl

instance AffineEtaleChart.localCompletionCoeffTower (E : AffineEtaleChart K α) :
    IsScalarTower K E.LocalRing (MvPowerSeries α K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro k
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial α K) E.LocalRing,
    ← IsScalarTower.algebraMap_apply (MvPolynomial α K) E.LocalRing (MvPowerSeries α K),
    ← IsScalarTower.algebraMap_apply K (MvPolynomial α K) (MvPowerSeries α K)]

noncomputable def AffineEtaleChart.deriv (E : AffineEtaleChart K α) (i : α) :
    Derivation K E.LocalRing E.LocalRing :=
  BoundaryOnly.FormalObstruction.AlgebraicReplacement.extendDerivation (MvPolynomial.pderiv i)

lemma AffineEtaleChart.expansion_deriv (E : AffineEtaleChart K α) (i : α) (x : E.LocalRing) :
    E.localExpansion (E.deriv i x) = pderiv i (E.localExpansion x) := by
  let d := (Algebra.linearMap E.LocalRing (MvPowerSeries α K)).compDer (E.deriv i)
  let e := (pderiv (R := K) i).compAlgebraMap E.LocalRing
  have hd : d = e := by
    apply BoundaryOnly.FormalObstruction.AlgebraicReplacement.etale_derivation_ext
      (S := MvPolynomial α K)
    intro p
    change algebraMap E.LocalRing (MvPowerSeries α K)
      (BoundaryOnly.FormalObstruction.AlgebraicReplacement.extendDerivation (MvPolynomial.pderiv i)
        (algebraMap (MvPolynomial α K) E.LocalRing p)) =
      pderiv i (algebraMap E.LocalRing (MvPowerSeries α K)
        (algebraMap (MvPolynomial α K) E.LocalRing p))
    rw [BoundaryOnly.FormalObstruction.AlgebraicReplacement.extendDerivation_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (polynomial_pderiv_expansion p i).symm
  exact Derivation.congr_fun hd x

theorem germ_pderiv {φ : MvPowerSeries α K}
    (hφ : Nonempty (LocalEtaleExpansion φ)) (i : α) :
    Nonempty (LocalEtaleExpansion (pderiv i φ)) := by
  obtain ⟨E,hE⟩ := hφ.some.affine
  obtain ⟨x,hx⟩ := E.localRange hE
  change E.localExpansion x = φ at hx
  rw [← hx, ← E.expansion_deriv]
  exact ⟨E.localGerm (E.deriv i x)⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped TensorProduct
variable {K α β : Type} [Field K] [Finite α] [Finite β]

lemma AffineEtaleChart.germ (E : AffineEtaleChart K α) {φ : MvPowerSeries α K}
    (h : φ ∈ E.expansion.range) : Nonempty (LocalEtaleExpansion φ) := by
  obtain ⟨x,hx⟩ := E.localRange h
  change E.localExpansion x = φ at hx
  rw [← hx]
  exact ⟨E.localGerm x⟩

lemma germ_polynomial (p : MvPolynomial α K) :
    Nonempty (LocalEtaleExpansion p.toMvPowerSeries) :=
  (AffineEtaleChart.base : AffineEtaleChart K α).germ ⟨p,rfl⟩

lemma germ_X (i : α) : Nonempty (LocalEtaleExpansion (X i : MvPowerSeries α K)) := by
  simpa using germ_polynomial (MvPolynomial.X i : MvPolynomial α K)

lemma germ_zero : Nonempty (LocalEtaleExpansion (0 : MvPowerSeries α K)) := by
  simpa using germ_polynomial (0 : MvPolynomial α K)

lemma germ_add {x y : MvPowerSeries α K}
    (hx : Nonempty (LocalEtaleExpansion x)) (hy : Nonempty (LocalEtaleExpansion y)) :
    Nonempty (LocalEtaleExpansion (x+y)) := by
  let v : Bool → MvPowerSeries α K := fun b ↦ if b then x else y
  have hv : ∀ b, Nonempty (LocalEtaleExpansion (v b)) := by
    rintro (_ | _) <;> assumption
  obtain ⟨E,hE⟩ := common_chart_finite v hv
  obtain ⟨a,ha⟩ := hE true
  obtain ⟨b,hb⟩ := hE false
  change E.localExpansion a = x at ha
  change E.localExpansion b = y at hb
  have he : E.localExpansion (a+b) = x+y := by rw [map_add,ha,hb]
  rw [← he]
  exact ⟨E.localGerm (a+b)⟩

lemma germ_neg {x : MvPowerSeries α K}
    (hx : Nonempty (LocalEtaleExpansion x)) :
    Nonempty (LocalEtaleExpansion (-x)) := by
  obtain ⟨E,⟨a,ha⟩⟩ := hx.some.affine
  apply E.germ
  exact ⟨-a,by simpa only [map_neg] using congrArg Neg.neg ha⟩

lemma germ_sub {x y : MvPowerSeries α K}
    (hx : Nonempty (LocalEtaleExpansion x)) (hy : Nonempty (LocalEtaleExpansion y)) :
    Nonempty (LocalEtaleExpansion (x-y)) := by
  rw [sub_eq_add_neg]
  exact germ_add hx (germ_neg hy)

lemma germ_sum {ι : Type*} (s : Finset ι) (v : ι → MvPowerSeries α K)
    (hv : ∀ i ∈ s, Nonempty (LocalEtaleExpansion (v i))) :
    Nonempty (LocalEtaleExpansion (∑ i ∈ s, v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (germ_zero (K := K) (α := α))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact germ_add (hv i (Finset.mem_insert_self _ _))
        (ih (fun j hj ↦ hv j (Finset.mem_insert_of_mem hj)))

theorem germ_subst {φ : MvPowerSeries α K} (u : α → MvPowerSeries β K)
    (hφ : Nonempty (LocalEtaleExpansion φ))
    (hu : ∀ i, Nonempty (LocalEtaleExpansion (u i)))
    (hc : ∀ i, constantCoeff (u i) = 0) :
    Nonempty (LocalEtaleExpansion (subst u φ)) := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨E,x,hx⟩ := hφ.some.affine
  obtain ⟨F,hF⟩ := common_affine_chart (Finset.univ.image u) (by
    intro ψ hψ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hu i)
  have hv : ∀ i, ∃ v : F.S, F.expansion v = u i := fun i ↦
    hF _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  choose v hv using hv
  let f : MvPolynomial α K →+* F.S := MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial β K) F.S).comp MvPolynomial.C) v
  let g : MvPolynomial α K →+* MvPowerSeries β K := MvPolynomial.eval₂Hom C u
  let : Algebra (MvPolynomial α K) F.S := f.toAlgebra
  let : Algebra (MvPolynomial α K) (MvPowerSeries β K) := g.toAlgebra
  let fF : F.S →ₐ[MvPolynomial α K] MvPowerSeries β K :=
    ⟨F.expansion.toRingHom, by
      intro p
      change F.expansion (f p) = g p
      induction p using MvPolynomial.induction_on with
      | C k =>
          simp only [f,g,MvPolynomial.eval₂Hom_C,RingHom.comp_apply]
          have hk := F.expansion.commutes (MvPolynomial.C k)
          change _ = (MvPolynomial.C k).toMvPowerSeries at hk
          simpa using hk
      | add p q hp hq => simp only [map_add,hp,hq]
      | mul_X p i hp => simp only [map_mul,f,g,MvPolynomial.eval₂Hom_X',hv,hp]⟩
  let su := substAlgHom (R := K) (hasSubst_of_constantCoeff_zero hc)
  let fE : E.S →ₐ[MvPolynomial α K] MvPowerSeries β K :=
    ⟨su.toRingHom.comp E.expansion.toRingHom, by
      intro p
      change su (E.expansion (algebraMap (MvPolynomial α K) E.S p)) = g p
      rw [E.expansion.commutes]
      change substAlgHom (R := K) (hasSubst_of_constantCoeff_zero hc) p.toMvPowerSeries = g p
      rw [substAlgHom_coe]
      rfl⟩
  let : SMulCommClass (MvPolynomial α K) (MvPolynomial β K) F.S :=
    ⟨fun scalarLeft scalarRight element ↦ by simp only [Algebra.smul_def, mul_left_comm]⟩
  let T := F.S ⊗[MvPolynomial α K] E.S
  let : Algebra (MvPolynomial β K) T := Algebra.TensorProduct.leftAlgebra
  let t : T →ₐ[MvPolynomial α K] MvPowerSeries β K :=
    Algebra.TensorProduct.lift fF fE (fun _ _ ↦ Commute.all _ _)
  let : Algebra.Etale (MvPolynomial β K) T := Algebra.Etale.comp (MvPolynomial β K) F.S T
  let H : AffineEtaleChart K β :=
    ⟨T,inferInstance,inferInstance,inferInstance,
     ⟨t.toRingHom,by
       intro p
       rw [IsScalarTower.algebraMap_apply (MvPolynomial β K) F.S T]
       change fF (algebraMap (MvPolynomial β K) F.S p) * fE 1 = _
       rw [map_one,mul_one]
       exact F.expansion.commutes p⟩⟩
  apply H.germ
  refine ⟨Algebra.TensorProduct.includeRight x,?_⟩
  change fF 1 * fE x = subst u φ
  rw [map_one,one_mul]
  change su (E.expansion x) = subst u φ
  rw [show E.expansion x = φ from hx]
  exact congrFun (coe_substAlgHom (R := K) (hasSubst_of_constantCoeff_zero hc)) φ

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
