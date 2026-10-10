import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.WitnessDescent

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α ι σ : Type*} [CommRing K]

def centerPolynomial (e : σ ≃ ι) (c : ι → K) :
    MvPolynomial ι (MvPolynomial α K) →+* MvPolynomial (α ⊕ σ) K :=
  MvPolynomial.eval₂Hom (MvPolynomial.rename Sum.inl).toRingHom
    (fun i => MvPolynomial.C (c i) + MvPolynomial.X (Sum.inr (e.symm i)))

def pointEval (c : ι → K) : MvPolynomial ι (MvPolynomial α K) →+* K :=
  MvPolynomial.eval₂Hom MvPolynomial.constantCoeff c

theorem pderiv_rename_inl (j : σ) (p : MvPolynomial α K) :
    MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.rename Sum.inl p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p a h => simp [Derivation.leibniz,h,MvPolynomial.pderiv_X]

theorem centerPolynomial_derivative (e : σ ≃ ι) (c : ι → K)
    (p : MvPolynomial ι (MvPolynomial α K)) (j : σ) :
    MvPolynomial.pderiv (Sum.inr j) (centerPolynomial e c p) =
      centerPolynomial e c (MvPolynomial.pderiv (e j) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [centerPolynomial,MvPolynomial.eval₂Hom,pderiv_rename_inl]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p a h =>
      simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,h]
      simp only [centerPolynomial,MvPolynomial.pderiv_X]
      have he : e.symm a = j ↔ a = e j := by
        constructor
        · intro h; simpa using congrArg e h
        · intro h; simp [h]
      simp [Pi.single_apply,he,apply_ite]

theorem centerPolynomial_constant (e : σ ≃ ι) (c : ι → K)
    (p : MvPolynomial ι (MvPolynomial α K)) :
    (centerPolynomial e c p).coeff 0 = pointEval c p := by
  change MvPolynomial.constantCoeff (centerPolynomial e c p) = pointEval c p
  have hh : MvPolynomial.constantCoeff.comp (centerPolynomial (α := α) e c) = pointEval c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [centerPolynomial,pointEval,MvPolynomial.eval₂Hom]
    · intro i
      simp [centerPolynomial,pointEval,MvPolynomial.eval₂Hom]
  exact congrArg (fun h => h p) hh

theorem centerPolynomial_linear (e : σ ≃ ι) (c : ι → K)
    (p : MvPolynomial ι (MvPolynomial α K)) (j : σ) :
    (centerPolynomial e c p).coeff (Finsupp.single (Sum.inr j) 1) =
      pointEval c (MvPolynomial.pderiv (e j) p) := by
  rw [← centerPolynomial_constant e c,← centerPolynomial_derivative e c]
  simp [MvPolynomial.coeff_pderiv]

theorem centerPolynomial_solution [Finite α] [Finite σ] (e : σ ≃ ι) (c : ι → K)
    (z : ι → MvPowerSeries α K) (hz : ∀ i, constantCoeff (z i) = c i)
    (p : MvPolynomial ι (MvPolynomial α K)) :
    subst (Sum.elim X (fun j => z (e j) - C (c (e j))))
      (centerPolynomial e c p).toMvPowerSeries =
    MvPolynomial.eval₂ MvPolynomial.coeToMvPowerSeries.ringHom z p := by
  have hc : ∀ j, constantCoeff
      (Sum.elim X (fun j => z (e j) - C (c (e j))) j) = 0 := by
    intro j; cases j <;> simp [hz]
  let hs := hasSubst_of_constantCoeff_zero hc
  rw [← substAlgHom_apply hs,substAlgHom_coe]
  have hh : (MvPolynomial.aeval (Sum.elim X
      (fun j => z (e j) - C (c (e j))))).toRingHom.comp (centerPolynomial e c) =
      MvPolynomial.eval₂Hom MvPolynomial.coeToMvPowerSeries.ringHom z := by
    apply MvPolynomial.ringHom_ext
    · intro a
      induction a using MvPolynomial.induction_on with
      | C r => simp [centerPolynomial,MvPolynomial.eval₂Hom,MvPowerSeries.algebraMap_apply]
      | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
      | mul_X p j hp =>
          simpa [centerPolynomial,MvPolynomial.eval₂Hom] using (congrArg (· * X j) hp)
    · intro i
      simp [centerPolynomial,MvPolynomial.eval₂Hom,MvPowerSeries.algebraMap_apply]
  exact congrArg (fun h => h p) hh

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α ι σ S : Type*} [CommRing K] [Fintype α]
  [CommRing S] [Algebra (MvPolynomial α K) S] [Fintype ι] [Fintype σ]

theorem finite_ring_submersive
    (P : Algebra.SubmersivePresentation (MvPolynomial α K) S ι σ)
    (hdim : P.dimension = 0) (f : S →+* MvPowerSeries α K)
    (hf : ∀ p : MvPolynomial α K, f (algebraMap _ S p) = p.toMvPowerSeries)
    (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ ∀ i, coefficientsIn R (f (P.val i)) := by
  have hcard : Nat.card ι ≤ Nat.card σ := by
    exact Nat.sub_eq_zero_iff_le.mp hdim
  let e : σ ≃ ι := Equiv.ofBijective P.map (P.map_inj.bijective_of_nat_card_le hcard)
  let z : ι → MvPowerSeries α K := fun i => f (P.val i)
  let c : ι → K := fun i => constantCoeff (z i)
  let w : σ → MvPowerSeries α K := fun j => z (e j) - C (c (e j))
  let F : σ → MvPolynomial (α ⊕ σ) K := fun j => centerPolynomial e c (P.relation j)
  let ev : MvPolynomial ι (MvPolynomial α K) →+* MvPowerSeries α K :=
    f.comp (MvPolynomial.aeval P.val).toRingHom
  have hev : ev = MvPolynomial.eval₂Hom MvPolynomial.coeToMvPowerSeries.ringHom z := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simpa [ev] using hf p
    · intro i; simp [ev,z]
  have hpoint : pointEval c = constantCoeff.comp ev := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp only [pointEval,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,hev,
        MvPolynomial.eval₂Hom_C]
      rfl
    · intro i; simp [pointEval,ev,c,z]
  have hF0 : ∀ j, (F j).coeff 0 = 0 := by
    intro j
    rw [show F j = centerPolynomial e c (P.relation j) from rfl,
      centerPolynomial_constant,hpoint]
    simp [ev,P.aeval_val_relation]
  have hw : ∀ j, constantCoeff (w j) = 0 := by intro j; simp [w,c]
  have hF : ∀ j, subst (Sum.elim X w) (F j).toMvPowerSeries = 0 := by
    intro j
    rw [show F j = centerPolynomial e c (P.relation j) from rfl,
      centerPolynomial_solution e c z (fun _ => rfl)]
    change MvPolynomial.eval₂Hom MvPolynomial.coeToMvPowerSeries.ringHom z (P.relation j) = 0
    rw [← hev]
    simp [ev,P.aeval_val_relation]
  have hJ : internalJacobian F =
      ((constantCoeff.comp ev).mapMatrix P.jacobiMatrix).transpose := by
    ext i j
    change (F i).coeff (Finsupp.single (Sum.inr j) 1) = _
    rw [show F i = centerPolynomial e c (P.relation i) from rfl,centerPolynomial_linear,hpoint]
    simp [Matrix.transpose_apply,RingHom.mapMatrix_apply,P.jacobiMatrix_apply,e]
  have hdet : IsUnit (internalJacobian F).det := by
    rw [hJ,Matrix.det_transpose,← RingHom.map_det]
    have hunit := P.jacobian_isUnit.map (constantCoeff.comp f)
    simpa only [P.jacobian_eq_jacobiMatrix_det,P.algebraMap_eq,RingHom.comp_apply,ev,
      AlgHom.toRingHom_eq_coe] using hunit
  obtain ⟨R,hR,hconst,hwR⟩ := finite_ring_nonsingular F hF0 hdet
    (constants ∪ Finset.univ.image c) w hw hF
  refine ⟨R,hR,fun x hx => hconst x (Finset.mem_union_left _ hx),?_⟩
  intro i d
  have hc : c i ∈ R := hconst (c i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,by simp,rfl⟩))
  have hh : f (P.val i) = w (e.symm i) + C (c i) := by simp [w,z]
  rw [hh,map_add]
  apply R.add_mem (hwR _ d)
  by_cases hd : d = 0
  · simpa [hd] using hc
  · simp [coeff_C,hd,R.zero_mem]

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α ι : Type*} [CommRing K]

def seriesCoefficientRing (R : Subalgebra ℤ K) : Subring (MvPowerSeries α K) where
  carrier := {f | coefficientsIn R f}
  zero_mem' := by intro e; simp [R.zero_mem]
  one_mem' := by
    intro e
    by_cases he : e = 0 <;> simp [coeff_one,he,R.zero_mem,R.one_mem]
  add_mem' := by intro f g hf hg e; simpa using R.add_mem (hf e) (hg e)
  mul_mem' := by
    intro f g hf hg e
    rw [coeff_mul]
    exact R.sum_mem (fun x hx => R.mul_mem (hf x.1) (hg x.2))
  neg_mem' := by intro f hf e; simpa using R.neg_mem (hf e)

theorem nested_polynomial_finite_coefficients
    (p : MvPolynomial ι (MvPolynomial α K)) :
    ∃ s : Finset K, ∀ d e, (p.coeff d).coeff e = 0 ∨ (p.coeff d).coeff e ∈ s := by
  refine ⟨p.support.biUnion (fun d => (p.coeff d).coeffs),?_⟩
  intro d e
  by_cases hz : (p.coeff d).coeff e = 0
  · exact Or.inl hz
  · right
    apply Finset.mem_biUnion.mpr
    refine ⟨d,?_,MvPolynomial.coeff_mem_coeffs e hz⟩
    apply MvPolynomial.mem_support_iff.mpr
    intro h
    simp [h] at hz

theorem coefficientsIn_polynomial_eval (R : Subalgebra ℤ K)
    (p : MvPolynomial ι (MvPolynomial α K))
    (hp : ∀ d e, (p.coeff d).coeff e ∈ R)
    (z : ι → MvPowerSeries α K) (hz : ∀ i, coefficientsIn R (z i)) :
    coefficientsIn R (MvPolynomial.eval₂ MvPolynomial.coeToMvPowerSeries.ringHom z p) := by
  change MvPolynomial.eval₂ _ z p ∈ seriesCoefficientRing R
  rw [MvPolynomial.eval₂_eq]
  apply (seriesCoefficientRing R).sum_mem
  intro d hd
  apply (seriesCoefficientRing R).mul_mem
  · change ∀ e, coeff e (p.coeff d).toMvPowerSeries ∈ R
    exact hp d
  · apply (seriesCoefficientRing R).prod_mem
    intro i hi
    exact (seriesCoefficientRing R).pow_mem (hz i) _

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α S : Type*} [CommRing K] [Fintype α]
  [CommRing S] [Algebra (MvPolynomial α K) S]

theorem finite_ring_etale_image [Algebra.Etale (MvPolynomial α K) S]
    (f : S →+* MvPowerSeries α K)
    (hf : ∀ p : MvPolynomial α K, f (algebraMap _ S p) = p.toMvPowerSeries)
    (s : S) (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ coefficientsIn R (f s) := by
  have hh : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial α K) S :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι,σ,hσ,hι,P,hdim⟩ := hh.out
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  obtain ⟨c,hc⟩ := nested_polynomial_finite_coefficients (P.σ s)
  obtain ⟨R,hR,hconst,hval⟩ := finite_ring_submersive P hdim f hf (constants ∪ c)
  refine ⟨R,hR,fun x hx => hconst x (Finset.mem_union_left _ hx),?_⟩
  have hev : f.comp (MvPolynomial.aeval P.val).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.coeToMvPowerSeries.ringHom (fun i => f (P.val i)) := by
    apply MvPolynomial.ringHom_ext
    · intro p; simpa using hf p
    · intro i; simp
  have heq := congrArg (fun h => h (P.σ s)) hev
  change f ((MvPolynomial.aeval P.val) (P.σ s)) = _ at heq
  rw [P.aeval_val_σ] at heq
  rw [heq]
  apply coefficientsIn_polynomial_eval R (P.σ s) _ _ hval
  intro d e
  rcases hc d e with hz | hm
  · rw [hz]; exact R.zero_mem
  · exact hconst _ (Finset.mem_union_right _ hm)

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {K α S L : Type*} [CommRing K] [Fintype α]
  [CommRing S] [Algebra (MvPolynomial α K) S]
  [CommRing L] [Algebra S L] [Algebra (MvPolynomial α K) L]
  [IsScalarTower (MvPolynomial α K) S L]

theorem finite_ring_etale_localization [Algebra.Etale (MvPolynomial α K) S]
    (M : Submonoid S) [IsLocalization M L]
    (f : L →+* MvPowerSeries α K)
    (hf : ∀ p : MvPolynomial α K, f (algebraMap _ L p) = p.toMvPowerSeries)
    (s : L) (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ coefficientsIn R (f s) := by
  obtain ⟨x,y,rfl⟩ := IsLocalization.exists_mk'_eq M s
  let T := Localization.Away (y : S)
  let g := f.comp (algebraMap S L)
  have hu : IsUnit (g y) := (IsLocalization.map_units L y).map f
  let H : T →+* MvPowerSeries α K := IsLocalization.Away.lift (y : S) hu
  let y' : Submonoid.powers (y : S) := ⟨y,⟨1,by simp⟩⟩
  let s' : T := IsLocalization.mk' T x y'
  let : Algebra.Etale (MvPolynomial α K) T := Algebra.Etale.comp (MvPolynomial α K) S T
  have hH (p : MvPolynomial α K) : H (algebraMap _ T p) = p.toMvPowerSeries := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial α K) S T,
      IsLocalization.Away.lift_eq]
    change f (algebraMap S L (algebraMap (MvPolynomial α K) S p)) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact hf p
  have hs : H s' = f (IsLocalization.mk' L x y) := by
    apply hu.mul_right_cancel
    have h₁ := congrArg H (IsLocalization.mk'_spec T x y')
    have h₂ := congrArg f (IsLocalization.mk'_spec L x y)
    simp only [map_mul,IsLocalization.Away.lift_eq,H,y'] at h₁
    simpa only [map_mul,g,RingHom.comp_apply] using h₁.trans h₂.symm
  rw [← hs]
  exact finite_ring_etale_image H hH s' constants

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries

structure LocalEtaleExpansion {K α : Type*} [CommRing K]
    (φ : MvPowerSeries α K) where
  S : Type
  L : Type
  ringS : CommRing S
  baseS : Algebra (MvPolynomial α K) S
  etale : Algebra.Etale (MvPolynomial α K) S
  ringL : CommRing L
  fromS : Algebra S L
  baseL : Algebra (MvPolynomial α K) L
  tower : IsScalarTower (MvPolynomial α K) S L
  denominators : Submonoid S
  localization : IsLocalization denominators L
  expansion : L →+* MvPowerSeries α K
  coordinates : ∀ p : MvPolynomial α K,
    expansion (algebraMap _ L p) = p.toMvPowerSeries
  germ : L
  represents : expansion germ = φ

attribute [instance] LocalEtaleExpansion.ringS LocalEtaleExpansion.baseS
  LocalEtaleExpansion.etale LocalEtaleExpansion.ringL LocalEtaleExpansion.fromS
  LocalEtaleExpansion.baseL LocalEtaleExpansion.tower LocalEtaleExpansion.localization

theorem LocalEtaleExpansion.finite_coefficients {K α : Type*} [CommRing K]
    [Fintype α] {φ : MvPowerSeries α K} (E : LocalEtaleExpansion φ)
    (constants : Finset K) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      (∀ c ∈ constants, c ∈ R) ∧ coefficientsIn R φ := by
  rw [← E.represents]
  exact finite_ring_etale_localization E.denominators E.expansion E.coordinates E.germ constants

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection
open scoped Classical
variable {K : Type*} [CommRing K] {d : ℕ} {n : Fin d → ℕ}

theorem QuadraticWitnesses.finite_ring_etale (Q : QuadraticData (R := K) (n := n))
    (W : QuadraticWitnesses Q)
    (h : ∀ e, LocalEtaleExpansion (W.entry Q e)) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      Nonempty (QuadraticData (R := R) (n := n)) := by
  obtain ⟨inv,hi⟩ := isUnit_iff_exists_inv.mp Q.complementary
  have hf : ∀ e, ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      coefficientsIn R (W.entry Q e) := by
    intro e
    obtain ⟨R,hR,_,he⟩ := (h e).finite_coefficients ∅
    exact ⟨R,hR,he⟩
  obtain ⟨R,hR,hc,he⟩ := finite_coefficient_family (W.entry Q) hf {inv}
  refine ⟨R,hR,W.descend Q R (fun i => he (.wall i)) (fun c => he (.graph c))
    (fun c e => he (.quadratic c e)) (fun t c => he (.positive t c))
    (fun t c => he (.negative t c)) inv (hc inv (Finset.mem_singleton_self inv)) hi⟩

theorem no_etale_quadratic_data [IsDomain K] [CharZero K] (hd : 5 ≤ d)
    (Q : QuadraticData (R := K) (n := n)) (W : QuadraticWitnesses Q)
    (h : ∀ e, LocalEtaleExpansion (W.entry Q e)) : False := by
  obtain ⟨R,hR,hQ⟩ := W.finite_ring_etale Q h
  let : Algebra.FiniteType ℤ R := hR
  exact no_integral_quadratic_data R d hd n hQ

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
