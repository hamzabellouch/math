import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import OAI.NumberTheory.SiegelZeros.Hilbert.ConeHomogeneousEquations
import OAI.NumberTheory.SiegelZeros.Intersection.PrimeHypersurfaceEquidimension
import OAI.NumberTheory.SiegelZeros.Intersection.RetainedIntersectionCycles
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedOneCutPropagation

namespace OAI

section

noncomputable section

namespace SiegelZeros.W17.ConeLocalLength

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mapped_minimalPrime_of_prime_extension
    (f : A →+* B) {I P : Ideal A} (hP : P ∈ I.minimalPrimes)
    (hprime : (P.map f).IsPrime) (hcontract : (P.map f).comap f = P) :
    P.map f ∈ (I.map f).minimalPrimes := by
  refine ⟨⟨hprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  apply Ideal.map_le_iff_le_comap.mpr
  apply hP.2 ⟨hQ.1.comap f, Ideal.map_le_iff_le_comap.mp hQ.2⟩
  exact (Ideal.comap_mono hQP).trans hcontract.le

theorem minimalPrime_isHomogeneous {k σ : Type*} [CommRing k]
    (I Q : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := k)
  let C := Q.homogeneousCore (MvPolynomial.homogeneousSubmodule σ k)
  have hIC : I ≤ C.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hQC : Q ≤ C.toIdeal := hQ.2 ⟨hQ.1.1.homogeneousCore, hIC⟩ hCQ
  have heq : C.toIdeal = Q := le_antisymm hCQ hQC
  exact heq ▸ C.isHomogeneous

end General

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrime_minimal_over_homogenized {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    conePrime k σ P ∈
      (Ideal.span (Set.range (fun i => WeightedTorusJets.W22.homogenize (f i)))).minimalPrimes := by
  let H := Ideal.span (Set.range (fun i => WeightedTorusJets.W22.homogenize (f i)))
  have hLP : laurentPrime (AffineRing k σ) P ∈ (H.map (coneToLaurent k σ)).minimalPrimes := by
    rw [map_homogenized_span_eq_laurent_span k σ f]
    exact mapped_minimalPrime_of_prime_extension LaurentPolynomial.C hP inferInstance
      (laurentPrime_comap (AffineRing k σ) P)
  have hcomp : coneToLaurent k σ = (coneLaurentEquiv k σ).toRingHom.comp
      (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    apply RingHom.ext
    intro F
    exact (coneAwayToLaurent_algebraMap k σ F).symm
  have hI : (H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom =
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    rw [hcomp, ← Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv]
    apply Ideal.ext
    intro z
    change (coneLaurentEquiv k σ).symm ((coneLaurentEquiv k σ) z) ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) ↔ z ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ))
    rw [RingEquiv.symm_apply_apply]
  have hchart := Ideal.minimalPrimes_comap_of_surjective
    (coneLaurentEquiv k σ).surjective hLP
  change awayChartPrime k σ P ∈
    ((H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom).minimalPrimes at hchart
  rw [hI, IsLocalization.minimalPrimes_map
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (ConeAway k σ)] at hchart
  exact hchart

theorem homogenized_span_isHomogeneous {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => WeightedTorusJets.W22.homogenize (f i)))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option σ) k) := by
  let := MvPolynomial.gradedAlgebra (σ := Option σ) (R := k)
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option σ) k)
  rintro F ⟨i, rfl⟩
  exact ⟨(f i).totalDegree, WeightedTorusJets.W22.homogenize_isHomogeneous (f i)⟩

theorem conePrime_isHomogeneous_of_minimal {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    (conePrime k σ P).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) k) :=
  minimalPrime_isHomogeneous _ _ (homogenized_span_isHomogeneous k σ f)
    (conePrime_minimal_over_homogenized k σ P f hP)

section Height

variable [IsNoetherianRing (AffineRing k σ)]

theorem laurentPrime_height_eq :
    (laurentPrime (AffineRing k σ) P).height = P.height := by
  let : IsNoetherianRing (LaurentChart k σ) :=
    IsLocalization.isNoetherianRing
      (Submonoid.powers (Polynomial.X : Polynomial (AffineRing k σ)))
      (LaurentChart k σ) inferInstance
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    P (laurentPrime (AffineRing k σ) P)
  change (laurentPrime (AffineRing k σ) P).height = P.height +
    ((laurentPrime (AffineRing k σ) P).map
      (Ideal.Quotient.mk (laurentPrime (AffineRing k σ) P))).height at h
  simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h

theorem conePrime_height_eq : (conePrime k σ P).height = P.height := by
  change ((awayChartPrime k σ P).comap
    (algebraMap (ConeRing k σ) (ConeAway k σ))).height = P.height
  rw [IsLocalization.height_under
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))]
  change ((laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom).height = _
  exact ((coneLaurentEquiv k σ).height_comap (laurentPrime (AffineRing k σ) P)).trans
    (laurentPrime_height_eq k σ P)

end Height
end SiegelZeros.W17.ConeLocalLength

end

end

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

def RetainedMinimalPrime (I T : Ideal (MvPolynomial σ k)) :=
  {Q : Ideal (MvPolynomial σ k) // Q ∈ I.minimalPrimes ∧ Q ≤ T}

namespace RetainedMinimalPrime

variable {I T : Ideal (MvPolynomial σ k)}

noncomputable instance finiteFamily (I T : Ideal (MvPolynomial σ k)) :
    Fintype (RetainedMinimalPrime I T) := by
  have hfinite : {Q : Ideal (MvPolynomial σ k) | Q ∈ I.minimalPrimes ∧ Q ≤ T}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ k) I).subset
      (fun _ h => h.1)
  exact hfinite.fintype

instance (Q : RetainedMinimalPrime I T) : Q.val.IsPrime := Q.property.1.1.1

noncomputable def toComponent
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    ProjectiveComponent k σ :=
  ⟨Q.val, Q.property.1.1.1,
    SiegelZeros.W17.ConeLocalLength.minimalPrime_isHomogeneous I Q.val hI Q.property.1,
    v, fun h => hv (Q.property.2 h)⟩

omit [Fintype σ] in
@[simp] theorem toComponent_val
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    (toComponent hI v hv Q).val = Q.val := rfl

omit [Fintype σ] in
theorem toComponent_injective
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) :
    Function.Injective (toComponent hI v hv : RetainedMinimalPrime I T → ProjectiveComponent k σ) := by
  intro Q R h
  exact Subtype.ext (congrArg (fun P : ProjectiveComponent k σ => P.val) h)

end RetainedMinimalPrime

namespace RetainedPrimeCycle

noncomputable def canonicalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) : ProperCut C where
  polynomial := f
  polynomialDegree := d
  positiveDegree := hd
  homogeneous := hf
  avoidsParent := havoid
  dimensionIndex := s
  parentDegree := hparent
  Child := fun a => RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T
  finiteChild := fun _ => inferInstance
  child := fun a => RetainedMinimalPrime.toComponent
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  distinctChild := fun a => RetainedMinimalPrime.toComponent_injective
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  minimalChild := fun _ Q => Q.property.1
  childDegree := fun a Q => actualHP_natDegree_of_prime_dimension Q.val
    (RetainedMinimalPrime.toComponent
      (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv Q).homogeneous
    v (fun h => hv (Q.property.2 h)) s (hchildDim a Q)

theorem canonicalRetainedCut_covers
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) :
    (canonicalRetainedCut C f d hd hf havoid s hparent T v hv hchildDim).CoversBelow T := by
  intro a Q hQ hQT
  exact ⟨⟨Q, hQ, hQT⟩, rfl⟩

theorem canonicalRetainedCut_next_le_target
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) :
    ∀ x, ((canonicalRetainedCut C f d hd hf havoid s hparent T v hv hchildDim).next.component x).val ≤ T := by
  intro x
  exact x.2.property.2

end RetainedPrimeCycle
end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22.RetainedPrimeCycle

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem retainedChild_dimension
    (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
    (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
    (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (a : C.Index)
    (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
    ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ) := by
  obtain ⟨N, hN⟩ := actualHP_eventually (C.component a).val (C.component a).homogeneous
  have hPdim := W24.prime_hilbert_natDegree_add_one_eq_krullDim (C.component a).val
    (C.component a).homogeneous (C.component a).coordinate (C.component a).coordinate_not_mem
    (actualHP (C.component a).val (C.component a).homogeneous) (N+1)
    (fun n hn => (hN n (by omega)).symm)
  have hdim : ringKrullDim (MvPolynomial σ k ⧸ (C.component a).val) = (s+2 : ℕ) := by
    calc
      _ = ((actualHP (C.component a).val (C.component a).homogeneous).natDegree + 1 :
          WithBot ℕ∞) := hPdim.symm
      _ = ((s+2 : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by rw [hparent a])
  exact W24.minimal_prime_hypersurface_dimension k σ (C.component a).val Q.val f
    (havoid a) (by simpa only [sup_comm] using Q.property.1) s hdim

noncomputable def equidimensionalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) : ProperCut C :=
  canonicalRetainedCut C f d hd hf havoid s hparent T v hv
    (retainedChild_dimension C f havoid s hparent T)

theorem equidimensionalRetainedCut_covers
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    (equidimensionalRetainedCut C f d hd hf havoid s hparent T v hv).CoversBelow T :=
  canonicalRetainedCut_covers C f d hd hf havoid s hparent T v hv
    (retainedChild_dimension C f havoid s hparent T)

end WeightedTorusJets.W22.RetainedPrimeCycle

end

section

namespace WeightedTorusJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem minimal_cut_of_intermediate_parent
    {A : Type*} [CommRing A] (I P Q : Ideal A) (x : A)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) (hIP : I ≤ P) (hPQ : P ≤ Q) :
    Q ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨hQ.1.1, sup_le hPQ (le_sup_right.trans hQ.1.2)⟩, ?_⟩
  intro K hK hKQ
  exact hQ.2 ⟨hK.1, (sup_le_sup hIP le_rfl).trans hK.2⟩ hKQ

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem cut_ideal_homogeneous
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d) :
    (I ⊔ Ideal.span {x}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  simpa only [sup_comm] using primeCut_isHomogeneous I hI x hx

theorem natural_local_onecut_recurrence
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) x))) :
    actualLocalLength (I ⊔ Ideal.span {x}) Q =
      ∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q := by
  have hrec := localized_onecut_parent_recurrence I Q x hdim hregular
  have hsum : globalParentCutSum I Q x =
      ((∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q : ℕ) : ℕ∞) := by
    unfold globalParentCutSum
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hP := SiegelZeros.W17.ConeLocalLength.minimalPrime_isHomogeneous
      I P.val hI P.property.1
    have hQP := minimal_cut_of_intermediate_parent I P.val Q x hQ
      P.property.1.1.2 P.property.2
    rw [actualLocalLength_spec I P.val hI P.property.1,
      actualLocalLength_spec (P.val ⊔ Ideal.span {x}) Q
        (cut_ideal_homogeneous P.val hP x hx) hQP, Nat.cast_mul]
  rw [actualLocalLength_spec (I ⊔ Ideal.span {x}) Q
    (cut_ideal_homogeneous I hI x hx) hQ, hsum] at hrec
  exact_mod_cast hrec

noncomputable def parentChildIncidenceEquiv
    (I T : Ideal (MvPolynomial σ k)) (x : MvPolynomial σ k) :
    (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T, MinimalParentsBelow I Q.val) ≃
      (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}) where
  toFun z := ⟨⟨z.2.val, z.2.property.1, z.2.property.2.trans z.1.property.2⟩,
    z.1, z.2.property.2⟩
  invFun z := ⟨z.2.val, z.1.val, z.1.property.1, z.2.property⟩
  left_inv := by rintro ⟨Q,P⟩; rfl
  right_inv := by rintro ⟨P,Q⟩; rfl

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def actualMultiplicityCycle
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    RetainedPrimeCycle.{u,u,u} k σ where
  Index := RetainedMinimalPrime I T
  finiteIndex := inferInstance
  component := RetainedMinimalPrime.toComponent hI v hv
  coefficient := fun P => actualLocalLength I P.val

theorem actualMultiplicityCycle_coefficient
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (P : RetainedMinimalPrime I T) :
    (actualMultiplicityCycle I hI T v hv).coefficientAt
      (RetainedMinimalPrime.toComponent hI v hv P) = actualLocalLength I P.val := by
  unfold RetainedPrimeCycle.coefficientAt
  change (∑ Q : RetainedMinimalPrime I T,
    if RetainedMinimalPrime.toComponent hI v hv Q = RetainedMinimalPrime.toComponent hI v hv P
      then actualLocalLength I Q.val else 0) = _
  rw [Finset.sum_eq_single P]
  · exact ite_eq_left rfl
  · intro Q _ hQP
    exact ite_eq_right (fun h => hQP (RetainedMinimalPrime.toComponent_injective hI v hv h))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ P))

theorem actualMultiplicityCycle_cut_expansion
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree =
      ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
          (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
          (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree := by
  let D := actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv
  have hrec (Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T) :=
    natural_local_onecut_recurrence I Q.val hI x hx Q.property.1 (hdim Q) (hregular Q)
  calc
    D.degree = ∑ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        ∑ P : MinimalParentsBelow I Q.val,
          (actualLocalLength I P.val : ℚ) *
            (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val : ℚ) *
              (D.component Q).hilbertDegree := by
      unfold RetainedPrimeCycle.degree
      apply Finset.sum_congr rfl
      intro Q _
      change RetainedMinimalPrime (I ⊔ Ideal.span {x}) T at Q
      change (actualLocalLength (I ⊔ Ideal.span {x}) Q.val : ℚ) * (D.component Q).hilbertDegree = _
      rw [hrec Q, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      rw [Nat.cast_mul]
    _ = ∑ z : (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        MinimalParentsBelow I Q.val),
          (actualLocalLength I z.2.val : ℚ) *
            (actualLocalLength (z.2.val ⊔ Ideal.span {x}) z.1.val : ℚ) *
              (D.component z.1).hilbertDegree := by rw [Fintype.sum_sigma]
    _ = ∑ z : (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}),
          (actualLocalLength I z.1.val : ℚ) *
            (actualLocalLength (z.1.val ⊔ Ideal.span {x}) z.2.val.val : ℚ) *
              (D.component z.2.val).hilbertDegree := by
      apply Fintype.sum_equiv (parentChildIncidenceEquiv I T x)
      intro z
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.mul_sum, mul_assoc, D, actualMultiplicityCycle]

theorem actualMultiplicityCycle_parent_budget
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (P : RetainedMinimalPrime I T) :
    (∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
      (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
        (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree) ≤
      (d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree := by
  let C := actualMultiplicityCycle I hI T v hv
  let Qs := {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}
  let Q : Qs → Ideal (MvPolynomial σ k) := fun q => q.val.val
  let E : Qs → ProjectiveComponent k σ := fun q =>
    RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv q.val
  have hQmin : ∀ q : Qs, Q q ∈ (Ideal.span {x} ⊔ P.val).minimalPrimes := by
    intro q
    simpa only [sup_comm] using minimal_cut_of_intermediate_parent I P.val q.val.val x
      q.val.property.1 P.property.1.1.2 q.property
  have hQdegree : ∀ q : Qs, (actualHP (Q q) (E q).homogeneous).natDegree = s := by
    intro q
    have hdim := RetainedPrimeCycle.retainedChild_dimension C x havoid s hparent T P
      ⟨Q q, hQmin q, q.val.property.2⟩
    exact actualHP_natDegree_of_prime_dimension (Q q) (E q).homogeneous
      (E q).coordinate (E q).coordinate_not_mem s hdim
  have hinj : Function.Injective Q := by
    intro q r h
    exact Subtype.ext (Subtype.ext h)
  have hb := prime_cut_component_budget P.val (C.component P).homogeneous x hx
    (havoid P) hd s (hparent P) Q hinj (fun q => (E q).homogeneous) hQmin
    (fun q => (E q).coordinate) (fun q => (E q).coordinate_not_mem) hQdegree
  change (∑ q : Qs,
    (actualLocalLength (P.val ⊔ Ideal.span {x}) (Q q) : ℚ) *
      actualMultiplicity (Q q) (E q).homogeneous
        (actualHP (Q q) (E q).homogeneous).natDegree) ≤
    (d : ℚ) * actualMultiplicity P.val (C.component P).homogeneous
      (actualHP P.val (C.component P).homogeneous).natDegree
  simp only [hQdegree, hparent]
  simpa only [sup_comm] using hb

theorem actualMultiplicityCycle_cut_degree_le
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree ≤
      (d : ℚ) * (actualMultiplicityCycle I hI T v hv).degree := by
  rw [actualMultiplicityCycle_cut_expansion I hI x hx T v hv hdim hregular]
  calc
    _ ≤ ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ((d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree) := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_of_nonneg_left
        (actualMultiplicityCycle_parent_budget I hI x d hd hx T v hv havoid s hparent P)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [RetainedPrimeCycle.degree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      dsimp only [actualMultiplicityCycle]
      ring

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
