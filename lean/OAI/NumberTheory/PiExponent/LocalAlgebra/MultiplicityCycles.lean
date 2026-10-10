import OAI.NumberTheory.PiExponent.LocalAlgebra.EquidimensionalRetainedCut
import OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation

namespace OAI

namespace PiExponentJets.W22

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
    exact ite_eq_right (fun heq => hQP (RetainedMinimalPrime.toComponent_injective hI v hv heq))
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
      let : Q.val.IsPrime := Q.property.1.1.1
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

end PiExponentJets.W22

end OAI
