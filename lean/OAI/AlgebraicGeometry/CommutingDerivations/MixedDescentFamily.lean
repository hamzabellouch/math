import OAI.AlgebraicGeometry.CommutingDerivations.DescentFamily
import OAI.AlgebraicGeometry.CommutingDerivations.LocalizedPartials

namespace OAI

/-! Each coordinate direction may use its own power of the fixed parameter.
In particular, additional ordinary coordinate partials use exponent zero. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K A B L I : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing L]
  [Algebra K A] [Algebra K B] [Algebra K L]

theorem mixed_descended_commute (ι : A →ₐ[K] L) (hinj : Function.Injective ι)
    (c : A) (N M : ℕ) (D E : Derivation K L L) (d e : Derivation K A A)
    (hd : ∀ a, ι (d a) = (ι c)^N * D (ι a))
    (he : ∀ a, ι (e a) = (ι c)^M * E (ι a))
    (hD : D (ι c) = 0) (hE : E (ι c) = 0)
    (hDE : ∀ a, D (E a) = E (D a)) (a : A) : d (e a) = e (d a) := by
  have hDp : D ((ι c)^M) = 0 := by simp [Derivation.leibniz_pow, hD]
  have hEp : E ((ι c)^N) = 0 := by simp [Derivation.leibniz_pow, hE]
  exact descendDerivation_commute ι hinj ((ι c)^N • D) ((ι c)^M • E) d e
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using hd)
    (by simpa only [Derivation.smul_apply, smul_eq_mul] using he)
    (scaleDerivation_commute D E ((ι c)^N) ((ι c)^M) hDp hEp hDE) a

theorem mixed_descended_linearIndependent [Fintype I] [DecidableEq I]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A)
    (hu : IsUnit (ι c)) (N : I → ℕ)
    (D : I → Derivation K L L) (d : I → Derivation K A A)
    (hdesc : ∀ i a, ι (d i a) = (ι c)^(N i) * D i (ι a))
    (hfix : ∀ i, D i (ι c) = 0)
    (t : I → L) (ht : ∀ i j, D i (t j) = if i = j then 1 else 0)
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), t j * (ι c)^n = ι r) :
    LinearIndependent A d := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  obtain ⟨n, r, hr⟩ := hfrac j
  have hir (i : I) : D i (ι r) = (ι c)^n * (if i = j then 1 else 0) := by
    rw [← hr, Derivation.leibniz]
    simp [Derivation.leibniz_pow, hfix, ht, smul_eq_mul]
  let ev : Derivation K A A →+ A :=
    { toFun := fun E => E r
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : ∑ i, a i * d i r = 0 := by
    have he' := congrArg ev ha
    rw [map_sum, map_zero] at he'
    simpa [ev, Derivation.smul_apply, smul_eq_mul] using he'
  have hj : (ι (a j) * (ι c)^(N j)) * (ι c)^n = 0 := by
    simpa [map_sum, hdesc, hir, mul_ite, ite_mul, mul_assoc] using congrArg ι he
  apply hinj
  rw [map_zero]
  exact (hu.pow (N j)).mul_left_eq_zero.mp ((hu.pow n).mul_left_eq_zero.mp hj)

theorem family_properties_of_mixed_descent [Fintype I] [IsDomain B] [CharZero B]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A) (hu : IsUnit (ι c))
    (e : L ≃ₐ[K] MvPolynomial I B) (b : B) (hc : e (ι c) = C b)
    (N : I → ℕ) (d : I → Derivation K A A)
    (hd : ∀ i a, ι (d i a) = (ι c)^(N i) * localizedPartial e i (ι a))
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), e.symm (X j) * (ι c)^n = ι r)
    (S : Subalgebra K A)
    (hintersection : ∀ a, (∃ b : B, e (ι a) = C b) ↔ a ∈ S) :
    (∀ i, d i c = 0) ∧
      (∀ i j a, d i (d j a) = d j (d i a)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧ LinearIndependent A d ∧
      (∀ a, (∀ i, d i a = 0) ↔ a ∈ S) := by
  classical
  have hfix (i : I) : localizedPartial e i (ι c) = 0 :=
    localizedPartial_fixes_relative e i (ι c) b hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact descended_fixes_parameter ι hinj c (N i) _ _ (hd i) (hfix i)
  · intro i j a
    exact mixed_descended_commute ι hinj c (N i) (N j) _ _ _ _
      (hd i) (hd j) (hfix i) (hfix j) (localizedPartials_commute e i j) a
  · intro i
    exact descended_locallyNilpotent ι hinj c (N i) _ _ (hd i) (hfix i)
      (localizedPartial_locallyNilpotent e i)
  · exact mixed_descended_linearIndependent ι hinj c hu N _ d hd hfix
      (fun j => e.symm (X j)) (localizedPartial_coordinate e) hfrac
  · intro a
    calc
      (∀ i, d i a = 0) ↔ ∀ i, localizedPartial e i (ι a) = 0 :=
        forall_congr' (fun i => descended_kernel ι hinj c hu (N i) _ _ (hd i) a)
      _ ↔ ∃ b : B, e (ι a) = C b := localizedPartials_common_kernel e (ι a)
      _ ↔ a ∈ S := hintersection a

end AbhyankarSathaye.CommutingDerivations

end

end OAI
