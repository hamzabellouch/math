import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticBlockFrequenciesLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedEnergyLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentZoomInAlgebraLemmas
import OAI.Computability.UniqueGames.Inverse.KMSKernelOrbitsFourierLemmas

namespace OAI

section

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

/-- The free block is the entire product when the fixed block is zero. -/
def zeroFixedEquiv : I ≃ₗ[F2] (A × I) :=
  { LinearMap.inr F2 A I with
    invFun := Prod.snd
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a, x⟩
      exact Prod.ext (Subsingleton.elim _ _) rfl }

@[simp] theorem zeroFixedEquiv_apply (x : I) :
    zeroFixedEquiv (A := A) x = (0, x) := rfl

@[simp] theorem zeroFixedEquiv_symm_apply (a : A) (x : I) :
    (zeroFixedEquiv (A := A) (I := I)).symm (a, x) = x := rfl

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (F →ₗ[F2] E)] [Fintype ((A × I) →ₗ[F2] F)] [Fintype (I →ₗ[F2] F)] in
/-- The actual partially restricted small function in zero fixed dimension. -/
theorem partialRestrict_smallComponent_zeroFixed (ι : (A × I) →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (smallComponent ι f) a =
      smallComponent (ι.comp (LinearMap.inr F2 A I)) f := by
  funext X
  have hmap : a.coprod X =
      X.comp (zeroFixedEquiv (A := A) (I := I)).symm.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨u, x⟩
    have hu : u = 0 := Subsingleton.elim _ _
    simp [hu]
  change smallComponent ι f (a.coprod X) = _
  rw [hmap]
  exact (smallComponent_precomp_equiv (zeroFixedEquiv (A := A) (I := I)) ι f X).symm

omit [FiniteDimensional F2 A] [FiniteDimensional F2 E]
  [Fintype (F →ₗ[F2] E)] [Fintype ((A × I) →ₗ[F2] F)] in
/-- Exact base normalization for the mixed estimate: the prescribed Fourier
slice is the fixed-frequency energy used by Lemma 3.19. -/
theorem mixedEnergy_zeroFixed (ι : (A × I) →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) =
      fixedFrequencyEnergy (ι.comp (LinearMap.inr F2 A I)) f π ν := by
  rw [partialRestrict_smallComponent_zeroFixed]
  simp only [sliceEnergy, fixedFrequencyEnergy, coeff_smallComponent]

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The actual mixed-energy induction step of KMS Lemma 3.20. Previously fixed
points form A, the remaining Fourier coordinates form I, and the new fixed
point is last. The dependent graphs translate the old fixed points, which
is why the inductive bound must hold uniformly over those prescribed values.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F A I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (((A × I) × F2) →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] ((A × I) × F2))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (F →ₗ[F2] F2)] [Fintype ((A × I) →ₗ[F2] F2)]

omit [FiniteDimensional F2 A] [Fintype ((A × I) →ₗ[F2] F)]
  [Fintype (((A × I) × F2) →ₗ[F2] F)] in
/-- The quantitative mixed recurrence, retaining every actual shifted center.
No density or Fourier estimate is assumed in this identity-based step. -/
theorem mixed_point_sliceEnergy_le (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : A →ₗ[F2] F) (b : F)
    (P : (F →ₗ[F2] I) → Prop) :
    sliceEnergy P (partialRestrict
      (pointRestrict (smallComponent (pointLift ι) f) b) a) ≤
      2 * (sliceEnergy P (partialRestrict (smallComponent ι (pointRestrict f b)) a) +
        (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) *
          ∑ φ : (A × I) →ₗ[F2] F2, sliceEnergy P
            (partialRestrict (smallComponent (pointPad ι) f)
              (a + (φ.smulRight b).comp (LinearMap.inl F2 A I)))) := by
  have he : pointRestrict (smallComponent (pointLift ι) f) b =
      fun X => smallComponent ι (pointRestrict f b) X -
        ∑ φ : (A × I) →ₗ[F2] F2,
          smallComponent (pointPad ι) f (X + φ.smulRight b) := by
    funext X
    exact point_restriction_recursion ι hι f hf X b
  rw [he]
  exact sliceEnergy_partialRestrict_sub_translates_le P
    (smallComponent ι (pointRestrict f b))
    (fun _ : (A × I) →ₗ[F2] F2 => smallComponent (pointPad ι) f)
    a (fun φ => φ.smulRight b)

omit [FiniteDimensional F2 A] [Fintype ((A × I) →ₗ[F2] F)]
  [Fintype (((A × I) × F2) →ₗ[F2] F)] in
/-- The induction uses one bound on the point-restricted original function,
and a bound on the lower component uniform in all previous fixed points. -/
theorem mixed_point_sliceEnergy_le_of_bounds (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : A →ₗ[F2] F) (b : F)
    (P : (F →ₗ[F2] I) → Prop) (H₀ H₁ : ℝ)
    (h₀ : sliceEnergy P
      (partialRestrict (smallComponent ι (pointRestrict f b)) a) ≤ H₀)
    (h₁ : ∀ a' : A →ₗ[F2] F,
      sliceEnergy P (partialRestrict (smallComponent (pointPad ι) f) a') ≤ H₁) :
    sliceEnergy P (partialRestrict
      (pointRestrict (smallComponent (pointLift ι) f) b) a) ≤
      2 * (H₀ + (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) ^ 2 * H₁) := by
  apply (mixed_point_sliceEnergy_le ι hι f hf a b P).trans
  have hs : (∑ φ : (A × I) →ₗ[F2] F2, sliceEnergy P
      (partialRestrict (smallComponent (pointPad ι) f)
        (a + (φ.smulRight b).comp (LinearMap.inl F2 A I)))) ≤
      (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) * H₁ := by
    calc
      _ ≤ ∑ _φ : (A × I) →ₗ[F2] F2, H₁ :=
        Finset.sum_le_sum (fun φ _ => h₁ _)
      _ = _ := by simp
  calc
    _ ≤ 2 * (H₀ + (Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) *
        ((Fintype.card ((A × I) →ₗ[F2] F2) : ℝ) * H₁)) := by
      gcongr
    _ = _ := by ring

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The quantitative one-point step of the KMS mixed-norm induction. This applies
the exact basis-invariant point recurrence to an arbitrary actual Fourier
slice. The only loss is the explicit number of dependent graph terms.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype ((I × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (I × F2))]
  [Fintype (F →ₗ[F2] F2)] [Fintype (I →ₗ[F2] F2)]

omit [Fintype ((I × F2) →ₗ[F2] F)] in
/-- Actual one-point mixed-energy recurrence; the remaining fixed-character
slice P is arbitrary, and all smaller components are the genuine functions. -/
theorem point_sliceEnergy_le (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : ((E × F2) →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (a : F) (P : (F →ₗ[F2] I) → Prop) :
    sliceEnergy P (pointRestrict (smallComponent (pointLift ι) f) a) ≤
      2 * (sliceEnergy P (smallComponent ι (pointRestrict f a)) +
        (Fintype.card (I →ₗ[F2] F2) : ℝ) ^ 2 *
          sliceEnergy P (smallComponent (pointPad ι) f)) := by
  have he : pointRestrict (smallComponent (pointLift ι) f) a =
      fun X => smallComponent ι (pointRestrict f a) X -
        ∑ φ : I →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
    funext X
    exact point_restriction_recursion ι hι f hf X a
  rw [he]
  exact sliceEnergy_sub_translates_le (E := I) (F := F)
    (J := I →ₗ[F2] F2) P (smallComponent ι (pointRestrict f a))
    (smallComponent (pointPad ι) f) (fun φ : I →ₗ[F2] F2 => φ.smulRight a)

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Put the last coordinate into the fixed block through `e`, keeping the
free block unchanged. -/
def pointShuffle (e : (A0 × F2) ≃ₗ[F2] A) :
    ((A0 × I) × F2) ≃ₗ[F2] (A × I) where
  toFun p := (e (p.1.1, p.2), p.1.2)
  invFun p := (((e.symm p.1).1, p.2), (e.symm p.1).2)
  left_inv p := by
    rcases p with ⟨⟨u, v⟩, c⟩
    simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change e (p.1.1 + q.1.1, p.2 + q.2) =
        e (p.1.1, p.2) + e (q.1.1, q.2)
      exact map_add e (p.1.1, p.2) (q.1.1, q.2)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · change e (c • p.1.1, c • p.2) = c • e (p.1.1, p.2)
      exact map_smul e c (p.1.1, p.2)
    · rfl

@[simp] theorem pointShuffle_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A0) (v : I) (c : F2) :
    pointShuffle (I := I) e ((u, v), c) = (e (u, c), v) := rfl

@[simp] theorem pointShuffle_symm_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A) (v : I) :
    (pointShuffle (I := I) e).symm (u, v) =
      (((e.symm u).1, v), (e.symm u).2) := rfl

/-- Actual matrix identity placing one fixed column last. -/
theorem coprod_comp_pointShuffle (e : (A0 × F2) ≃ₗ[F2] A)
    (a : A →ₗ[F2] F) (X : I →ₗ[F2] F) :
    (a.coprod X).comp (pointShuffle e).toLinearMap =
      pointAppend (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
        (a (e (0, 1))) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨⟨u, v⟩, c⟩
  change a (e (u, c)) + X v =
    (a (e (u, 0)) + X v) + c • a (e (0, 1))
  have hp : (u, c) = (u, (0 : F2)) + c • ((0 : A0), (1 : F2)) := by
    simp
  have ha : a (e (u, c)) = a (e (u, 0)) + c • a (e (0, 1)) := by
    rw [hp]
    simp only [map_add, map_smul]
  rw [ha]
  abel

/-- Express a function in the shuffled coordinates. -/
def pointShuffleTransport (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) :
    (((A0 × I) × F2) →ₗ[F2] F) → ℝ :=
  fun Y => f (Y.comp (pointShuffle e).symm.toLinearMap)

/-- Fixing the last column and then the remaining fixed block in shuffled
coordinates is the original partial restriction, with the same free map. -/
theorem partialRestrict_pointRestrict_pointShuffleTransport
    (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict
      (pointRestrict (pointShuffleTransport e f) (a (e (0, 1))))
      ((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)) =
        partialRestrict f a := by
  funext X
  change f ((pointAppend
    (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
    (a (e (0, 1)))).comp (pointShuffle e).symm.toLinearMap) = f (a.coprod X)
  rw [← coprod_comp_pointShuffle]
  congr 1
  apply LinearMap.ext
  intro p
  change (a.coprod X) ((pointShuffle e) ((pointShuffle e).symm p)) = (a.coprod X) p
  rw [LinearEquiv.apply_symm_apply]

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The exact basis-invariant KMS zoom-out recursion. The restricted coefficient
is an actual Fourier coefficient of the homogeneous codomain restriction.
The full extension fiber is split into dependent vectors and one common
coefficient on all independent vectors; neither term is replaced by an
assumed estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
/-- Exact codomain-restriction coefficient, reindexed by the extension vector.
The sum has no cardinality normalization. -/
theorem coefficient_hyperplane_restriction
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (z : B →ₗ[F2] E) :
    linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z =
      ∑ u : E, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_codomain_pullback_fiber]
  exact ((hyperplaneExtensionEquiv z).sum_comp
    (fun S => linearCoeff f S.val)).symm

omit [Fintype (B →ₗ[F2] E)] in
/-- KMS's genuine zoom-out recurrence, in product coordinates. The denominator
is the exact number of independent extension vectors. Basis invariance is
used to prove their Fourier coefficients coincide. -/
theorem coefficient_zoomOut_recursion
    (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z v) =
      (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) /
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) := by
  rw [coefficient_hyperplane_restriction]
  exact coefficient_hyperplaneExtend_recursion f hf z hv

omit [Fintype (B →ₗ[F2] E)] in
/-- A denominator-free form convenient for squared-norm estimates. -/
theorem coefficient_zoomOut_mul
    (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) =
      linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_hyperplane_restriction, sum_hyperplaneExtend f hf z hv]
  ring

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-! The actual squared-coefficient inequality from the KMS zoom-out recursion.
Only a finite Cauchy--Schwarz inequality is applied to the exact restriction
identity. No restricted Fourier bound is taken as a premise. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant
open UniqueGamesTheorem.Inverse.KMSFourthMoment

/-- Cauchy--Schwarz with the distinguished scalar included as one extra
summand. This form also handles an empty dependent branch. -/
theorem sub_sum_sq_le_card_mul {C : Type*} [Fintype C]
    (x : ℝ) (a : C → ℝ) :
    (x - ∑ c, a c) ^ 2 ≤
      ((Fintype.card C : ℝ) + 1) * (x ^ 2 + ∑ c, a c ^ 2) := by
  let b : Option C → ℝ := fun c => c.elim x (fun c => -a c)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option C))
    (fun _ => (1 : ℝ)) b
  simpa [b, Fintype.sum_option, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
/-- An actual independent extension coefficient is controlled by its
homogeneous restriction coefficient and every dependent extension. -/
theorem coefficient_zoomOut_sq_bound
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] E) {v : E} (hv : v ∉ z.range) :
    (((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend z v) ^ 2 ≤
      ((Fintype.card z.range : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z ^ 2 +
          ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val) ^ 2) := by
  have hrec := coefficient_zoomOut_mul f hf z hv
  rw [Finset.sum_subtype (p := fun u : E => u ∈ z.range) _ (by simp)
    (fun u : E => linearCoeff f (hyperplaneExtend z u))] at hrec
  calc
    _ = ((((Fintype.card E - Fintype.card z.range : ℕ) : ℝ)) *
        linearCoeff f (hyperplaneExtend z v)) ^ 2 := (mul_pow _ _ _).symm
    _ = (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z -
        ∑ u : z.range, linearCoeff f (hyperplaneExtend z u.val)) ^ 2 := by rw [hrec]
    _ ≤ _ := sub_sum_sq_le_card_mul _ _

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! A denominator-cleared fixed-character induction step. Its right side
contains only the actual smaller restricted Fourier energies, obtained from
the exact zoom-out identity and injective reindexing of each dependent branch.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] J)] [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype (B →ₗ[F2] E)] in
/-- The exact zoom-out square bound after embedding the small frequency
space; the dependent sum is indexed by that small space itself. -/
theorem coefficient_lifted_zoomOut_sq_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 ≤
      ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
  have hv : ι (0, 1) ∉ ((leftEmbedding ι).comp z).range := by
    rw [range_left_comp_of_surjective ι z hz]
    exact lastVector_not_mem_left_range ι hι
  have h := coefficient_zoomOut_sq_bound f hf ((leftEmbedding ι).comp z) hv
  rw [card_lifted_range ι hι z hz,
    sum_lifted_range ι hι z hz
      (fun u => linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) u) ^ 2)] at h
  simpa only [hyperplaneExtend_left_comp] using h

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] (B × F2))]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)] in
/-- Summing the genuine pointwise recurrence bounds every dependent branch
by an actual lower-rank fixed-character energy, with no missing multiplicity. -/
theorem fixedCharacter_step_sum
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] J =>
            π.comp z = A ∧ Function.Surjective z),
          linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) ≤
      ((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  change _ * (∑ z ∈ P, _) ≤ _
  calc
    _ ≤ ∑ z ∈ P, ((Fintype.card J : ℝ) + 1) *
        (linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X))
            ((leftEmbedding ι).comp z) ^ 2 +
          ∑ w : J, linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      exact coefficient_lifted_zoomOut_sq_bound ι hι f hf z
        (Finset.mem_filter.mp hz).2.2
    _ = ((Fintype.card J : ℝ) + 1) *
        ((∑ z ∈ P, linearCoeff
          (fun X => f ((LinearMap.inl F2 B F2).comp X)) ((leftEmbedding ι).comp z) ^ 2) +
        ∑ w : J, ∑ z ∈ P,
          linearCoeff f ((leftEmbedding ι).comp (hyperplaneExtend z w)) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · rw [fixedFrequencyEnergy_eq]
      · apply Finset.sum_le_sum
        intro w _
        exact dependent_extension_energy_le (leftEmbedding ι) f π A w

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! The complete product-coordinate fixed-character recurrence, with the
actual new-coordinate multiplicity. This joins the block-frequency bijection
to the genuine Fourier zoom-out energy inequality. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

theorem comp_blockFrequency_zero (ι : (J × F2) →ₗ[F2] E) (z : B →ₗ[F2] J) :
    ι.comp (blockFrequency z 0) =
      hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1)) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  change ι (z b + c • 0, c) = ι (z b, 0) + c • ι (0, 1)
  simp only [smul_zero, add_zero]
  rw [← map_smul, ← map_add]
  congr 1
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [FiniteDimensional F2 J]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)] in
/-- A genuine one-step recurrence in the actual restricted Fourier energy.
Every term on the right has one fewer small-space dimension and one fewer
fixed character. -/
theorem fixedFrequencyEnergy_product_step
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    (((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
        fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (Fintype.card π.ker : ℝ) * (((Fintype.card J : ℝ) + 1) *
        (fixedFrequencyEnergy (leftEmbedding ι)
          (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A +
        ∑ w : J, fixedFrequencyEnergy (leftEmbedding ι) f π (hyperplaneExtend A (π w)))) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A ∧ Function.Surjective z
  have hsum : (∑ z : CompatibleOldFrequency π A,
      linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2) =
      ∑ z ∈ P,
        linearCoeff f (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2 := by
    rw [← Finset.sum_subtype (p := fun z : B →ₗ[F2] J =>
      Function.Surjective z ∧ π.comp z = A) P (by intro z; simp [P, and_comm])
      (fun z => linearCoeff f (ι.comp (blockFrequency z 0)) ^ 2)]
    apply Finset.sum_congr rfl
    intro z _
    rw [comp_blockFrequency_zero]
  rw [fixedFrequencyEnergy_block ι hι f hf π A, hsum]
  calc
    _ = (Fintype.card π.ker : ℝ) *
        ((((Fintype.card E - Fintype.card J : ℕ) : ℝ) ^ 2) *
          ∑ z ∈ P, linearCoeff f
            (hyperplaneExtend ((leftEmbedding ι).comp z) (ι (0, 1))) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fixedCharacter_step_sum ι hι f hf π A)
      (Nat.cast_nonneg _)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Quantitative closure of the genuine fixed-character product recurrence.
The hypotheses are the actual two smaller restricted energies. The proof
accounts for the kernel multiplicity and all dependent extensions explicitly.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [FiniteDimensional F2 J] [FiniteDimensional F2 K]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] (B × F2))]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)] in
/-- The fixed-character recurrence preserves the explicit quadratic constant.
No local-density or Fourier bound is hidden in the scalar accounting. -/
theorem fixedFrequencyEnergy_product_bound
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (hf : IsBasisInvariant f)
    (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) (ε : ℝ) (hε : 0 ≤ ε)
    (hfirst : (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι)
        (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε)
    (hlower : ∀ w : J, (2 : ℝ) ^ ((Module.finrank F2 J + Module.finrank F2 K) *
        Module.finrank F2 E) * fixedFrequencyEnergy (leftEmbedding ι) f π
        (hyperplaneExtend A (π w)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 J * Module.finrank F2 J) * ε) :
    (2 : ℝ) ^ ((Module.finrank F2 (J × F2) + Module.finrank F2 (K × F2)) *
        Module.finrank F2 E) * fixedFrequencyEnergy ι f
        (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
        (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 (J × F2) * Module.finrank F2 (J × F2)) * ε := by
  let n := Module.finrank F2 J
  let m := Module.finrank F2 K
  let ell := Module.finrank F2 E
  let P : ℝ := 2 ^ ((n + m) * ell)
  let C : ℝ := 2 ^ (4 * n * n)
  let N : ℝ := 2 ^ n
  let D : ℝ := 2 ^ ell - 2 ^ n
  let a := fixedFrequencyEnergy (leftEmbedding ι)
    (fun X : E →ₗ[F2] B => f ((LinearMap.inl F2 B F2).comp X)) π A
  let b := fun w : J => fixedFrequencyEnergy (leftEmbedding ι) f π
    (hyperplaneExtend A (π w))
  let t := fixedFrequencyEnergy ι f
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
    (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
  have hnell : n < ell := by
    have hdim := LinearMap.finrank_le_finrank_of_injective hι
    rw [Module.finrank_prod, Module.finrank_self] at hdim
    exact hdim
  have hcardE : Fintype.card E = 2 ^ ell := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, ell]
  have hcardJ : Fintype.card J = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := F2)]
    simp only [F2, ZMod.card, n]
  have hcardle : Fintype.card J ≤ Fintype.card E := by
    rw [hcardJ, hcardE]
    exact Nat.pow_le_pow_right (by decide) hnell.le
  have hcardJR : (Fintype.card J : ℝ) = N := by
    rw [hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, N]
  have hdiff : ((Fintype.card E - Fintype.card J : ℕ) : ℝ) = D := by
    rw [Nat.cast_sub hcardle, hcardE, hcardJ]
    simp only [Nat.cast_pow, Nat.cast_ofNat, D]
  have hker : (Fintype.card π.ker : ℝ) ≤ N := by
    rw [← hcardJR]
    exact_mod_cast Fintype.card_le_of_injective (fun x : π.ker => (x : J))
      Subtype.val_injective
  have hP : 0 < P := by dsimp [P]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hnell)
  have ha : 0 ≤ a := fixedFrequencyEnergy_nonneg _ _ _ _
  have hb : 0 ≤ ∑ w : J, b w :=
    Finset.sum_nonneg (fun w _ => fixedFrequencyEnergy_nonneg _ _ _ _)
  have hsum : P * (a + ∑ w : J, b w) ≤ (N + 1) * (C * ε) := by
    calc
      _ = P * a + ∑ w : J, P * b w := by rw [mul_add, Finset.mul_sum]
      _ ≤ C * ε + ∑ _w : J, C * ε :=
        add_le_add hfirst (Finset.sum_le_sum (fun w _ => hlower w))
      _ = (N + 1) * (C * ε) := by simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcardJR]; ring
  have hrec : D ^ 2 * t ≤ (Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w)) := by
    simpa only [hdiff, hcardJR] using fixedFrequencyEnergy_product_step ι hι f hf π A
  have hweighted : (D ^ 2 * P) * t ≤ N * (N + 1) ^ 2 * C * ε := by
    calc
      _ = P * (D ^ 2 * t) := by ring
      _ ≤ P * ((Fintype.card π.ker : ℝ) * ((N + 1) * (a + ∑ w : J, b w))) :=
        mul_le_mul_of_nonneg_left hrec hP.le
      _ ≤ P * (N * ((N + 1) * (a + ∑ w : J, b w))) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact mul_le_mul_of_nonneg_right hker (mul_nonneg (by positivity) (add_nonneg ha hb))
      _ = (N * (N + 1)) * (P * (a + ∑ w : J, b w)) := by ring
      _ ≤ (N * (N + 1)) * ((N + 1) * (C * ε)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have ht : t ≤ (N * (N + 1) ^ 2 * C / (D ^ 2 * P)) * ε := by
    calc
      t ≤ (N * (N + 1) ^ 2 * C * ε) / (D ^ 2 * P) :=
        (le_div_iff₀ (show 0 < D ^ 2 * P by positivity)).mpr
          (by simpa only [mul_comm] using hweighted)
      _ = _ := by ring
  have hc := fixedCharacter_constant_step n m ell hnell
  change N * (N + 1) ^ 2 * C / (D ^ 2 * P) ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
      (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) at hc
  have hfinal := ht.trans (mul_le_mul_of_nonneg_right hc hε)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  change (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) * t ≤
    (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε
  have hresult := (le_div_iff₀
    (show 0 < (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) by positivity)).mp
      (show t ≤ ((2 : ℝ) ^ (4 * (n + 1) * (n + 1)) * ε) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) from hfinal.trans_eq (by ring))
  simpa only [mul_comm] using hresult

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
