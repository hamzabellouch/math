import Mathlib
import OAI.Computability.DirectedFeedback.Games.KMSAnalyticHybridEnergyFiber

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

def partialRestrict (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    (I →ₗ[F2] F) → ℝ := fun X => f (a.coprod X)

@[simp] theorem partialRestrict_apply
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (X : I →ₗ[F2] F) : partialRestrict f a X = f (a.coprod X) := rfl

theorem coprod_add_shift (a : A →ₗ[F2] F) (X : I →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    a.coprod X + Z =
      (a + Z.comp (LinearMap.inl F2 A I)).coprod
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨u, v⟩
  change a u + X v + Z (u, v) =
    (a u + Z (u, 0)) + (X v + Z (0, v))
  have hZ : Z (u, v) = Z (u, 0) + Z (0, v) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using Z.map_add (u, 0) (0, v)
  rw [hZ]
  abel

theorem partialRestrict_translate
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    partialRestrict (fun Y => f (Y + Z)) a =
      fun X => partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))
        (X + Z.comp (LinearMap.inr F2 A I)) := by
  funext X
  change f (a.coprod X + Z) =
    f ((a + Z.comp (LinearMap.inl F2 A I)).coprod
      (X + Z.comp (LinearMap.inr F2 A I)))
  rw [coprod_add_shift]

theorem partialRestrict_sub_sum {J : Type*} [Fintype J]
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (fun Y => f Y - ∑ j, g j Y) a =
      fun X => partialRestrict f a X - ∑ j, partialRestrict (g j) a X := rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

theorem sliceEnergy_partialRestrict_translate
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (Z : (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f (Y + Z)) a) =
      sliceEnergy P (partialRestrict f (a + Z.comp (LinearMap.inl F2 A I))) := by
  rw [partialRestrict_translate, sliceEnergy_translate]

theorem sliceEnergy_partialRestrict_sub_translates_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] I) → Prop)
    (f : ((A × I) →ₗ[F2] F) → ℝ)
    (g : J → ((A × I) →ₗ[F2] F) → ℝ)
    (a : A →ₗ[F2] F) (Z : J → (A × I) →ₗ[F2] F) :
    sliceEnergy P (partialRestrict (fun Y => f Y - ∑ j, g j (Y + Z j)) a) ≤
      2 * (sliceEnergy P (partialRestrict f a) +
        (Fintype.card J : ℝ) * ∑ j, sliceEnergy P
          (partialRestrict (g j) (a + (Z j).comp (LinearMap.inl F2 A I)))) := by
  rw [partialRestrict_sub_sum]
  have h := sliceEnergy_sub_sum_le P (partialRestrict f a)
    (fun j => partialRestrict (fun Y => g j (Y + Z j)) a)
  simpa only [sliceEnergy_partialRestrict_translate] using h

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment
open DFVSGames.Inverse.KMSAnalyticHybridEnergyPhase

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

def frequencyBlockEquiv : ((F →ₗ[F2] A) × (F →ₗ[F2] I)) ≃
    (F →ₗ[F2] (A × I)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 A I).comp S,
    (LinearMap.snd F2 A I).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_frequency_blocks {M : Type*} [AddCommMonoid M]
    [Fintype (F →ₗ[F2] A)] [Fintype (F →ₗ[F2] I)]
    [Fintype (F →ₗ[F2] (A × I))]
    (g : (F →ₗ[F2] (A × I)) → M) :
    ∑ S, g S = ∑ T : F →ₗ[F2] I, ∑ alpha : F →ₗ[F2] A, g (alpha.prod T) := by
  rw [← frequencyBlockEquiv.sum_comp g, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 F]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (F →ₗ[F2] A)]

omit [Fintype (I →ₗ[F2] F)] in

theorem partialRestrict_eq_synthesis
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict h a = synthesis (fun T : F →ₗ[F2] I =>
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re) := by
  funext X
  change h (a.coprod X) = _
  rw [← linear_fourier_inversion h (a.coprod X), sum_frequency_blocks]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro alpha _
  rw [character_prod_coprod_re]
  ring

theorem coeff_partialRestrict
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (T : F →ₗ[F2] I) :
    linearCoeff (partialRestrict h a) T =
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re := by
  rw [partialRestrict_eq_synthesis, coeff_synthesis]

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSAnalyticHybridEnergyPhase
open KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

def coordinateOfData (z : B →ₗ[F2] W) (α : (B × C) →ₗ[F2] A)
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    Coordinates (A := A) (D := D) (C := C) z :=
  ⟨α, ψ.val, ψ.property, v⟩

def primalA (T : (A × (W × D)) →ₗ[F2] (B × C)) : A →ₗ[F2] (B × C) :=
  T.comp (LinearMap.inl F2 A (W × D))

def primalW (T : (A × (W × D)) →ₗ[F2] (B × C)) : W →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)

def primalD (T : (A × (W × D)) →ₗ[F2] (B × C)) : D →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D)

variable [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype (C →ₗ[F2] D)] [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]

theorem sum_compressedFiber (z : B →ₗ[F2] W)
    (g : ((B × C) →ₗ[F2] (A × (W × D))) → ℝ) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)}, g S.val) =
      ∑ α : (B × C) →ₗ[F2] A, ∑ ψ : Extension (C := C) z,
        ∑ v : C →ₗ[F2] D, g (assemble (coordinateOfData z α ψ v)) := by
  calc
    _ = ∑ p : ((B × C) →ₗ[F2] A) × Extension (C := C) z × (C →ₗ[F2] D),
        g (assemble (coordinateOfData z p.1 p.2.1 p.2.2)) := by
      apply Fintype.sum_equiv (compressedFiberDataEquiv (A := A) (D := D) z)
      intro S
      exact congrArg g (assemble_extract z S).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]

variable [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

omit [Fintype (B × C →ₗ[F2] W)] [Fintype (C →ₗ[F2] D)] in

theorem sum_alpha_hybrid_term (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C))
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    (∑ α : (B × C) →ₗ[F2] A,
      (if LinearIdentities.Hybrid (assemble (coordinateOfData z α ψ v))
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f)
          (assemble (coordinateOfData z α ψ v)) else 0) *
        (linearTraceCharacter (assemble (coordinateOfData z α ψ v)) T).re) =
      if Function.Injective v then
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re *
        ((linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) else 0 := by
  simp_rw [hybrid_rank_coeff_assemble hz _ κ hκ f hf, character_assemble_re]
  by_cases hv : Function.Injective v
  · simp only [coordinateOfData, hv, ite_true]
    rw [coeff_partialRestrict]
    simp only [coeff_smallComponent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    change smallCoeff κ f (α.prod (ψ.val.prod (LinearMap.snd F2 B C))) *
        ((linearTraceCharacter α (primalA T)).re *
          ((linearTraceCharacter ψ.val (primalW T)).re *
            (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re)) = _
    ring
  · simp [coordinateOfData, hv]

theorem hybrid_fiber_coefficient_factorization
    (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)},
      (if LinearIdentities.Hybrid S.val
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
        (linearTraceCharacter S.val T).re) =
      (∑ v ∈ Finset.univ.filter (fun v : C →ₗ[F2] D => Function.Injective v),
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re) *
      (∑ ψ : Extension (C := C) z,
        (linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) := by
  rw [sum_compressedFiber z (fun S =>
    (if LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S else 0) *
      (linearTraceCharacter S T).re), Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ((B × C) →ₗ[F2] A)))
    (t := (Finset.univ : Finset (C →ₗ[F2] D))),
    sum_alpha_hybrid_term z hz κ hκ f hf T]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical

theorem phase_weighted_sum_sq_le {Ψ : Type*} (s : Finset Ψ)
    (b H : Ψ → ℝ) (hb : ∀ ψ ∈ s, b ψ ^ 2 ≤ 1) :
    (∑ ψ ∈ s, b ψ * H ψ) ^ 2 ≤ (s.card : ℝ) * ∑ ψ ∈ s, H ψ ^ 2 := by
  have hphase : (∑ ψ ∈ s, b ψ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _ψ ∈ s, (1 : ℝ) := Finset.sum_le_sum hb
      _ = _ := by simp
  exact (Finset.sum_mul_sq_le_sq_mul_sq s b H).trans
    (mul_le_mul_of_nonneg_right hphase (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))

theorem phase_sum_sq_le_card_sq {V : Type*} [Fintype V]
    (a : V → ℝ) (ha : ∀ v, a v ^ 2 ≤ 1) :
    (∑ v, a v) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := phase_weighted_sum_sq_le Finset.univ a (fun _ => (1 : ℝ))
    (fun v _ => ha v)
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, pow_two] using h

theorem sum_fiber_phase_sq_le {Ψ Z : Type*} [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2) ≤
      (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have hlocal (z : Z) :
      (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 ≤
        (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 := by
    have hc : ((Finset.univ.filter (fun ψ => r ψ = z)).card : ℝ) ≤
        (maxFiber : ℝ) := Nat.cast_le.mpr (hcard z)
    exact (phase_weighted_sum_sq_le (Finset.univ.filter (fun ψ => r ψ = z))
      b H (fun ψ _ => hb ψ)).trans
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))
  calc
    _ ≤ ∑ z, (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
      rw [← Finset.mul_sum]
      exact congrArg (fun t : ℝ => (maxFiber : ℝ) * t)
        (Finset.sum_fiberwise Finset.univ r (fun ψ => H ψ ^ 2))

theorem sum_fiber_product_sq_le {V Ψ Z : Type*}
    [Fintype V] [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (a : V → ℝ) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (ha : ∀ v, a v ^ 2 ≤ 1) (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2) ≤
      (Fintype.card V : ℝ) ^ 2 * (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have haSum := phase_sum_sq_le_card_sq a ha
  have hmerged := sum_fiber_phase_sq_le r b H maxFiber hb hcard
  calc
    _ = (∑ v, a v) ^ 2 * ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ (Fintype.card V : ℝ) ^ 2 *
        ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 :=
      mul_le_mul_of_nonneg_right haSum (Finset.sum_nonneg (fun z _ => sq_nonneg _))
    _ ≤ (Fintype.card V : ℝ) ^ 2 * ((maxFiber : ℝ) * ∑ ψ, H ψ ^ 2) :=
      mul_le_mul_of_nonneg_left hmerged (sq_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix

theorem card_restriction_fiber_eq {R B C W : Type*} [Ring R]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup W] [Module R W]
    [Fintype ((B × C) →ₗ[R] W)] [Fintype (C →ₗ[R] W)]
    (z : B →ₗ[R] W) :
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)).card = Fintype.card (C →ₗ[R] W) := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (extensionEquiv (C := C) z)

section Extensions

variable {B C W : Type*}
  [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
  [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]

theorem natCard_extension (z : B →ₗ[F2] W) :
    Nat.card (Extension (C := C) z) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 W) := by
  rw [Nat.card_congr (extensionEquiv (C := C) z)]
  exact CompressionCount.natCard_linearMap

theorem card_restriction_fiber [Fintype ((B × C) →ₗ[F2] W)]
    (z : B →ₗ[F2] W) :
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[F2] W =>
      ψ.comp (LinearMap.inl F2 B C) = z)).card =
        2 ^ (Module.finrank F2 C * Module.finrank F2 W) := by
  rw [← Fintype.card_subtype]
  simpa only [Extension, Nat.card_eq_fintype_card] using natCard_extension (C := C) z

end Extensions

section Injections

variable {C D : Type*}
  [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
  [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]

theorem card_linearMap_eq [Fintype (C →ₗ[F2] D)] :
    Fintype.card (C →ₗ[F2] D) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using
    (CompressionCount.natCard_linearMap (U := C) (C := D))

theorem natCard_injective_le :
    Nat.card {v : C →ₗ[F2] D // Function.Injective v} ≤
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  let : Finite C := Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (C →ₗ[F2] D) := Finite.of_injective
    (fun v : C →ₗ[F2] D => (v : C → D)) DFunLike.coe_injective
  calc
    _ ≤ Nat.card (C →ₗ[F2] D) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := CompressionCount.natCard_linearMap

theorem card_injective_le [Fintype (C →ₗ[F2] D)] :
    Fintype.card {v : C →ₗ[F2] D // Function.Injective v} ≤
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using natCard_injective_le (C := C) (D := D)

end Injections

section Images

variable {U : Type*} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]

theorem natCard_rank_subspaces_le (q : ℕ) :
    Nat.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.mul_comm] using
    (SubspaceCounting.card_binary_subspaces_rank_le (V := U)
      (Module.finrank F2 U) q le_rfl)

theorem card_rank_subspaces_le [Fintype (Submodule F2 U)] (q : ℕ) :
    Fintype.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.card_eq_fintype_card] using natCard_rank_subspaces_le (U := U) q

end Images

theorem count_exponent_le (a b q d : ℕ) :
    q * (q + d) + (b * d) * 2 + b * q ≤ (2 * b + q) * (a + q + d) := by
  calc
    _ ≤ q * (q + d) + (b * d) * 2 + b * q + ((2 * b + q) * a + b * q) :=
      Nat.le_add_right _ _
    _ = _ := by ring

theorem count_budget_le (a b q d : ℕ) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (q + d)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤
      (2 : ℝ) ^ ((2 * b + q) * (a + q + d)) := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hvSq : countV ^ 2 ≤ ((2 : ℝ) ^ (b * d)) ^ 2 :=
    (sq_le_sq₀ hv0 (pow_nonneg htwo _)).mpr hv
  have hfirst : countW * countV ^ 2 ≤
      (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 :=
    mul_le_mul hw hvSq (sq_nonneg countV) (pow_nonneg htwo _)
  calc
    _ ≤ (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 *
        (2 : ℝ) ^ (b * q) :=
      mul_le_mul hfirst he he0 (mul_nonneg (pow_nonneg htwo _) (sq_nonneg _))
    _ = (2 : ℝ) ^ (q * (q + d) + (b * d) * 2 + b * q) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (count_exponent_le a b q d)

theorem count_budget_le_of_dimension (a b q d ell : ℕ)
    (hell : ell = a + q + d) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (ell - a)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤ (2 : ℝ) ^ ((2 * b + q) * ell) := by
  have hsub : ell - a = q + d := by omega
  rw [hsub] at hw
  rw [hell]
  exact count_budget_le a b q d countW countV extensionFactor hv0 he0 hw hv he

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSFourthMoment

section Slice

variable {F W C : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (W × C))]
  [Fintype (F →ₗ[F2] W)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in

theorem sliceEnergy_fixed_snd (ν : F →ₗ[F2] C)
    (g : ((W × C) →ₗ[F2] F) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = ν) g =
      ∑ ψ : F →ₗ[F2] W, linearCoeff g (ψ.prod ν) ^ 2 := by
  let : Finite (F →ₗ[F2] C) := Finite.of_injective
    (fun ν : F →ₗ[F2] C => (0 : F →ₗ[F2] W).prod ν) (by
      intro ν μ h
      simpa using congrArg
        (fun T : F →ₗ[F2] (W × C) => (LinearMap.snd F2 W C).comp T) h)
  let := Fintype.ofFinite (F →ₗ[F2] C)
  unfold sliceEnergy
  rw [Finset.sum_filter, sum_frequency_blocks, Finset.sum_comm]
  simp only [LinearMap.snd_prod]
  apply Finset.sum_congr rfl
  intro ψ _
  exact Fintype.sum_ite_eq' ν (fun x => linearCoeff g (ψ.prod x) ^ 2)

end Slice

section HybridSlice

variable {B W C : Type*}
  [AddCommGroup B] [Module F2 B]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]
  [Fintype ((B × C) →ₗ[F2] W)]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in

theorem sliceEnergy_snd_eq_sum (g : ((W × C) →ₗ[F2] (B × C)) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = LinearMap.snd F2 B C) g =
      ∑ ψ : (B × C) →ₗ[F2] W,
        linearCoeff g (ψ.prod (LinearMap.snd F2 B C)) ^ 2 :=
  sliceEnergy_fixed_snd (LinearMap.snd F2 B C) g

end HybridSlice

variable {R B W C M : Type*} [Ring R]
  [AddCommGroup B] [Module R B]
  [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]
  [AddCommMonoid M] [Fintype ((B × C) →ₗ[R] W)]

theorem sum_extensions_eq_filter (z : B →ₗ[R] W)
    [Fintype (Extension (C := C) z)] (H : ((B × C) →ₗ[R] W) → M) :
    (∑ ψ : Extension (C := C) z, H ψ.val) =
      ∑ ψ with ψ.comp (LinearMap.inl R B C) = z, H ψ := by
  exact (Finset.sum_subtype
    (p := fun ψ : (B × C) →ₗ[R] W => ψ.comp (LinearMap.inl R B C) = z)
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)) (by simp) H).symm

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] D)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

def adaptedFiberCoefficient (z : B →ₗ[F2] W)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  ∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[F2] D)},
    (if LinearIdentities.Hybrid S.val
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
      (linearTraceCharacter S.val T).re

omit [FiniteDimensional F2 W] [FiniteDimensional F2 B] [FiniteDimensional F2 C] [Fintype (B × C →ₗ[F2] W)] [Fintype (B × C →ₗ[F2] C)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)] [Fintype (W × C →ₗ[F2] B × C)] [Fintype (B × C →ₗ[F2] W × C)] in
theorem traceCharacter_re_sq (S : (B × C) →ₗ[F2] W) (X : W →ₗ[F2] (B × C)) :
    (linearTraceCharacter S X).re ^ 2 = 1 := by
  by_cases h : linearTracePair X S = 0 <;>
    simp [linearTraceCharacter_apply, binarySign, h]

omit [Fintype (B × C →ₗ[F2] C)] in

theorem adapted_image_energy_le_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) *
        sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
          (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
          (partialRestrict (smallComponent κ f) (primalA T)) := by
  let r : ((B × C) →ₗ[F2] W) → (B →ₗ[F2] W) :=
    fun ψ => ψ.comp (LinearMap.inl F2 B C)
  let a : (C →ₗ[F2] D) → ℝ := fun v => if Function.Injective v then
    (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re else 0
  let b : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    (linearTraceCharacter ψ (primalW T)).re
  let H : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
      (ψ.prod (LinearMap.snd F2 B C))
  have ha (v : C →ₗ[F2] D) : a v ^ 2 ≤ 1 := by
    dsimp [a]
    split_ifs
    · by_cases h : linearTracePair (primalD T) (v.comp (LinearMap.snd F2 B C)) = 0 <;>
        simp [binarySign, h]
    · norm_num
  have hb (ψ : (B × C) →ₗ[F2] W) : b ψ ^ 2 ≤ 1 := by
    exact le_of_eq (traceCharacter_re_sq ψ (primalW T))
  have hr (z : B →ₗ[F2] W) :
      (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ Fintype.card (C →ₗ[F2] W) := by
    exact le_of_eq (card_restriction_fiber_eq z)
  have hfactor (z : B →ₗ[F2] W) (hz : Function.Surjective z) :
      adaptedFiberCoefficient z f T =
        (∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ) := by
    rw [adaptedFiberCoefficient, hybrid_fiber_coefficient_factorization z hz κ hκ f hf T]
    have he : (∑ ψ : Extension (C := C) z, b ψ.val * H ψ.val) =
        ∑ ψ with r ψ = z, b ψ * H ψ := by
      exact sum_extensions_eq_filter z (fun ψ => b ψ * H ψ)
    change _ = (∑ v, a v) * _
    rw [← he]
    congr 1
    simp only [a, Finset.sum_filter]
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z),
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hfactor z (Finset.mem_filter.mp hz).2]
    _ ≤ ∑ z : B →ₗ[F2] W,
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun z _ _ => sq_nonneg _)
    _ ≤ (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 *
        (Fintype.card (C →ₗ[F2] W) : ℝ) * ∑ ψ, H ψ ^ 2 :=
      sum_fiber_product_sq_le r a b H (Fintype.card (C →ₗ[F2] W)) ha hb hr
    _ = _ := by
      rw [sliceEnergy_snd_eq_sum]

omit [Fintype (B × C →ₗ[F2] C)] in
theorem adapted_image_energy_le_of_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) (H : ℝ)
    (hH : sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
      (partialRestrict (smallComponent κ f) (primalA T)) ≤ H) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) * H := by
  apply (adapted_image_energy_le_mixed κ hκ f hf T).trans
  exact mul_le_mul_of_nonneg_left hH (by positivity)

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end OAI
