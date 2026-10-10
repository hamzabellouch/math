import Mathlib
import OAI.Computability.MaxCut.Games.KMSAnalyticHybridEnergyImageSplit
import OAI.Computability.MaxCut.Encoding.KMSKernelOrbitsFourier

namespace OAI

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallCoeff ι f = smallCoeff κ f :=
  smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- Independence is equality of the actual small-space functions. -/
theorem smallComponent_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallComponent ι f = smallComponent κ f :=
  smallComponent_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem surjective_postcomp_equiv (g : I ≃ₗ[F2] I) (T : F →ₗ[F2] I) :
    Function.Surjective (g.toLinearMap.comp T) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (g y)
    exact ⟨x, g.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (g.symm y)
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- The retained coefficient array is invariant under a small-space basis
change, with surjectivity and the lifted frequency kernel both preserved. -/
theorem smallCoeff_postcomp_equiv (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (g : I ≃ₗ[F2] I) (T : F →ₗ[F2] I) :
    smallCoeff ι f (g.toLinearMap.comp T) = smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_postcomp_equiv]
  split_ifs
  · apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
    rw [ker_comp_of_injective ι hι, ker_comp_of_injective g.toLinearMap g.injective,
      ker_comp_of_injective ι hι]
  · rfl

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The small component is genuinely invariant as a function on matrices. -/
theorem smallComponent_invariant (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (smallComponent ι f) := by
  intro g X
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Fintype.sum_equiv (KMSBasisInvariant.frequencyChange g)
  intro T
  change smallCoeff ι f T * (linearTraceCharacter T (X.comp g.toLinearMap)).re =
    smallCoeff ι f (g.toLinearMap.comp T) *
      (linearTraceCharacter (g.toLinearMap.comp T) X).re
  rw [smallCoeff_postcomp_equiv ι hι f hf, KMSBasisInvariant.character_change]

end
end MaxCutGames.Inverse.KMSAnalytic

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open KMSAnalyticHybridCoordinates KMSAnalytic

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The unnormalized fiber of extensions of one compressed frequency. -/
abbrev Extension (z : B →ₗ[R] W) :=
  {ψ : (B × C) →ₗ[R] W // ψ.comp (LinearMap.inl R B C) = z}

/-- The coordinate record has precisely three independent entries. -/
def coordinatesDataEquiv (z : B →ₗ[R] W) :
    Coordinates (A := A) (D := D) (C := C) z ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) where
  toFun p := (p.alpha, ⟨p.psi, p.psi_left⟩, p.v)
  invFun p := ⟨p.1, p.2.1.val, p.2.1.property, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨a, ⟨ψ, hψ⟩, v⟩; rfl

def compressedFiberDataEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) :=
  (compressedFiberEquiv z).trans (coordinatesDataEquiv z)

/-- Specifying the value on the complementary block gives every extension
exactly once. This will give the cardinality factor `|Hom(C,W)|`. -/
def extensionEquiv (z : B →ₗ[R] W) : Extension (C := C) z ≃ (C →ₗ[R] W) where
  toFun ψ := ψ.val.comp (LinearMap.inr R B C)
  invFun u := ⟨z.coprod u, by ext b; simp⟩
  left_inv ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : ψ.val (b, 0) = z b :=
      congrArg (fun t : B →ₗ[R] W => t b) ψ.property
    change z b + ψ.val (0, c) = ψ.val (b, c)
    rw [← hb, ← map_add]
    simp
  right_inv u := by ext c; simp

variable [Module F2 A] [Module F2 W] [Module F2 D] [Module F2 B] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]

omit [Fintype (A × W × C →ₗ[F2] B × C)] [Fintype (B × C →ₗ[F2] A × W × C)] in
/-- The actual hybrid and rank selectors reduce to the small component's
ordinary surjectivity selector. The only remaining geometric selector is
injectivity of the complementary block. -/
theorem hybrid_rank_coeff_assemble
    {z : B →ₗ[F2] W} (hz : Function.Surjective z)
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D)))
    (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) :
    (if LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) (assemble p)
     else 0) =
      if Function.Injective p.v then smallCoeff κ f (fullCoordinates p) else 0 := by
  have hh := hybrid_assemble_iff p hz
  change LinearIdentities.Hybrid (assemble p) _ _ ↔
    Function.Injective p.v ∧ Function.Surjective (fullCoordinates p) at hh
  rw [hh]
  by_cases hv : Function.Injective p.v
  · simp only [hv, true_and, ite_true]
    by_cases hp : Function.Surjective (fullCoordinates p)
    · rw [ite_eq_left hp]
      have hr := finrank_assemble p hv hp
      simp only [rankComponent, coeff_component, hr, ite_true]
      have he := congrFun (smallCoeff_eq_of_basisInvariant (embedLast p.v) κ
        (embedLast_injective p.v hv) hκ f hf) (fullCoordinates p)
      rw [smallCoeff, ite_eq_left hp, ← assemble_eq_embedLast_comp] at he
      exact he
    · simp [hp, smallCoeff]
  · simp [hv]

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergyPhase

noncomputable section
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

section Product

variable {H U V : Type*}
  [AddCommGroup H] [Module F2 H]
  [AddCommGroup U] [Module F2 U]
  [AddCommGroup V] [Module F2 V]

/-- Each frequency block pairs with the corresponding restriction of the
primal map. The trace is taken on the common codomain `H`. -/
theorem tracePair_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTracePair X (S.prod T) =
      linearTracePair (X.comp (LinearMap.inl F2 U V)) S +
      linearTracePair (X.comp (LinearMap.inr F2 U V)) T := by
  have hc : X.comp (S.prod T) =
      (X.comp (LinearMap.inl F2 U V)).comp S +
        (X.comp (LinearMap.inr F2 U V)).comp T := by
    apply LinearMap.ext
    intro h
    change X (S h, T h) = X (S h, 0) + X (0, T h)
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      X.map_add (S h, 0) (0, T h)
  simp only [linearTracePair, hc, map_add]

/-- Exact complex-valued phase splitting into two frequency blocks. -/
theorem character_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTraceCharacter (S.prod T) X =
      linearTraceCharacter S (X.comp (LinearMap.inl F2 U V)) *
      linearTraceCharacter T (X.comp (LinearMap.inr F2 U V)) := by
  simp only [linearTraceCharacter_apply, tracePair_prod, binarySign_add]

/-- The real phases multiply because every binary trace character is real. -/
theorem character_prod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) X).re =
      (linearTraceCharacter S (X.comp (LinearMap.inl F2 U V))).re *
      (linearTraceCharacter T (X.comp (LinearMap.inr F2 U V))).re := by
  rw [character_prod, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- Splitting a primal map and its dual frequency introduces no cardinal
factor: both traces remain on the common space `H`. -/
theorem character_prod_coprod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (a : U →ₗ[F2] H) (X : V →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) (a.coprod X)).re =
      (linearTraceCharacter S a).re * (linearTraceCharacter T X).re := by
  simpa only [LinearMap.coprod_inl, LinearMap.coprod_inr] using
    character_prod_re S T (a.coprod X)

end Product

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

/-- The three actual block phases of the assembled Hybrid frequency. -/
theorem character_assemble {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    linearTraceCharacter (assemble p) X =
      linearTraceCharacter p.alpha (X.comp (LinearMap.inl F2 A (W × D))) *
        (linearTraceCharacter p.psi
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)) *
        linearTraceCharacter (p.v.comp (LinearMap.snd F2 B C))
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D))) := by
  simp only [assemble, character_prod]

/-- The real phase factorization used in the coefficient fiber sum. -/
theorem character_assemble_re {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    (linearTraceCharacter (assemble p) X).re =
      (linearTraceCharacter p.alpha (X.comp (LinearMap.inl F2 A (W × D)))).re *
        ((linearTraceCharacter p.psi
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D))).re *
        (linearTraceCharacter (p.v.comp (LinearMap.snd F2 B C))
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D))).re) := by
  simp only [assemble, character_prod_re]

/-- The ambient character is exactly the small character after restricting
the primal map along the last-block embedding. -/
theorem character_assemble_eq_fullCoordinates {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    linearTraceCharacter (assemble p) X =
      linearTraceCharacter (fullCoordinates p) (X.comp (embedLast p.v)) := by
  simp only [assemble_eq_embedLast_comp, linearTraceCharacter_apply,
    linearTracePair, LinearMap.comp_assoc]

/-- Real-valued form of the exact small-character transport. -/
theorem character_assemble_eq_fullCoordinates_re {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    (linearTraceCharacter (assemble p) X).re =
      (linearTraceCharacter (fullCoordinates p) (X.comp (embedLast p.v))).re :=
  congrArg Complex.re (character_assemble_eq_fullCoordinates p X)

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergyPhase

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

/-- Append the primal value at the last coordinate. -/
def pointAppend (X : E →ₗ[F2] F) (a : F) : (E × F2) →ₗ[F2] F :=
  X.coprod (LinearMap.toSpanSingleton F2 F a)

@[simp] theorem pointAppend_apply (X : E →ₗ[F2] F) (a : F) (x : E) (c : F2) :
    pointAppend X a (x, c) = X x + c • a := rfl

/-- Fix one primal column, with no averaging or normalization. -/
def pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    (E →ₗ[F2] F) → ℝ := fun X => f (pointAppend X a)

/-- Extend an injection while retaining the newly fixed coordinate. -/
def pointLift (ι : J →ₗ[F2] E) : (J × F2) →ₗ[F2] (E × F2) :=
  ι.prodMap LinearMap.id

/-- The lower-dimensional embedding into the old coordinates. -/
def pointPad (ι : J →ₗ[F2] E) : J →ₗ[F2] (E × F2) :=
  ι.prod 0

theorem pointLift_injective (ι : J →ₗ[F2] E) (hι : Function.Injective ι) :
    Function.Injective (pointLift ι) := by
  rintro ⟨x, c⟩ ⟨y, d⟩ h
  have hxy : ι x = ι y := congrArg (fun z : E × F2 => z.1) h
  have hcd : c = d := congrArg (fun z : E × F2 => z.2) h
  exact Prod.ext (hι hxy) hcd

theorem pointPad_injective (ι : J →ₗ[F2] E) (hι : Function.Injective ι) :
    Function.Injective (pointPad ι) := by
  intro x y h
  exact hι (congrArg Prod.fst h)

theorem pointLift_comp_prod (ι : J →ₗ[F2] E) (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) :
    (pointLift ι).comp (T.prod ell) = (ι.comp T).prod ell := by
  ext x <;> rfl

theorem pointPad_comp (ι : J →ₗ[F2] E) (T : F →ₗ[F2] J) :
    (pointPad ι).comp T = (ι.comp T).prod 0 := rfl

/-- A non-surjective appended row vanishes on the kernel of a surjective
base frequency; the proof explicitly constructs a preimage otherwise. -/
theorem ker_le_of_not_surjective_prod (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2)
    (h : ¬ Function.Surjective (T.prod ell)) : T.ker ≤ ell.ker := by
  intro w hw
  change ell w = 0
  by_contra hn
  have hwT : T w = 0 := hw
  have hwell : ell w = 1 :=
    (MaxCutGames.Integration.BinaryLinear.scalar_cases (ell w)).resolve_left hn
  apply h
  rintro ⟨y, c⟩
  obtain ⟨x, hx⟩ := hT y
  refine ⟨x + (c - ell x) • w, ?_⟩
  apply Prod.ext
  · change T (x + (c - ell x) • w) = y
    simp [hx, hwT]
  · change ell (x + (c - ell x) • w) = c
    simp [hwell]

/-- Exact factorization, including uniqueness, of every dependent row. -/
theorem not_surjective_prod_iff (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2) :
    ¬ Function.Surjective (T.prod ell) ↔
      ∃! φ : J →ₗ[F2] F2, φ.comp T = ell := by
  constructor
  · intro h
    let φ := (T.ker.liftQ ell (ker_le_of_not_surjective_prod T hT ell h)).comp
      (T.quotKerEquivOfSurjective hT).symm.toLinearMap
    have hφ : φ.comp T = ell := by
      ext x
      simp [φ]
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ
    ext y
    obtain ⟨x, rfl⟩ := hT y
    exact (congrArg (fun L : F →ₗ[F2] F2 => L x) hψ).trans
      (congrArg (fun L : F →ₗ[F2] F2 => L x) hφ).symm
  · rintro ⟨φ, hφ, _⟩ hsurj
    obtain ⟨x, hx⟩ := hsurj (0, 1)
    have hTx : T x = 0 := congrArg Prod.fst hx
    have hellx : ell x = 1 := congrArg Prod.snd hx
    have he := congrArg (fun L : F →ₗ[F2] F2 => L x) hφ
    simp only [LinearMap.comp_apply, hTx, map_zero, hellx] at he
    exact zero_ne_one he

theorem surjective_of_surjective_prod (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) (h : Function.Surjective (T.prod ell)) :
    Function.Surjective T := by
  intro y
  obtain ⟨x, hx⟩ := h (y, 0)
  exact ⟨x, congrArg Prod.fst hx⟩

/-- Pullback along a surjection parametrizes the dependent rows exactly. -/
def dependentRowEquiv (T : F →ₗ[F2] J) (hT : Function.Surjective T) :
    (J →ₗ[F2] F2) ≃ {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)} where
  toFun φ := ⟨φ.comp T, (not_surjective_prod_iff T hT _).mpr
    ⟨φ, rfl, fun ψ hψ => by
      ext y
      obtain ⟨x, rfl⟩ := hT y
      exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩⟩
  invFun ell := Classical.choose ((not_surjective_prod_iff T hT ell.val).mp ell.property)
  left_inv φ := by
    exact (Classical.choose_spec ((not_surjective_prod_iff T hT (φ.comp T)).mp
      ((not_surjective_prod_iff T hT _).mpr
        ⟨φ, rfl, fun ψ hψ => by
          ext y
          obtain ⟨x, rfl⟩ := hT y
          exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩))).2 φ rfl |>.symm
  right_inv ell := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((not_surjective_prod_iff T hT ell.val).mp ell.property)).1

/-- Dependent extension preserves the base kernel. -/
theorem ker_prod_pullback (T : F →ₗ[F2] J) (φ : J →ₗ[F2] F2) :
    (T.prod (φ.comp T)).ker = T.ker := by
  ext x
  change (T x, φ (T x)) = (0, 0) ↔ T x = 0
  constructor
  · exact fun h => congrArg Prod.fst h
  · intro h
    simp [h]

end

/-!
Exact Fourier merging when one primal column is fixed. All frequency sums
are unnormalized; the primal Fourier coefficient uses normalized expectation.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Splitting the last frequency row is an exact bijection. -/
def frequencyProdEquiv : ((F →ₗ[F2] E) × (F →ₗ[F2] F2)) ≃
    (F →ₗ[F2] (E × F2)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 E F2).comp S,
    (LinearMap.snd F2 E F2).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_frequency_prod {A : Type*} [AddCommMonoid A]
    [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] F2)]
    [Fintype (F →ₗ[F2] (E × F2))]
    (g : (F →ₗ[F2] (E × F2)) → A) :
    ∑ S, g S = ∑ T : F →ₗ[F2] E, ∑ ell : F →ₗ[F2] F2, g (T.prod ell) := by
  rw [← frequencyProdEquiv.sum_comp g, Fintype.sum_prod_type]
  rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (pointAppend X a) (T.prod ell) =
      linearTracePair X T + ell a := by
  have hc : (pointAppend X a).comp (T.prod ell) =
      X.comp T + ell.smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight]

omit [FiniteDimensional F2 E] in
theorem character_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter (T.prod ell) (pointAppend X a)).re =
      (linearTraceCharacter T X).re * (binarySign (ell a)).re := by
  simp [linearTraceCharacter_apply, tracePair_pointAppend, binarySign_add,
    Complex.mul_re]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (X + φ.smulRight a) T = linearTracePair X T + φ (T a) := by
  have hc : (X + φ.smulRight a).comp T =
      X.comp T + (φ.comp T).smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight,
    LinearMap.comp_apply]

omit [FiniteDimensional F2 E] in
theorem character_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter T (X + φ.smulRight a)).re =
      (linearTraceCharacter T X).re * (binarySign (φ (T a))).re := by
  simp [linearTraceCharacter_apply, tracePair_pointShift, binarySign_add,
    Complex.mul_re]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (F →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] F)] in
/-- Fixing a primal column merges exactly its dual frequency row. -/
theorem pointRestrict_eq_synthesis (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    pointRestrict f a = synthesis (fun T : F →ₗ[F2] E =>
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re) := by
  funext X
  change f (pointAppend X a) = _
  rw [← linear_fourier_inversion f (pointAppend X a), sum_frequency_prod]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro ell _
  rw [character_pointAppend]
  ring

theorem coeff_pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F)
    (T : F →ₗ[F2] E) :
    linearCoeff (pointRestrict f a) T =
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re := by
  rw [pointRestrict_eq_synthesis, coeff_synthesis]

end

/-!
KMS Lemma 3.8 in coordinates with the newly fixed column last. The correction
sum runs over the dual of the smaller coordinate space. This is exactly one
representative of each graph subspace, so there is no basis-counting factor.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

theorem sum_dependentRows [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, if ¬ Function.Surjective (T.prod ell) then g ell else 0) =
      ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  calc
    _ = ∑ ell ∈ Finset.univ.filter (fun ell => ¬ Function.Surjective (T.prod ell)),
        g ell := (Finset.sum_filter _ _).symm
    _ = ∑ ell : {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)},
        g ell.val := Finset.sum_subtype _ (by simp) _
    _ = _ := ((dependentRowEquiv T hT).sum_comp (fun ell => g ell.val)).symm

theorem sum_rows_split [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (g : (F →ₗ[F2] F2) → ℝ) :
    (∑ ell, g ell) =
      (∑ ell, if Function.Surjective (T.prod ell) then g ell else 0) +
        ∑ φ : J →ₗ[F2] F2, g (φ.comp T) := by
  rw [← sum_dependentRows T hT g, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases h : Function.Surjective (T.prod ell) <;> simp [h]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 J]
  [Fintype ((E × F2) →ₗ[F2] F)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 J] in
/-- A dependent row changes the embedding, but not its frequency kernel. -/
theorem coeff_dependent_extension (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (φ : J →ₗ[F2] F2) :
    linearCoeff f ((ι.comp T).prod (φ.comp T)) =
      linearCoeff f ((pointPad ι).comp T) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  ext x
  change (ι (T x), φ (T x)) = (0, 0) ↔ (ι (T x), (0 : F2)) = (0, 0)
  constructor
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    exact Prod.ext hfst rfl
  · intro h
    have hfst := congrArg (fun z : E × F2 => z.1) h
    have hTx : T x = 0 := hι (by simpa using hfst)
    simp [hTx]

variable [Fintype (F →ₗ[F2] F2)] [Fintype (J →ₗ[F2] F2)]

omit [FiniteDimensional F2 J] in
/-- The precise rowwise identity before Fourier synthesis. -/
theorem point_row_recursion (ι : J →ₗ[F2] E) (hι : Function.Injective ι)
    (f : ((E × F2) →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : F →ₗ[F2] J) (hT : Function.Surjective T)
    (X : J →ₗ[F2] F) (a : F) :
    (∑ ell : F →ₗ[F2] F2,
      linearCoeff f ((ι.comp T).prod ell) * (binarySign (ell a)).re) *
        (linearTraceCharacter T X).re =
      (∑ ell : F →ₗ[F2] F2,
        (if Function.Surjective (T.prod ell)
          then linearCoeff f ((ι.comp T).prod ell) else 0) *
            (linearTraceCharacter (T.prod ell) (pointAppend X a)).re) +
      ∑ φ : J →ₗ[F2] F2, linearCoeff f ((pointPad ι).comp T) *
        (linearTraceCharacter T (X + φ.smulRight a)).re := by
  calc
    _ = ∑ ell : F →ₗ[F2] F2, linearCoeff f ((ι.comp T).prod ell) *
        (linearTraceCharacter (T.prod ell) (pointAppend X a)).re := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ell _
      rw [character_pointAppend]
      ring
    _ = _ := by
      rw [sum_rows_split T hT]
      congr 1
      · apply Finset.sum_congr rfl
        intro ell _
        split_ifs <;> simp
      · apply Finset.sum_congr rfl
        intro φ _
        rw [coeff_dependent_extension ι hι f hf, character_pointAppend,
          character_pointShift]
        rfl

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (J →ₗ[F2] F)] [Fintype (F →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] F)] [Fintype (J × F2 →ₗ[F2] F)] in
/-- One-column point restriction, with the dependent-row correction added
back. This identity applies in every dimension, including zero. -/
theorem point_restriction_recursion_add (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent ι (pointRestrict f a) X =
      smallComponent (pointLift ι) f (pointAppend X a) +
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  simp only [smallComponent, synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_frequency_prod (fun S : F →ₗ[F2] (J × F2) =>
    smallCoeff (pointLift ι) f S * (linearTraceCharacter S (pointAppend X a)).re)]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (J →ₗ[F2] F2)))
    (t := (Finset.univ : Finset (F →ₗ[F2] J))), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T
  · simp only [smallCoeff, hT, ite_true, coeff_pointRestrict, pointLift_comp_prod]
    exact point_row_recursion ι hι f hf T hT X a
  · have hprod : ∀ ell : F →ₗ[F2] F2, ¬ Function.Surjective (T.prod ell) :=
      fun ell h => hT (surjective_of_surjective_prod T ell h)
    simp [smallCoeff, hT, hprod]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] F)] [Fintype (J × F2 →ₗ[F2] F)] in
/-- KMS Lemma 3.8: the full-rank component after adjoining one coordinate
is the restricted component minus the sum of all dependent graph terms. -/
theorem point_restriction_recursion (ι : J →ₗ[F2] E)
    (hι : Function.Injective ι) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (X : J →ₗ[F2] F) (a : F) :
    smallComponent (pointLift ι) f (pointAppend X a) =
      smallComponent ι (pointRestrict f a) X -
        ∑ φ : J →ₗ[F2] F2, smallComponent (pointPad ι) f (X + φ.smulRight a) := by
  have h := point_restriction_recursion_add ι hι f hf X a
  linarith

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- An arbitrary actual Fourier slice; in the mixed estimate P fixes selected
frequency coordinates. -/
def sliceEnergy (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ T with P T, linearCoeff f T ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem sliceEnergy_nonneg (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ sliceEnergy P f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Translation acts on each actual coefficient by its trace-character sign. -/
theorem coeff_translate (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F)
    (T : F →ₗ[F2] E) :
    linearCoeff (fun X => f (X + Z)) T =
      linearCoeff f T * (linearTraceCharacter T Z).re := by
  have he : (fun X => f (X + Z)) =
      synthesis (fun S => linearCoeff f S * (linearTraceCharacter S Z).re) := by
    funext X
    rw [← linear_fourier_inversion f (X + Z)]
    simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro S _
    have hi (Y : E →ₗ[F2] F) : (linearTraceCharacter S Y).im = 0 := by
      simp
    rw [AddChar.map_add_eq_mul, Complex.mul_re, hi X, hi Z]
    ring
  rw [he, coeff_synthesis]

/-- No loss from translating a function before taking a fixed Fourier slice. -/
theorem sliceEnergy_translate (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Z : E →ₗ[F2] F) :
    sliceEnergy P (fun X => f (X + Z)) = sliceEnergy P f := by
  unfold sliceEnergy
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_translate, mul_pow]
  have hs : (linearTraceCharacter T Z).re ^ 2 = 1 := by
    simp only [linearTraceCharacter_apply, binarySign]
    split_ifs <;> norm_num
  rw [hs, mul_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
/-- A finite difference of functions costs only the number of summands in
its Fourier slice energy. No pointwise bound on those functions is used. -/
theorem sliceEnergy_sub_sum_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (g : J → (E →ₗ[F2] F) → ℝ) :
    sliceEnergy P (fun X => f X - ∑ j, g j X) ≤
      2 * (sliceEnergy P f + (Fintype.card J : ℝ) * ∑ j, sliceEnergy P (g j)) := by
  have hc (T : F →ₗ[F2] E) :
      linearCoeff (fun X => f X - ∑ j, g j X) T =
        linearCoeff f T - ∑ j, linearCoeff (g j) T := by
    simp only [linearCoeff, sub_mul, Finset.sum_mul, Finset.expect_sub_distrib,
      Finset.expect_sum_comm]
  have hp (T : F →ₗ[F2] E) :
      (linearCoeff f T - ∑ j, linearCoeff (g j) T) ^ 2 ≤
        2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
          ∑ j, linearCoeff (g j) T ^ 2) := by
    have hcs : (∑ j, linearCoeff (g j) T) ^ 2 ≤
        (Fintype.card J : ℝ) * ∑ j, linearCoeff (g j) T ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : J => (1 : ℝ)) (fun j => linearCoeff (g j) T)
    nlinarith [sq_nonneg (linearCoeff f T + ∑ j, linearCoeff (g j) T)]
  calc
    _ ≤ ∑ T with P T, 2 * (linearCoeff f T ^ 2 + (Fintype.card J : ℝ) *
        ∑ j, linearCoeff (g j) T ^ 2) := by
      apply Finset.sum_le_sum
      intro T _
      rw [hc]
      exact hp T
    _ = _ := by
      unfold sliceEnergy
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_comm (s := Finset.univ.filter P) (t := Finset.univ)]

/-- A sum of arbitrary translates has the same quadratic slice bound with
the square of the number of translates. -/
theorem sliceEnergy_sub_translates_le {J : Type*} [Fintype J]
    (P : (F →ₗ[F2] E) → Prop) (f g : (E →ₗ[F2] F) → ℝ)
    (Z : J → E →ₗ[F2] F) :
    sliceEnergy P (fun X => f X - ∑ j, g (X + Z j)) ≤
      2 * (sliceEnergy P f + (Fintype.card J : ℝ) ^ 2 * sliceEnergy P g) := by
  have h := sliceEnergy_sub_sum_le P f (fun j X => g (X + Z j))
  simp only [sliceEnergy_translate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  convert h using 1 ; ring

end
end MaxCutGames.Inverse.KMSFourthMoment

end OAI
