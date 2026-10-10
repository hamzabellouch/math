import Mathlib
import OAI.Computability.MaxCut.Games.KMSAnalyticHybridEnergyImageTransportCore

namespace OAI

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

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
end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- Squared small Fourier coefficients whose image under a prescribed linear
projection is the fixed partial frequency. -/
def fixedFrequencyEnergy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) : ℝ :=
  ∑ T with π.comp T = A, smallCoeff ι f T ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_nonneg (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    0 ≤ fixedFrequencyEnergy ι f π A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The definition retains precisely the surjective compatible frequencies. -/
theorem fixedFrequencyEnergy_eq (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => π.comp T = A ∧ Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> by_cases hA : π.comp T = A <;>
    simp [smallCoeff, hT, hA]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- An impossible partial frequency contributes no energy. -/
theorem fixedFrequencyEnergy_eq_zero_of_not_surjective
    (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (A : F →ₗ[F2] J) (hA : ¬ Function.Surjective A) :
    fixedFrequencyEnergy ι f π A = 0 := by
  rw [fixedFrequencyEnergy_eq]
  apply Finset.sum_eq_zero
  intro T hT
  have ht := (Finset.mem_filter.mp hT).2
  exact (hA (ht.1 ▸ hπ.comp ht.2)).elim

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Forgetting the prescribed partial frequency gives the exact full small
energy, so every individual restricted sum is bounded by it. -/
theorem fixedFrequencyEnergy_le (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A ≤ 𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- With no fixed characters the restricted sum is exactly the small squared
norm; there is no ambient-cardinality normalization in the frequency sum. -/
theorem fixedFrequencyEnergy_zero (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    fixedFrequencyEnergy ι f (0 : I →ₗ[F2] J) 0 =
      𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  simp [fixedFrequencyEnergy]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The fixed-character energy is independent of the chosen small-space
embedding for the actual basis-invariant function. -/
theorem fixedFrequencyEnergy_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A = fixedFrequencyEnergy κ f π A := by
  unfold fixedFrequencyEnergy
  rw [smallCoeff_eq_of_basisInvariant ι κ hι hκ f hf]

end

/-!
# Transport of the small component between equivalent coordinate spaces

The embedding and partial projection are transported together. Thus the
lifted frequency and its prescribed partial value remain literally the same.
Finite reindexing proves exact coefficient, function, and restricted-energy
identities without requiring basis invariance of the original function.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

/-- Reindex the actual dual frequency maps by an equivalence of their targets. -/
def smallFrequencyEquiv (e : I ≃ₗ[F2] I') : (F →ₗ[F2] I) ≃ (F →ₗ[F2] I') where
  toFun T := e.toLinearMap.comp T
  invFun T := e.symm.toLinearMap.comp T
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem smallFrequencyEquiv_apply (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    smallFrequencyEquiv e T = e.toLinearMap.comp T := rfl

theorem surjective_smallFrequencyEquiv_iff (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    Function.Surjective (e.toLinearMap.comp T) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    exact ⟨x, e.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨x, ?_⟩
    change e (T x) = y
    rw [hx, e.apply_symm_apply]

/-- Transporting the outer map in the opposite direction cancels the
frequency-coordinate change. -/
theorem smallFrequency_transport_comp (e : I ≃ₗ[F2] I') (π : I →ₗ[F2] J)
    (T : F →ₗ[F2] I) :
    (π.comp e.symm.toLinearMap).comp (e.toLinearMap.comp T) = π.comp T := by
  ext x
  simp

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 I'] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I' →ₗ[F2] F)] [Fintype (F →ₗ[F2] I')] in
/-- Exact coefficient transport; the embedding need not be injective and
the original function need not be basis invariant. -/
theorem smallCoeff_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (ι.comp e.symm.toLinearMap) f (e.toLinearMap.comp T) =
      smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_smallFrequencyEquiv_iff, smallFrequency_transport_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 I'] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in
/-- Prescribed partial-frequency energy is unchanged when its projection
and embedding are both transported to the new small space. -/
theorem fixedFrequencyEnergy_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy (ι.comp e.symm.toLinearMap) f
      (π.comp e.symm.toLinearMap) A = fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallFrequency_transport_comp,
    smallCoeff_transport]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 I']
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)]

/-- The actual small-space functions agree under the corresponding primal
coordinate pullback. -/
theorem smallComponent_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I' →ₗ[F2] F) :
    smallComponent (ι.comp e.symm.toLinearMap) f X =
      smallComponent ι f (X.comp e.toLinearMap) := by
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (smallFrequencyEquiv (F := F) e)
  intro T
  simp only [smallFrequencyEquiv_apply, smallCoeff_transport,
    linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

/-- The same function identity with the new embedding written as `ι ∘ g`. -/
theorem smallComponent_precomp_equiv (g : I ≃ₗ[F2] I') (ι : I' →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I →ₗ[F2] F) :
    smallComponent (ι.comp g.toLinearMap) f X =
      smallComponent ι f (X.comp g.symm.toLinearMap) := by
  simpa only [LinearEquiv.symm_symm] using smallComponent_transport g.symm ι f X

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

namespace MaxCutGames.Inverse.KMSPointComplement

noncomputable section
open MaxCutGames.Integration.BinaryLinear (F2)
open KMSAnalytic (pointLift)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

/-- The coordinates supplied by a complement to a nonzero point. -/
def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

/-- Every injection with a distinguished last coordinate can be expressed
as `pointLift` after a change of coordinates on its target. -/
theorem exists_aligned_point_equiv (ι : (I × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) :
    ∃ U : Submodule F2 E, ∃ e : (U × F2) ≃ₗ[F2] E,
      ∃ κ : I →ₗ[F2] U, Function.Injective κ ∧
        e.toLinearMap.comp (pointLift κ) = ι := by
  let z : I →ₗ[F2] E := ι.comp (LinearMap.inl F2 I F2)
  let v : E := ι (0, 1)
  have hv : v ∉ z.range := by
    rintro ⟨x, hx⟩
    have hx' : ι (x, 0) = ι (0, 1) := hx
    have h01 : (0 : F2) = 1 := congrArg Prod.snd (hι hx')
    exact zero_ne_one h01
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    rw [h]
    exact z.range.zero_mem
  obtain ⟨U, hU, hc⟩ := (Submodule.disjoint_span_singleton_of_notMem hv).exists_isCompl
  let κ : I →ₗ[F2] U := z.codRestrict U (fun x => hU ⟨x, rfl⟩)
  let e : (U × F2) ≃ₗ[F2] E := pointEquivOfIsCompl U v hv0 hc
  refine ⟨U, e, κ, ?_, ?_⟩
  · intro x y h
    have hxy : ι (x, 0) = ι (y, 0) := congrArg Subtype.val h
    exact congrArg Prod.fst (hι hxy)
  · apply LinearMap.ext
    rintro ⟨x, c⟩
    change ι (x, 0) + c • ι (0, 1) = ι (x, c)
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp

/-- A positive-dimensional binary space admits a last-point coordinate, with
an actual subspace for the remaining coordinates and the exact dimension drop. -/
theorem exists_point_equiv [FiniteDimensional F2 E]
    (h : 0 < Module.finrank F2 E) :
    ∃ U : Submodule F2 E, ∃ _e : (U × F2) ≃ₗ[F2] E,
      Module.finrank F2 U + 1 = Module.finrank F2 E := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  obtain ⟨U, hc⟩ := (Submodule.span F2 {v}).exists_isCompl
  let e := pointEquivOfIsCompl U v hv hc.symm
  refine ⟨U, e, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using e.finrank_eq

end
end MaxCutGames.Inverse.KMSPointComplement

/-!
Exact coordinate alignment for the mixed-norm induction. A chosen fixed point
is moved to the last small coordinate, and an actual ambient complement makes
its injection a pointLift. Small-component transport identifies the resulting
functions exactly, so the next recursive estimate concerns the same law.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

variable {E E0 F A A0 I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E0] [Module F2 E0]
  [AddCommGroup F] [Module F2 F] [AddCommGroup A] [Module F2 A]
  [AddCommGroup A0] [Module F2 A0] [AddCommGroup I] [Module F2 I]

/-- The injection can be aligned with the fixed-point shuffle on its domain. -/
theorem exists_mixed_aligned_point (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (eA : (A0 × F2) ≃ₗ[F2] A) :
    ∃ U : Submodule F2 E, ∃ eE : (U × F2) ≃ₗ[F2] E,
      ∃ κ : (A0 × I) →ₗ[F2] U, Function.Injective κ ∧
        eE.toLinearMap.comp (pointLift κ) =
          ι.comp (pointShuffle eA).toLinearMap :=
  KMSPointComplement.exists_aligned_point_equiv
    (ι.comp (pointShuffle eA).toLinearMap) (hι.comp (pointShuffle eA).injective)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E0 × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (((A0 × I) × F2) →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] ((A0 × I) × F2))]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (((A0 × I) × F2) →ₗ[F2] F)]

/-- Exact small function after both coordinate changes. -/
theorem smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap) (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (pointLift κ)
      (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)) =
      pointShuffleTransport eA (smallComponent ι f) := by
  have he : eE.symm.toLinearMap.comp (ι.comp (pointShuffle eA).toLinearMap) =
      pointLift κ := by
    rw [← halign]
    apply LinearMap.ext
    intro x
    simp
  have htransport := smallComponent_ambient_transport
    (E := E) (E' := E0 × F2) (F := F) (I := (A0 × I) × F2)
    eE.symm (ι.comp (pointShuffle eA).toLinearMap) f
  rw [he] at htransport
  rw [htransport]
  funext X
  exact smallComponent_precomp_equiv (I := (A0 × I) × F2) (I' := A × I)
    (E := E) (F := F) (pointShuffle eA) ι f X

/-- The original partially fixed small function is literally the function
appearing on the left side of the actual one-point mixed recurrence. -/
theorem partialRestrict_smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (smallComponent ι f) a =
      partialRestrict (pointRestrict (smallComponent (pointLift κ)
        (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)))
        (a (eA (0, 1))))
        ((a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)) := by
  rw [smallComponent_mixed_aligned ι eA eE κ halign f,
    partialRestrict_pointRestrict_pointShuffleTransport]

end

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic

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
  [Fintype (F →ₗ[F2] E)] [Fintype ((A × I) →ₗ[F2] F)]
  [Fintype (I →ₗ[F2] F)] in
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

/-!
The actual mixed-energy induction step of KMS Lemma 3.20. Previously fixed
points form A, the remaining Fourier coordinates form I, and the new fixed
point is last. The dependent graphs translate the old fixed points, which
is why the inductive bound must hold uniformly over those prescribed values.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

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
  [Fintype (((A × I) × F2) →ₗ[F2] F)]
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

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

/-- A deliberately generous rank-dependent cost for one fixed point. -/
def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

theorem one_le_mixedStepFactor (R : ℕ) : 1 ≤ mixedStepFactor R := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

/-- Character dimension is at most the number of free coordinates, so the
ambient-weight ratio has exponent at most twice the rank cap. -/
theorem mixed_step_factor_bound (R t n : ℕ) (ht : t ≤ 2 * R) (hn : n ≤ R) :
    2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) ≤ mixedStepFactor R := by
  have ht' : (2 : ℝ) ^ t ≤ 2 ^ (2 * R) :=
    pow_le_pow_right₀ (by norm_num) ht
  have hn' : ((2 : ℝ) ^ n) ^ 2 ≤ 2 ^ (2 * R) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have he : mixedStepFactor R = 4 * (2 : ℝ) ^ (2 * R) := by
    unfold mixedStepFactor
    rw [pow_add]
    ring
  rw [he]
  linarith

/-- The two lower estimates live in adjacent ambient dimensions. Multiplying
by the new weight costs q on the point-restricted branch, and nothing on the
unrestricted lower-component branch. -/
theorem mixed_weighted_step {M A B q w n C : ℝ}
    (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hrec : M ≤ 2 * (A + n ^ 2 * B))
    (hA : w * A ≤ C) (hB : (q * w) * B ≤ C) :
    (q * w) * M ≤ 2 * (q + n ^ 2) * C := by
  calc
    (q * w) * M ≤ (q * w) * (2 * (A + n ^ 2 * B)) :=
      mul_le_mul_of_nonneg_left hrec (mul_nonneg hq hw)
    _ = 2 * (q * (w * A) + n ^ 2 * ((q * w) * B)) := by ring
    _ ≤ 2 * (q * C + n ^ 2 * C) := by
      gcongr
    _ = 2 * (q + n ^ 2) * C := by ring

/-- The complete scalar induction step with a rank-independent ambient
weight and a rank-dependent but dimension-independent loss. -/
theorem mixed_weighted_step_pow (R s ell t n : ℕ) (H ε M A B : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (ht : t ≤ 2 * R) (hn : n ≤ R)
    (hrec : M ≤ 2 * (A + ((2 : ℝ) ^ n) ^ 2 * B))
    (hA : (2 : ℝ) ^ (t * ell) * A ≤ H * mixedStepFactor R ^ s * ε)
    (hB : (2 : ℝ) ^ (t * (ell + 1)) * B ≤ H * mixedStepFactor R ^ s * ε) :
    (2 : ℝ) ^ (t * (ell + 1)) * M ≤ H * mixedStepFactor R ^ (s + 1) * ε := by
  have he : (2 : ℝ) ^ (t * (ell + 1)) = 2 ^ t * 2 ^ (t * ell) := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    ring
  have hc : 0 ≤ H * mixedStepFactor R ^ s * ε :=
    mul_nonneg (mul_nonneg hH (pow_nonneg (mixedStepFactor_nonneg R) _)) hε
  have h := mixed_weighted_step (q := (2 : ℝ) ^ t)
    (w := (2 : ℝ) ^ (t * ell)) (n := (2 : ℝ) ^ n)
    (by positivity) (by positivity) hrec hA (by simpa only [he] using hB)
  rw [← he] at h
  calc
    _ ≤ 2 * ((2 : ℝ) ^ t + ((2 : ℝ) ^ n) ^ 2) *
        (H * mixedStepFactor R ^ s * ε) := h
    _ ≤ mixedStepFactor R * (H * mixedStepFactor R ^ s * ε) :=
      mul_le_mul_of_nonneg_right (mixed_step_factor_bound R t n ht hn) hc
    _ = _ := by rw [pow_succ]; ring

end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

/-- Every homogeneous output restriction of codimension at most `r` has the
stated actual normalized squared norm. The dimension inequality avoids
truncated subtraction in the restriction-composition step. -/
def HomogeneousRestrictionBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (E →ₗ[F2] C)],
    ∀ J : C →ₗ[F2] F, Function.Injective J →
      Module.finrank F2 F ≤ Module.finrank F2 C + r →
        (𝔼 X : E →ₗ[F2] C, f (J.comp X) ^ 2) ≤ ε

/-- Restricting to codimension `s` leaves the remaining budget `r`. The proof
uses only composition of actual injections and addition of dimensions. -/
theorem HomogeneousRestrictionBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound (r + s) ε f)
    (J : B →ₗ[F2] F) (hJ : Function.Injective J)
    (hcodim : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    HomogeneousRestrictionBound r ε (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro C _ _ _ _ K hK hdim
  have hdim' : Module.finrank F2 F ≤ Module.finrank F2 C + (r + s) := by omega
  simpa only [LinearMap.comp_assoc] using hf C (J.comp K) (hJ.comp hK) hdim'

/-- The unrestricted squared norm is included by the identity presentation. -/
theorem HomogeneousRestrictionBound.energy_le
    [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) : (𝔼 X, f X ^ 2) ≤ ε := by
  simpa using hf F (LinearMap.id : F →ₗ[F2] F) Function.injective_id
    (Nat.le_add_right (Module.finrank F2 F) r)

/-- A homogeneous output restriction retains the original domain-basis
invariance, as required at every step of the fixed-character induction. -/
theorem basisInvariant_codomain_pullback (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (J : B →ₗ[F2] F) :
    IsBasisInvariant (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro g X
  simpa only [LinearMap.comp_assoc] using hf g (J.comp X)

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
