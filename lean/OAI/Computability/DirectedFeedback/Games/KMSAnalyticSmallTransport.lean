import Mathlib
import OAI.Computability.DirectedFeedback.Probability.KMSFourthMomentZoomTransport

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

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

theorem smallCoeff_transport (e : I ≃ₗ[F2] I') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (ι.comp e.symm.toLinearMap) f (e.toLinearMap.comp T) =
      smallCoeff ι f T := by
  unfold smallCoeff
  rw [surjective_smallFrequencyEquiv_iff, smallFrequency_transport_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 I'] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I' →ₗ[F2] F)] in

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

theorem smallComponent_precomp_equiv (g : I ≃ₗ[F2] I') (ι : I' →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I →ₗ[F2] F) :
    smallComponent (ι.comp g.toLinearMap) f X =
      smallComponent ι f (X.comp g.symm.toLinearMap) := by
  simpa only [LinearEquiv.symm_symm] using smallComponent_transport g.symm ι f X

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSPointComplement

noncomputable section
open DFVSGames.Integration.BinaryLinear (F2)
open KMSAnalytic (pointLift)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

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
end DFVSGames.Inverse.KMSPointComplement

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {E E0 F A A0 I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E0] [Module F2 E0]
  [AddCommGroup F] [Module F2 F] [AddCommGroup A] [Module F2 A]
  [AddCommGroup A0] [Module F2 A0] [AddCommGroup I] [Module F2 I]

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E0] [FiniteDimensional F2 F]
  [FiniteDimensional F2 A] [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (((A0 × I) × F2) →ₗ[F2] F)]

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
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

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
theorem mixedEnergy_zeroFixed (ι : (A × I) →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) =
      fixedFrequencyEnergy (ι.comp (LinearMap.inr F2 A I)) f π ν := by
  rw [partialRestrict_smallComponent_zeroFixed]
  simp only [sliceEnergy, fixedFrequencyEnergy, coeff_smallComponent]

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

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
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment

def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

theorem one_le_mixedStepFactor (R : ℕ) : 1 ≤ mixedStepFactor R := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

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

end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

def HomogeneousRestrictionBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (E →ₗ[F2] C)],
    ∀ J : C →ₗ[F2] F, Function.Injective J →
      Module.finrank F2 F ≤ Module.finrank F2 C + r →
        (𝔼 X : E →ₗ[F2] C, f (J.comp X) ^ 2) ≤ ε

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

theorem HomogeneousRestrictionBound.energy_le
    [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) : (𝔼 X, f X ^ 2) ≤ ε := by
  simpa using hf F (LinearMap.id : F →ₗ[F2] F) Function.injective_id
    (Nat.le_add_right (Module.finrank F2 F) r)

theorem basisInvariant_codomain_pullback (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (J : B →ₗ[F2] F) :
    IsBasisInvariant (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro g X
  simpa only [LinearMap.comp_assoc] using hf g (J.comp X)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem pointAppend_comp_basis (X : E →ₗ[F2] F) (a : F) (g : E ≃ₗ[F2] E) :
    pointAppend (X.comp g.toLinearMap) a =
      (pointAppend X a).comp (g.prodCongr (LinearEquiv.refl F2 F2)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rfl

theorem pointRestrict_invariant (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : F) :
    KMSBasisInvariant.IsBasisInvariant (pointRestrict f a) := by
  intro g X
  change f (pointAppend (X.comp g.toLinearMap) a) = f (pointAppend X a)
  rw [pointAppend_comp_basis]
  exact hf (g.prodCongr (LinearEquiv.refl F2 F2)) (pointAppend X a)

theorem pointAppend_add (X : E →ₗ[F2] F) (a : F)
    (Z : (E × F2) →ₗ[F2] F) :
    pointAppend X a + Z =
      pointAppend (X + Z.comp (LinearMap.inl F2 E F2)) (a + Z (0, 1)) := by
  have hZ (x : E) (c : F2) : Z (x, c) = Z (x, 0) + c • Z (0, 1) := by
    calc
      Z (x, c) = Z ((x, 0) + c • (0, 1)) := by simp
      _ = Z (x, 0) + c • Z (0, 1) := by rw [map_add, map_smul]
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, c⟩
  simp only [LinearMap.add_apply, pointAppend_apply, LinearMap.comp_apply,
    LinearMap.inl_apply, smul_add]
  rw [hZ]
  abel

theorem pointRestrict_translate (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (Z : (E × F2) →ₗ[F2] F) (a : F) :
    pointRestrict (fun Y => f (Y + Z)) a =
      fun X => pointRestrict f (a + Z (0, 1))
        (X + Z.comp (LinearMap.inl F2 E F2)) := by
  funext X
  change f (pointAppend X a + Z) = _
  rw [pointAppend_add]
  rfl

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

def AffineDensityBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]
    (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (D →ₗ[F2] C)],
    ∀ L : E →ₗ[F2] D, Function.Surjective L →
    ∀ J : C →ₗ[F2] F, Function.Injective J →
    ∀ T : E →ₗ[F2] F,
      Module.finrank F2 E + Module.finrank F2 F ≤
        Module.finrank F2 D + Module.finrank F2 C + r →
      (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) ≤ ε

theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

theorem AffineDensityBound.homogeneous [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) : HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ J hJ hdim
  have h := hf E C (LinearMap.id : E →ₗ[F2] E) Function.surjective_id
    J hJ 0 (by omega)
  simpa using h

theorem AffineDensityBound.pointRestrict [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound (r + 1) ε f) (a : F) :
    AffineDensityBound r ε (pointRestrict f a) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  let L' : (E × F2) →ₗ[F2] D := L.comp (LinearMap.fst F2 E F2)
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    exact ⟨(x, 0), hx⟩
  have hdim' : Module.finrank F2 (E × F2) + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + 1) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have he (X : D →ₗ[F2] C) :
      pointAppend (T + J.comp (X.comp L)) a =
        pointAppend T a + J.comp (X.comp L') := by
    apply LinearMap.ext
    intro p
    rcases p with ⟨x, c⟩
    simp only [pointAppend_apply, LinearMap.add_apply, LinearMap.comp_apply,
      L', LinearMap.fst_apply]
    abel
  have h := hf D C L' hL' J hJ (pointAppend T a) hdim'
  simpa only [KMSAnalytic.pointRestrict, he] using h

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)

universe u v
variable {E E' : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup B] [Module F2 B]

theorem AffineDensityBound.domain_equiv
    [FiniteDimensional F2 E] [FiniteDimensional F2 E']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) (e : E ≃ₗ[F2] E') :
    AffineDensityBound r ε (fun X : E' →ₗ[F2] F => f (X.comp e.toLinearMap)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hdim
  have h := hf D C (L.comp e.toLinearMap) (hL.comp e.surjective) J hJ
    (T.comp e.toLinearMap) hdim'
  simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using h

theorem AffineDensityBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound (r + s) ε f)
    (K : B →ₗ[F2] F) (hK : Function.Injective K)
    (hdimK : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    AffineDensityBound r ε (fun X : E →ₗ[F2] B => f (K.comp X)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + s) := by omega
  have h := hf D C L hL (K.comp J) (hK.comp hJ) (K.comp T) hdim'
  simpa only [LinearMap.comp_add, LinearMap.comp_assoc] using h

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {F : Type v} {I J : Type u}
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Fintype F] [Fintype I] [Fintype J]

omit [FiniteDimensional F2 J] [Fintype J] in

theorem mixed_bound_of_character_bound (R : ℕ) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J)
    (hπ : Function.Surjective π)
    (hbase : ∀ (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E],
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 I) ε f →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π ν ≤ H * ε) :
    ∀ (n : ℕ) (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E]
      (A : Type u) [AddCommGroup A] [Module F2 A]
      [FiniteDimensional F2 A] [Fintype A],
      Module.finrank F2 A = n →
      ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f →
      ∀ (a : A →ₗ[F2] F), Module.finrank F2 A + Module.finrank F2 I ≤ R →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
          H * mixedStepFactor R ^ n * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ A _ _ _ _ hAn ι hι f hf hd a hr
    by_cases hn : n = 0
    · have hz : Module.finrank F2 A = 0 := hAn.trans hn
      let : Subsingleton A := Module.finrank_zero_iff.mp hz
      have hi : Function.Injective (ι.comp (LinearMap.inr F2 A I)) := by
        intro x y hxy
        exact congrArg Prod.snd (hι hxy)
      have hd0 : AffineDensityBound (Module.finrank F2 I) ε f := by simpa [hz] using hd
      rw [mixedEnergy_zeroFixed]
      simpa only [hn, pow_zero, mul_one] using
        hbase E (ι.comp (LinearMap.inr F2 A I)) hi f hf hd0
    · have hp : 0 < Module.finrank F2 A := by omega
      obtain ⟨A0, eA, hAdrop⟩ := KMSPointComplement.exists_point_equiv hp
      change Module.finrank F2 A0 + 1 = Module.finrank F2 A at hAdrop
      obtain ⟨E0, eE, κ, hκ, halign⟩ := exists_mixed_aligned_point ι hι eA
      let f' : ((E0 × F2) →ₗ[F2] F) → ℝ :=
        fun X => f (X.comp eE.symm.toLinearMap)
      let a0 : A0 →ₗ[F2] F := (a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)
      let b : F := a (eA (0, 1))
      let r0 := Module.finrank F2 A0 + Module.finrank F2 I
      let t := Module.finrank F2 I + Module.finrank F2 J
      have hs : Module.finrank F2 A0 < n := by omega
      have hr0 : r0 ≤ R := by dsimp [r0]; omega
      have hf' : KMSBasisInvariant.IsBasisInvariant f' :=
        ambient_basisInvariant_transport eE.symm f hf
      have hd' : AffineDensityBound (r0 + 1) ε f' := by
        have h := AffineDensityBound.domain_equiv _ ε f hd eE.symm
        have he : Module.finrank F2 A + Module.finrank F2 I = r0 + 1 := by
          dsimp [r0]; omega
        simpa only [he] using h
      have hdp : AffineDensityBound r0 ε (pointRestrict f' b) :=
        AffineDensityBound.pointRestrict r0 ε f' hd' b
      have hdo : AffineDensityBound r0 ε f' :=
        AffineDensityBound.mono (Nat.le_succ r0) ε f' hd'
      have hdimE : Module.finrank F2 E = Module.finrank F2 E0 + 1 := by
        simpa only [Module.finrank_prod, Module.finrank_self] using eE.finrank_eq.symm
      have ht : t ≤ 2 * R := by
        have hji : Module.finrank F2 J ≤ Module.finrank F2 I :=
          LinearMap.finrank_le_finrank_of_surjective hπ
        dsimp [t]
        omega
      have hcard : (Fintype.card ((A0 × I) →ₗ[F2] F2) : ℝ) = (2 : ℝ) ^ r0 := by
        rw [Module.card_eq_pow_finrank (K := F2)]
        simp [Module.finrank_prod, r0, F2, ZMod.card]
      let C := H * mixedStepFactor R ^ Module.finrank F2 A0 * ε
      let W0 : ℝ := 2 ^ (t * Module.finrank F2 E0)
      let W1 : ℝ := 2 ^ (t * (Module.finrank F2 E0 + 1))
      have hW0 : 0 < W0 := by dsimp [W0]; positivity
      have hW1 : 0 < W1 := by dsimp [W1]; positivity
      have hfirst : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent κ (pointRestrict f' b)) a0) ≤ C / W0 := by
        apply (le_div_iff₀ hW0).mpr
        have h := ih (Module.finrank F2 A0) hs E0 A0 rfl κ hκ
          (pointRestrict f' b) (pointRestrict_invariant f' hf' b) hdp a0 hr0
        simpa only [C, W0, t, mul_comm] using h
      have hsecond (a' : A0 →ₗ[F2] F) : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent (pointPad κ) f') a') ≤ C / W1 := by
        apply (le_div_iff₀ hW1).mpr
        have h := ih (Module.finrank F2 A0) hs (E0 × F2) A0 rfl
          (pointPad κ) (pointPad_injective κ hκ) f' hf' hdo a' hr0
        simpa only [C, W1, t, Module.finrank_prod, Module.finrank_self, mul_comm] using h
      have hrec := mixed_point_sliceEnergy_le_of_bounds κ hκ f' hf' a0 b
        (fun T => π.comp T = ν) (C / W0) (C / W1) hfirst hsecond
      rw [hcard] at hrec
      have hweighted := mixed_weighted_step_pow R (Module.finrank F2 A0)
        (Module.finrank F2 E0) t r0 H ε _ (C / W0) (C / W1)
        hH hε ht hr0 hrec
        (by change W0 * (C / W0) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW0)])
        (by change W1 * (C / W1) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW1)])
      rw [partialRestrict_smallComponent_mixed_aligned ι eA eE κ halign f a]
      simpa only [hdimE, ← hAn, ← hAdrop, f', a0, b, t] using hweighted

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
