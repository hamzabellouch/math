import Mathlib
import OAI.Computability.DirectedFeedback.Probability.KMSFourthMomentZoomTransport

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 B]

theorem character_codomain_composition (J : B →ₗ[F2] F)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] B) :
    linearTraceCharacter S (J.comp X) = linearTraceCharacter (S.comp J) X := by
  simp only [linearTraceCharacter_apply]
  congr 1
  rw [linearTracePair_swap (J.comp X) S, linearTracePair_swap X (S.comp J)]
  simp only [linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in

theorem coefficient_codomain_pullback (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : F →ₗ[F2] E, if S.comp J = T then linearCoeff f S else 0 := by
  have hexpand : (fun X => f (J.comp X)) =
      ∑ S : F →ₗ[F2] E, linearCoeff f S •
        (fun X => (linearTraceCharacter (S.comp J) X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa only [character_codomain_composition] using
      (linear_fourier_inversion f (J.comp X)).symm
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.comp J = T
  · simp [hS]
  · simp [hS, Ne.symm hS]

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_codomain_pullback_fiber (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : {S : F →ₗ[F2] E // S.comp J = T}, linearCoeff f S.val := by
  rw [coefficient_codomain_pullback]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun S _ => S.val) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property⟩
  · intro S _ R _ h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S, (Finset.mem_filter.mp hS).2⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rfl

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

def hyperplaneExtend (z : B →ₗ[F2] E) (v : E) : (B × F2) →ₗ[F2] E :=
  z.coprod (LinearMap.toSpanSingleton F2 E v)

@[simp] theorem hyperplaneExtend_apply (z : B →ₗ[F2] E) (v : E) (b : B) (c : F2) :
    hyperplaneExtend z v (b, c) = z b + c • v := rfl

@[simp] theorem hyperplaneExtend_comp_inl (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).comp (LinearMap.inl F2 B F2) = z :=
  LinearMap.coprod_inl _ _

@[simp] theorem hyperplaneExtend_new_coordinate (z : B →ₗ[F2] E) (v : E) :
    hyperplaneExtend z v (0, 1) = v := by simp

theorem hyperplaneExtend_recover (S : (B × F2) →ₗ[F2] E) :
    hyperplaneExtend (S.comp (LinearMap.inl F2 B F2)) (S (0, 1)) = S := by
  have h : LinearMap.toSpanSingleton F2 E (S (0, 1)) =
      S.comp (LinearMap.inr F2 B F2) := by
    ext
    simp
  rw [hyperplaneExtend, h, LinearMap.coprod_comp_inl_inr]

def hyperplaneExtensionEquiv (z : B →ₗ[F2] E) :
    E ≃ {S : (B × F2) →ₗ[F2] E // S.comp (LinearMap.inl F2 B F2) = z} where
  toFun v := ⟨hyperplaneExtend z v, hyperplaneExtend_comp_inl z v⟩
  invFun S := S.1 (0, 1)
  left_inv v := hyperplaneExtend_new_coordinate z v
  right_inv S := by
    apply Subtype.ext
    change hyperplaneExtend z (S.1 (0, 1)) = S.1
    simpa only [S.2] using hyperplaneExtend_recover S.1

theorem hyperplaneExtend_injective (z : B →ₗ[F2] E) :
    Function.Injective (hyperplaneExtend z) := by
  intro u v h
  simpa using congrArg (fun S : (B × F2) →ₗ[F2] E => S (0, 1)) h

theorem range_hyperplaneExtend (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).range = z.range ⊔ Submodule.span F2 {v} := by
  rw [hyperplaneExtend, LinearMap.range_coprod, LinearMap.range_toSpanSingleton]

theorem range_hyperplaneExtend_of_mem (z : B →ₗ[F2] E) {v : E} (hv : v ∈ z.range) :
    (hyperplaneExtend z v).range = z.range := by
  rw [range_hyperplaneExtend, sup_eq_left]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv

theorem ker_hyperplaneExtend_of_notMem (z : B →ₗ[F2] E) {v : E}
    (hv : v ∉ z.range) :
    (hyperplaneExtend z v).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  have hv0 : v ≠ 0 := fun h => hv (h.symm ▸ z.range.zero_mem)
  have hd : Disjoint z.range (LinearMap.toSpanSingleton F2 E v).range := by
    rw [LinearMap.range_toSpanSingleton]
    exact Submodule.disjoint_span_singleton_of_notMem hv
  rw [hyperplaneExtend, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
    LinearMap.ker_toSpanSingleton F2 hv0]

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

theorem coefficient_hyperplaneExtend_eq (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {u v : E} (hu : u ∉ z.range) (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z u) = linearCoeff f (hyperplaneExtend z v) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [ker_hyperplaneExtend_of_notMem z hu, ker_hyperplaneExtend_of_notMem z hv]

variable [Fintype E]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] B × F2)] in

theorem card_hyperplaneExtension_outside (z : B →ₗ[F2] E) :
    (Finset.univ.filter (fun v : E => v ∉ z.range)).card =
      Fintype.card E - Fintype.card z.range := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_subtype_compl (fun v : E => v ∈ z.range)

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] B × F2)] in
theorem card_hyperplaneExtension_outside_pow (z : B →ₗ[F2] E) :
    (Finset.univ.filter (fun v : E => v ∉ z.range)).card =
      2 ^ Module.finrank F2 E - 2 ^ Module.finrank F2 z.range := by
  rw [card_hyperplaneExtension_outside, Module.card_eq_pow_finrank (K := F2) (V := E),
    Module.card_eq_pow_finrank (K := F2) (V := z.range)]
  simp only [F2, ZMod.card]

theorem sum_hyperplaneExtend_outside (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u with u ∉ z.range, linearCoeff f (hyperplaneExtend z u)) =
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  calc
    _ = ∑ _u ∈ Finset.univ.filter (fun u : E => u ∉ z.range),
        linearCoeff f (hyperplaneExtend z v) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact coefficient_hyperplaneExtend_eq f hf z (Finset.mem_filter.mp hu).2 hv
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_hyperplaneExtension_outside]

theorem sum_hyperplaneExtend (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    (∑ u : E, linearCoeff f (hyperplaneExtend z u)) =
      (∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) +
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) *
        linearCoeff f (hyperplaneExtend z v) := by
  rw [← sum_hyperplaneExtend_outside f hf z hv]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u => u ∈ z.range) (fun u => linearCoeff f (hyperplaneExtend z u))).symm

theorem coefficient_hyperplaneExtend_recursion (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] E)
    {v : E} (hv : v ∉ z.range) :
    linearCoeff f (hyperplaneExtend z v) =
      ((∑ u : E, linearCoeff f (hyperplaneExtend z u)) -
        ∑ u with u ∈ z.range, linearCoeff f (hyperplaneExtend z u)) /
      ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) := by
  have hlt : Fintype.card z.range < Fintype.card E :=
    Fintype.card_subtype_lt hv
  have hne : ((Fintype.card E - Fintype.card z.range : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
  apply (eq_div_iff hne).mpr
  rw [sum_hyperplaneExtend f hf z hv]
  ring

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {E B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B]
  [Fintype E]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
theorem coefficient_hyperplane_restriction
    (f : (E →ₗ[F2] (B × F2)) → ℝ) (z : B →ₗ[F2] E) :
    linearCoeff (fun X => f ((LinearMap.inl F2 B F2).comp X)) z =
      ∑ u : E, linearCoeff f (hyperplaneExtend z u) := by
  rw [coefficient_codomain_pullback_fiber]
  exact ((hyperplaneExtensionEquiv z).sum_comp
    (fun S => linearCoeff f S.val)).symm

omit [Fintype (B →ₗ[F2] E)] in
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
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSFourthMoment

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
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

def leftEmbedding (ι : (J × F2) →ₗ[F2] E) : J →ₗ[F2] E :=
  ι.comp (LinearMap.inl F2 J F2)

theorem leftEmbedding_injective (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : Function.Injective (leftEmbedding ι) := by
  intro x y h
  have hxy : (x, (0 : F2)) = (y, 0) := hι h
  exact congrArg Prod.fst hxy

theorem lastVector_not_mem_left_range (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : ι (0, 1) ∉ (leftEmbedding ι).range := by
  rintro ⟨j, hj⟩
  have h : (j, (0 : F2)) = (0, 1) := hι hj
  exact zero_ne_one (congrArg Prod.snd h)

theorem range_left_comp_of_surjective (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    ((leftEmbedding ι).comp z).range = (leftEmbedding ι).range := by
  ext v
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨z b, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨b, rfl⟩ := hz j
    exact ⟨b, rfl⟩

def liftedRangeEquiv (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    J ≃ ((leftEmbedding ι).comp z).range :=
  Equiv.ofBijective
    (fun j => ⟨leftEmbedding ι j, by
      rw [range_left_comp_of_surjective ι z hz]
      exact ⟨j, rfl⟩⟩)
    ⟨by
      intro x y h
      exact leftEmbedding_injective ι hι (congrArg Subtype.val h),
      by
      rintro ⟨v, b, rfl⟩
      exact ⟨z b, rfl⟩⟩

@[simp] theorem liftedRangeEquiv_val (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (z : B →ₗ[F2] J) (hz : Function.Surjective z) (j : J) :
    (liftedRangeEquiv ι hι z hz j).val = leftEmbedding ι j := rfl

theorem card_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    Fintype.card ((leftEmbedding ι).comp z).range = Fintype.card J :=
  (Fintype.card_congr (liftedRangeEquiv ι hι z hz)).symm

theorem sum_lifted_range [Fintype E] [Fintype J]
    (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) (a : E → ℝ) :
    (∑ u : ((leftEmbedding ι).comp z).range, a u.val) =
      ∑ j : J, a (leftEmbedding ι j) :=
  ((liftedRangeEquiv ι hι z hz).sum_comp (fun u => a u.val)).symm

theorem hyperplaneExtend_left_comp (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (w : J) :
    hyperplaneExtend ((leftEmbedding ι).comp z) (leftEmbedding ι w) =
      (leftEmbedding ι).comp (hyperplaneExtend z w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [hyperplaneExtend, map_add, map_smul]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]

theorem hyperplaneExtend_old_injective (w : J) :
    Function.Injective (fun z : B →ₗ[F2] J => hyperplaneExtend z w) := by
  intro z z' h
  have hc := congrArg
    (fun T : (B × F2) →ₗ[F2] J => T.comp (LinearMap.inl F2 B F2)) h
  simpa only [hyperplaneExtend_comp_inl] using hc

theorem hyperplaneExtend_surjective {z : B →ₗ[F2] J}
    (hz : Function.Surjective z) (w : J) :
    Function.Surjective (hyperplaneExtend z w) := by
  intro y
  obtain ⟨b, hb⟩ := hz y
  refine ⟨(b, 0), ?_⟩
  simpa using hb

theorem comp_hyperplaneExtend (π : J →ₗ[F2] K) (z : B →ₗ[F2] J) (w : J) :
    π.comp (hyperplaneExtend z w) = hyperplaneExtend (π.comp z) (π w) := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  simp [LinearMap.comp_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))] in
theorem dependent_extension_energy_le
    (ι : J →ₗ[F2] E) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (π : J →ₗ[F2] K) (A0 : B →ₗ[F2] K) (w : J) :
    (∑ z : B →ₗ[F2] J with π.comp z = A0 ∧ Function.Surjective z,
      linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
        fixedFrequencyEnergy ι f π (hyperplaneExtend A0 (π w)) := by
  let P : Finset (B →ₗ[F2] J) :=
    Finset.univ.filter fun z => π.comp z = A0 ∧ Function.Surjective z
  let Q : Finset ((B × F2) →ₗ[F2] J) :=
    Finset.univ.filter fun T =>
      π.comp T = hyperplaneExtend A0 (π w) ∧ Function.Surjective T
  have hsub : P.image (fun z => hyperplaneExtend z w) ⊆ Q := by
    intro T hT
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hT
    have hp := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hyperplaneExtend_surjective hp.2 w⟩
    rw [comp_hyperplaneExtend, hp.1]
  rw [fixedFrequencyEnergy_eq]
  change (∑ z ∈ P, linearCoeff f (ι.comp (hyperplaneExtend z w)) ^ 2) ≤
    ∑ T ∈ Q, linearCoeff f (ι.comp T) ^ 2
  calc
    _ = ∑ T ∈ P.image (fun z => hyperplaneExtend z w),
        linearCoeff f (ι.comp T) ^ 2 := by
      rw [Finset.sum_image]
      exact fun z _ z' _ h => hyperplaneExtend_old_injective w h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun T _ _ => sq_nonneg _)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

variable {E B J K : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J] [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 E] [FiniteDimensional F2 B] [FiniteDimensional F2 J]
  [Fintype E] [Fintype J]
  [Fintype (E →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype ((B × F2) →ₗ[F2] J)]
  [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)]

omit [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] B × F2)] [Fintype (B × F2 →ₗ[F2] J)] [Fintype (J →ₗ[F2] B)] [Fintype (B →ₗ[F2] J)] in

omit [Fintype (B →ₗ[F2] E)] in
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

omit [Fintype (J →ₗ[F2] B)] [FiniteDimensional F2 J]
  [Fintype (J →ₗ[F2] (B × F2))] [Fintype (B →ₗ[F2] E)] in
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
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

theorem blockFrequency_surjective_iff (z : B →ₗ[F2] J) (w : J) :
    Function.Surjective (blockFrequency z w) ↔ Function.Surjective z := by
  constructor
  · intro h y
    obtain ⟨⟨b, c⟩, hx⟩ := h (y, 0)
    have hc : c = 0 := congrArg Prod.snd hx
    refine ⟨b, ?_⟩
    simpa only [blockFrequency_apply, hc, zero_smul, add_zero] using congrArg Prod.fst hx
  · intro h x
    obtain ⟨b, hb⟩ := h (x.1 - x.2 • w)
    refine ⟨(b, x.2), ?_⟩
    simp only [blockFrequency_apply, hb, sub_add_cancel, Prod.eta]

theorem ker_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    (blockFrequency z w).ker = z.ker.prod (⊥ : Submodule F2 F2) := by
  ext ⟨b, c⟩
  change ((z b + c • w, c) = (0, 0)) ↔ (z b = 0 ∧ c = 0)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by simpa using h, rfl⟩
  · rintro ⟨h, rfl⟩
    simpa using h

theorem blockFrequency_compatible_iff (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (z : B →ₗ[F2] J) (w : J) :
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp (blockFrequency z w) =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) ↔ π.comp z = A ∧ π w = 0 := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro b
      simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (b, 0)).1) h
    · simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (0, 1)).1) h
  · rintro ⟨hz, hw⟩
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : π (z b) = A b := congrArg (fun T : B →ₗ[F2] K => T b) hz
    simp [hb, hw]

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

theorem blockFrequency_recover (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (T : (B × F2) →ₗ[F2] (J × F2))
    (hT : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) :
    blockFrequency (blockOld T) (blockNew T) = T := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun R : (B × F2) →ₗ[F2] J => R x)
      (hyperplaneExtend_recover ((LinearMap.fst F2 J F2).comp T))
  · have h := congrArg (fun R : (B × F2) →ₗ[F2] (K × F2) => (R x).2) hT
    exact h.symm

abbrev CompatibleBlockFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {T : (B × F2) →ₗ[F2] (J × F2) // Function.Surjective T ∧
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)}

abbrev CompatibleOldFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {z : B →ₗ[F2] J // Function.Surjective z ∧ π.comp z = A}

def compatibleBlockFrequencyEquiv (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    CompatibleBlockFrequency π A ≃ CompatibleOldFrequency π A × π.ker where
  toFun T := by
    have hr := blockFrequency_recover π A T.val T.property.2
    have hc : π.comp (blockOld T.val) = A ∧ π (blockNew T.val) = 0 :=
      (blockFrequency_compatible_iff π A _ _).mp (by rw [hr]; exact T.property.2)
    refine (⟨blockOld T.val, ?_, hc.1⟩, ⟨blockNew T.val, hc.2⟩)
    apply (blockFrequency_surjective_iff (blockOld T.val) (blockNew T.val)).mp
    rw [hr]
    exact T.property.1
  invFun p := ⟨blockFrequency p.1.val p.2.val,
    (blockFrequency_surjective_iff _ _).mpr p.1.property.1,
    (blockFrequency_compatible_iff π A _ _).mpr ⟨p.1.property.2, p.2.property⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact blockFrequency_recover π A T.val T.property.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact blockOld_blockFrequency _ _
    · apply Subtype.ext
      exact blockNew_blockFrequency _ _

variable [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] (B × F2))]

theorem coefficient_blockFrequency_eq (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (z : B →ₗ[F2] J) (u v : J) :
    linearCoeff f (ι.comp (blockFrequency z u)) =
      linearCoeff f (ι.comp (blockFrequency z v)) := by
  apply KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hι),
    ker_blockFrequency, ker_blockFrequency]

variable [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype J]
  [Fintype ((B × F2) →ₗ[F2] E)] [Fintype (B →ₗ[F2] J)]
  [Fintype ((J × F2) →ₗ[F2] (B × F2))]
  [Fintype ((B × F2) →ₗ[F2] (J × F2))]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 J] [Fintype (B × F2 →ₗ[F2] E)] [Fintype (J × F2 →ₗ[F2] B × F2)] in

theorem fixedFrequencyEnergy_block (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] (B × F2)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    fixedFrequencyEnergy ι f (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
      (A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
      (Fintype.card π.ker : ℝ) * ∑ z : CompatibleOldFrequency π A,
        linearCoeff f (ι.comp (blockFrequency z.val 0)) ^ 2 := by
  let e := compatibleBlockFrequencyEquiv π A
  calc
    _ = ∑ T : CompatibleBlockFrequency π A, linearCoeff f (ι.comp T.val) ^ 2 := by
      unfold fixedFrequencyEnergy
      rw [← Finset.sum_subtype (Finset.univ.filter (fun T : (B × F2) →ₗ[F2] (J × F2) =>
          Function.Surjective T ∧
            (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
              A.prodMap (LinearMap.id : F2 →ₗ[F2] F2))) (by simp)
          (fun T => linearCoeff f (ι.comp T) ^ 2),
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hs : Function.Surjective T <;>
        by_cases hp : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
            A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) <;> simp [smallCoeff, hs, hp]
    _ = ∑ p : CompatibleOldFrequency π A × π.ker,
        linearCoeff f (ι.comp (blockFrequency p.1.val p.2.val)) ^ 2 := by
      apply Fintype.sum_equiv e
      intro T
      exact congrArg (fun R : (B × F2) →ₗ[F2] (J × F2) =>
        linearCoeff f (ι.comp R) ^ 2) (congrArg Subtype.val (e.symm_apply_apply T)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [coefficient_blockFrequency_eq ι hι f hf _ _ 0]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

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

omit [Fintype ((J × F2) →ₗ[F2] (B × F2))] [Fintype (J →ₗ[F2] B)]
  [FiniteDimensional F2 J] [Fintype (J →ₗ[F2] (B × F2))] [Fintype (B →ₗ[F2] E)] in
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
end DFVSGames.Inverse.KMSAnalytic

end OAI
