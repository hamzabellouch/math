import Mathlib
import OAI.Computability.DirectedFeedback.Games.KMSAnalyticSmallTransport

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical

section FiniteFibers

variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]

theorem sum_comp_eq_fiber_card (p : A → J) (b : J → ℝ) :
    (∑ x, b (p x)) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j := by
  calc
    (∑ x, b (p x)) = ∑ x, ∑ j, if p x = j then b j else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ∑ j, ∑ x, if p x = j then b j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

theorem sum_sq_eq_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) :
    (∑ x, a x ^ 2) =
      ∑ j, ((Finset.univ.filter fun x => p x = j).card : ℝ) * b j ^ 2 := by
  simpa only [hab] using sum_comp_eq_fiber_card p (fun j => b j ^ 2)

theorem sum_sq_eq_uniform_fiber_card (p : A → J) (a : A → ℝ) (b : J → ℝ)
    (hab : ∀ x, a x = b (p x)) (n : ℕ)
    (hn : ∀ j, (Finset.univ.filter fun x => p x = j).card = n) :
    (∑ x, a x ^ 2) = (n : ℝ) * ∑ j, b j ^ 2 := by
  rw [sum_sq_eq_fiber_card p a b hab, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hn]

theorem fiber_constant_energy_cross_mul (p : A → J) (q : B → J)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (a : A → ℝ) (b : B → ℝ)
    (hab : ∀ x y, p x = q y → a x = b y)
    (nA nB : ℕ)
    (hA : ∀ j, (Finset.univ.filter fun x => p x = j).card = nA)
    (hB : ∀ j, (Finset.univ.filter fun y => q y = j).card = nB) :
    (nB : ℝ) * (∑ x, a x ^ 2) = (nA : ℝ) * ∑ y, b y ^ 2 := by
  let c : J → ℝ := fun j => b (Classical.choose (hq j))
  have ha : ∀ x, a x = c (p x) := by
    intro x
    exact hab x (Classical.choose (hq (p x)))
      (Classical.choose_spec (hq (p x))).symm
  have hb : ∀ y, b y = c (q y) := by
    intro y
    obtain ⟨x, hx⟩ := hp (q y)
    exact (hab x y hx).symm.trans (by simpa only [hx] using ha x)
  rw [sum_sq_eq_uniform_fiber_card p a c ha nA hA,
    sum_sq_eq_uniform_fiber_card q b c hb nB hB]
  ring

end FiniteFibers

open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype J]

theorem synthesis_energy_grouped (p : (F →ₗ[F2] E) → J)
    (a : (F →ₗ[F2] E) → ℝ) (b : J → ℝ) (hab : ∀ S, a S = b (p S)) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ j, ((Finset.univ.filter fun S => p S = j).card : ℝ) * b j ^ 2 := by
  rw [synthesis_energy]
  exact sum_sq_eq_fiber_card p a b hab

theorem synthesis_energy_by_kernel [Fintype (Submodule F2 F)]
    (a : (F →ₗ[F2] E) → ℝ) (b : Submodule F2 F → ℝ)
    (hab : ∀ S, a S = b S.ker) :
    (𝔼 X, synthesis a X ^ 2) =
      ∑ K : Submodule F2 F,
        ((Finset.univ.filter fun S : F →ₗ[F2] E => S.ker = K).card : ℝ) * b K ^ 2 :=
  synthesis_energy_grouped (fun S => S.ker) a b hab

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSKernelFiberCard

noncomputable section

abbrev F2 := ZMod 2

variable (F E I : Type*)
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

abbrev KernelClass :=
  {K : Submodule F2 F // Module.finrank F2 (F ⧸ K) = Module.finrank F2 I}

abbrev RankFrequency :=
  {S : F →ₗ[F2] E // Module.finrank F2 S.range = Module.finrank F2 I}

abbrev FullFrequency := {T : F →ₗ[F2] I // Function.Surjective T}

variable {F E I}

def rankKernel (S : RankFrequency F E I) : KernelClass F I :=
  ⟨S.val.ker, S.val.quotKerEquivRange.finrank_eq.trans S.property⟩

def fullKernel (T : FullFrequency F I) : KernelClass F I :=
  ⟨T.val.ker, (T.val.quotKerEquivOfSurjective T.property).finrank_eq⟩

@[simp] theorem rankKernel_val (S : RankFrequency F E I) :
    (rankKernel S).val = S.val.ker := rfl

@[simp] theorem fullKernel_val (T : FullFrequency F I) :
    (fullKernel T).val = T.val.ker := rfl

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

theorem finrank_range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R (fixedKernelEquivQuotientInjection K S).val.range =
      Module.finrank R S.val.range := by
  rw [range_forward]

theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

theorem range_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E) :
    (J.comp K.mkQ).range = J.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨K.mkQ x, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    exact ⟨x, rfl⟩

theorem quotientInjection_comp_finrank (K : Submodule R F)
    (J : (F ⧸ K) →ₗ[R] E) (hJ : Function.Injective J) :
    Module.finrank R (J.comp K.mkQ).range = Module.finrank R (F ⧸ K) := by
  rw [range_comp_mkQ]
  exact LinearMap.finrank_range_of_inj hJ

theorem natCard_fixedKernel_eq_injectiveQuotient (K : Submodule R F) :
    Nat.card {S : F →ₗ[R] E // S.ker = K} =
      Nat.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Nat.card_congr (fixedKernelEquivQuotientInjection K)

theorem card_fixedKernel_eq_injectiveQuotient (K : Submodule R F)
    [Fintype {S : F →ₗ[R] E // S.ker = K}]
    [Fintype {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}] :
    Fintype.card {S : F →ₗ[R] E // S.ker = K} =
      Fintype.card {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} :=
  Fintype.card_congr (fixedKernelEquivQuotientInjection K)

end
end DFVSGames.Inverse.KMSAnalyticKernelCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

def quotientEquiv (K : KernelClass F I) : (F ⧸ K.val) ≃ₗ[F2] I :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq K.property)

theorem rankKernel_surjective
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    Function.Surjective (rankKernel (F := F) (E := E) (I := I)) := by
  classical
  obtain ⟨j, hj⟩ :=
    (finrank_le_iff_exists_linearMap (R := F2) (M := I) (M' := E)).mp hdim
  intro K
  let J : (F ⧸ K.val) →ₗ[F2] E := j.comp (quotientEquiv K).toLinearMap
  have hJ : Function.Injective J := hj.comp (quotientEquiv K).injective
  refine ⟨⟨J.comp K.val.mkQ, ?_⟩, ?_⟩
  · exact (quotientInjection_comp_finrank K.val J hJ).trans K.property
  · apply Subtype.ext
    exact ker_comp_mkQ K.val J hJ

theorem fullKernel_surjective :
    Function.Surjective (fullKernel (F := F) (I := I)) := by
  classical
  intro K
  let T : F →ₗ[F2] I := (quotientEquiv K).toLinearMap.comp K.val.mkQ
  have hT : Function.Surjective T :=
    (quotientEquiv K).surjective.comp K.val.mkQ_surjective
  refine ⟨⟨T, hT⟩, ?_⟩
  apply Subtype.ext
  exact ker_comp_mkQ K.val (quotientEquiv K).toLinearMap (quotientEquiv K).injective

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

abbrev F2 := ZMod 2

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

def beta : ℕ := Nat.card {J : I →ₗ[F2] E // Function.Injective J}

def injectiveEquivIndependent {ι : Type*} (b : Module.Basis ι F2 I) :
    {J : I →ₗ[F2] E // Function.Injective J} ≃
      {s : ι → E // LinearIndependent F2 s} where
  toFun J := ⟨J.val ∘ b, b.linearIndependent.map' J.val (LinearMap.ker_eq_bot.mpr J.property)⟩
  invFun s := ⟨b.constr F2 s.val, b.injective_constr_of_linearIndependent s.property⟩
  left_inv J := by
    apply Subtype.ext
    exact b.constr_self F2 J.val
  right_inv s := by
    apply Subtype.ext
    funext i
    exact b.constr_basis F2 s.val i

theorem beta_eq_product [FiniteDimensional F2 I] [Finite E]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E = ∏ j : Fin (Module.finrank F2 I),
      (2 ^ Module.finrank F2 E - 2 ^ j.val) := by
  unfold beta
  rw [Nat.card_congr (injectiveEquivIndependent I E (Module.finBasis F2 I))]
  simpa only [F2, ZMod.card] using
    (card_linearIndependent (K := F2) (V := E) hdim)

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

def injectionEquivOfDomainEquiv (e : J ≃ₗ[F2] I) :
    {u : J →ₗ[F2] E // Function.Injective u} ≃
      {u : I →ₗ[F2] E // Function.Injective u} where
  toFun u := ⟨u.val.comp e.symm.toLinearMap, u.property.comp e.symm.injective⟩
  invFun u := ⟨u.val.comp e.toLinearMap, u.property.comp e.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e.symm (e x)) = u.val x
    rw [e.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e (e.symm x)) = u.val x
    rw [e.apply_symm_apply]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

def fixedKernelEquivInjection (K : KernelClass F I) :
    {S : F →ₗ[F2] E // S.ker = K.val} ≃
      {J : I →ₗ[F2] E // Function.Injective J} :=
  (fixedKernelEquivQuotientInjection K.val).trans
    (injectionEquivOfDomainEquiv (quotientEquiv K))

theorem natCard_fixedKernel_eq_beta (K : KernelClass F I) :
    Nat.card {S : F →ₗ[F2] E // S.ker = K.val} = beta I E :=
  Nat.card_congr (fixedKernelEquivInjection K)

def rankFiberEquivFixedKernel (K : KernelClass F I) :
    {S : RankFrequency F E I // rankKernel S = K} ≃
      {S : F →ₗ[F2] E // S.ker = K.val} where
  toFun S := ⟨S.val.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨⟨S.val,
    (fixedKernel_finrank_eq_quotient K.val S).trans K.property⟩,
    Subtype.ext S.property⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

omit [FiniteDimensional F2 F] in

theorem surjective_of_kernel_class (K : KernelClass F I)
    (T : F →ₗ[F2] I) (hT : T.ker = K.val) : Function.Surjective T := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (fixedKernel_finrank_eq_quotient K.val ⟨T, hT⟩).trans K.property

def fullFiberEquivFixedKernel (K : KernelClass F I) :
    {T : FullFrequency F I // fullKernel T = K} ≃
      {T : F →ₗ[F2] I // T.ker = K.val} where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, surjective_of_kernel_class K T.val T.property⟩,
    Subtype.ext T.property⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    rfl

theorem rankKernel_fiber_card [Fintype (F →ₗ[F2] E)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun S : RankFrequency F E I => rankKernel S = K)).card =
      beta I E := by
  calc
    _ = Fintype.card {S : RankFrequency F E I // rankKernel S = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {S : RankFrequency F E I // rankKernel S = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {S : F →ₗ[F2] E // S.ker = K.val} :=
      Nat.card_congr (rankFiberEquivFixedKernel K)
    _ = beta I E := natCard_fixedKernel_eq_beta K

theorem fullKernel_fiber_card [Fintype (F →ₗ[F2] I)]
    (K : KernelClass F I) :
    (Finset.univ.filter (fun T : FullFrequency F I => fullKernel T = K)).card =
      beta I I := by
  calc
    _ = Fintype.card {T : FullFrequency F I // fullKernel T = K} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card {T : FullFrequency F I // fullKernel T = K} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {T : F →ₗ[F2] I // T.ker = K.val} :=
      Nat.card_congr (fullFiberEquivFixedKernel K)
    _ = beta I I := natCard_fixedKernel_eq_beta K

end
end DFVSGames.Inverse.KMSKernelFiberCard

namespace DFVSGames.Inverse.KMSInjectionCount

open scoped BigOperators

theorem binary_factor_lower {d n j : ℕ} (hj : j < d) (hdn : d ≤ n) :
    2 ^ (n - d) ≤ 2 ^ n - 2 ^ j := by
  have hn : 0 < n := by omega
  have hjn : j ≤ n - 1 := by omega
  have hdn' : n - d ≤ n - 1 := by omega
  calc
    2 ^ (n - d) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) hdn'
    _ = 2 ^ n - 2 ^ (n - 1) := (Nat.two_pow_sub_two_pow_pred hn).symm
    _ ≤ 2 ^ n - 2 ^ j :=
      Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) hjn) _

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

theorem beta_le_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    beta I E ≤ 2 ^ (Module.finrank F2 E * Module.finrank F2 I) := by
  rw [beta_eq_product I E hdim]
  calc
    _ ≤ ∏ _j : Fin (Module.finrank F2 I), 2 ^ Module.finrank F2 E := by
      apply Finset.prod_le_prod
      intro j _
      exact Nat.sub_le _ _
    _ = _ := by simp [← pow_mul]

theorem beta_ge_pow (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) ≤
      beta I E := by
  rw [beta_eq_product I E hdim]
  calc
    _ = ∏ _j : Fin (Module.finrank F2 I),
        2 ^ (Module.finrank F2 E - Module.finrank F2 I) := by
      simp [← pow_mul, Nat.mul_comm]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro j _
      exact binary_factor_lower j.isLt hdim

theorem beta_positive (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    0 < beta I E :=
  lt_of_lt_of_le (Nat.pow_pos (by decide)) (beta_ge_pow I E hdim)

theorem beta_self_le [Finite I] :
    beta I I ≤ 2 ^ (Module.finrank F2 I * Module.finrank F2 I) :=
  beta_le_pow I I le_rfl

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSKernelOrbitsFourier
open DFVSGames.Inverse.KMSKernelFiberCard (KernelClass FullFrequency RankFrequency
  fullKernel rankKernel fullKernel_surjective rankKernel_surjective
  fullKernel_fiber_card rankKernel_fiber_card)
open DFVSGames.Inverse.KMSInjectionCount (beta)

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KernelClass F I)]

omit [Finite E] [Finite F] [Finite I] in

theorem smallComponent_energy_cross_mul (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (beta I E : ℝ) * (𝔼 X, smallComponent ι f X ^ 2) =
      (beta I I : ℝ) * (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have h := fiber_constant_energy_cross_mul
    (fullKernel (F := F) (I := I)) (rankKernel (F := F) (E := E) (I := I))
    fullKernel_surjective (rankKernel_surjective hdim)
    (fun T : FullFrequency F I => linearCoeff f (ι.comp T.val))
    (fun S : RankFrequency F E I => linearCoeff f S.val)
    (fun T S hTS => coefficient_eq_of_ker_eq f hf _ _
      ((ker_comp_of_injective ι hι T.val).trans
        (congrArg Subtype.val hTS)))
    (beta I I) (beta I E)
    (fun K => by
      have hc := fullKernel_fiber_card (F := F) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
    (fun K => by
      have hc := rankKernel_fiber_card (F := F) (E := E) (I := I) K
      convert hc using 1 ; congr 1 ; ext T ; simp)
  rw [smallComponent_energy, rankComponent_energy]
  rw [Finset.sum_subtype (p := fun T : F →ₗ[F2] I => Function.Surjective T) _ (by simp) (fun T : F →ₗ[F2] I => linearCoeff f (ι.comp T) ^ 2),
    Finset.sum_subtype (p := fun S : F →ₗ[F2] E => Module.finrank F2 S.range = Module.finrank F2 I) _ (by simp) (fun S : F →ₗ[F2] E => linearCoeff f S ^ 2)]
  exact h

omit [Finite F] [Finite I] in
theorem smallComponent_energy_ratio (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      (beta I I : ℝ) / (beta I E : ℝ) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hb : (beta I E : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (KMSInjectionCount.beta_positive I E hdim))
  apply (mul_left_cancel₀ hb)
  calc
    _ = (beta I I : ℝ) * (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) :=
      smallComponent_energy_cross_mul ι hι f hf
    _ = _ := by field_simp

omit [Finite F] in
theorem smallComponent_energy_pow_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) :
    (2 : ℝ) ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlo : (2 : ℝ) ^
      (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) ≤
      (beta I E : ℝ) := by
    exact_mod_cast KMSInjectionCount.beta_ge_pow I E hdim
  have hhi : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast KMSInjectionCount.beta_self_le I
  calc
    _ ≤ (beta I E : ℝ) * (𝔼 X, smallComponent ι f X ^ 2) :=
      mul_le_mul_of_nonneg_right hlo (Finset.expect_nonneg (fun _ _ => sq_nonneg _))
    _ = (beta I I : ℝ) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) :=
      smallComponent_energy_cross_mul ι hι f hf
    _ ≤ _ := mul_le_mul_of_nonneg_right hhi
      (Finset.expect_nonneg (fun _ _ => sq_nonneg _))

omit [Finite F] in
theorem smallComponent_energy_le_of_energy_le (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ) (hε : (𝔼 X, f X ^ 2) ≤ ε) :
    (2 : ℝ) ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * ε := by
  exact (smallComponent_energy_pow_bound ι hι f hf).trans
    (mul_le_mul_of_nonneg_left
      ((component_energy_le (fun T : F →ₗ[F2] E =>
        Module.finrank F2 T.range = Module.finrank F2 I) f).trans hε)
      (pow_nonneg (by norm_num) _))

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSInjectionCount

noncomputable section

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 I] [Finite E]

theorem pow_dim_mul_le_pow_sq_mul_beta
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ) := by
  have hexp : Module.finrank F2 I * Module.finrank F2 I +
      Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I) =
      Module.finrank F2 I * Module.finrank F2 E := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hdim]
  have hnat : 2 ^ (Module.finrank F2 I * Module.finrank F2 E) ≤
      2 ^ (Module.finrank F2 I * Module.finrank F2 I) * beta I E := by
    calc
      _ = 2 ^ (Module.finrank F2 I * Module.finrank F2 I) *
          2 ^ (Module.finrank F2 I * (Module.finrank F2 E - Module.finrank F2 I)) := by
        rw [← pow_add, hexp]
      _ ≤ _ := Nat.mul_le_mul_left _ (beta_ge_pow I E hdim)
  exact_mod_cast hnat

theorem beta_ratio_le_pow [Finite I]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E) :
    (beta I I : ℝ) / (beta I E : ℝ) ≤
      (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) /
        (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) := by
  have hb : 0 < (beta I E : ℝ) := by exact_mod_cast beta_positive I E hdim
  have hp : 0 < (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) :=
    pow_pos (by norm_num) _
  have hq : 0 ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) :=
    pow_nonneg (by norm_num) _
  have hself : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast beta_self_le I
  apply (div_le_div_iff₀ hb hp).mpr
  calc
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) :=
      mul_le_mul_of_nonneg_right hself hp.le
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ)) :=
      mul_le_mul_of_nonneg_left (pow_dim_mul_le_pow_sq_mul_beta I E hdim) hq
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

theorem pow_mul_le_of_beta_cross_mul [Finite I]
    (hdim : Module.finrank F2 I ≤ Module.finrank F2 E)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hcross : (beta I E : ℝ) * x = (beta I I : ℝ) * y) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) * x ≤
      (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * y := by
  have hq : 0 ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) :=
    pow_nonneg (by norm_num) _
  have hself : (beta I I : ℝ) ≤
      (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) := by
    exact_mod_cast beta_self_le I
  calc
    _ ≤ ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * (beta I E : ℝ)) * x :=
      mul_le_mul_of_nonneg_right (pow_dim_mul_le_pow_sq_mul_beta I E hdim) hx
    _ = (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * ((beta I I : ℝ) * y) := by
      rw [mul_assoc, hcross]
    _ ≤ (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) *
        ((2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 I) * y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hself hy) hq
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

end
end DFVSGames.Inverse.KMSInjectionCount

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v w x
variable {E : Type u} {F : Type v} {I : Type w} {J : Type x}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KMSKernelFiberCard.KernelClass F I)]

omit [Finite F] in
theorem smallComponent_energy_base_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have henergy : (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) ≤ ε :=
    (component_energy_le (fun T : F →ₗ[F2] E =>
      Module.finrank F2 T.range = Module.finrank F2 I) f).trans (hg.energy_le _ _ _)
  have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans henergy
  have hbase := KMSInjectionCount.pow_mul_le_of_beta_cross_mul I E hdim
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (smallComponent ι f _)))
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (rankComponent (Module.finrank F2 I) f _)))
    (smallComponent_energy_cross_mul ι hι f hf)
  calc
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := hbase
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * ε :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)) hε

omit [Finite F] in
theorem fixedFrequencyEnergy_zero_dim_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) (hJ : Module.finrank F2 J = 0) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  let : Subsingleton J := Module.finrank_zero_iff.mp hJ
  have hπ : π = 0 := Subsingleton.elim _ _
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hπ, hA, fixedFrequencyEnergy_zero, hJ, Nat.add_zero]
  exact smallComponent_energy_base_bound ι hι f hf ε hg

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
