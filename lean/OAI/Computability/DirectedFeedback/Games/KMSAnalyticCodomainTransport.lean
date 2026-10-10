import Mathlib
import OAI.Computability.DirectedFeedback.Games.KMSKernelFiberDefs
import OAI.Computability.DirectedFeedback.Games.KMSAnalyticHyperplaneExtensions

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

theorem fixedCharacter_constant_step (n m ell : ℕ) (hnell : n < ell) :
    (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) ^ 2 * (2 : ℝ) ^ (4 * n * n) /
        ((((2 : ℝ) ^ ell - (2 : ℝ) ^ n) ^ 2) * (2 : ℝ) ^ ((n + m) * ell)) ≤
      (2 : ℝ) ^ (4 * (n + 1) * (n + 1)) /
        (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) := by
  let A : ℝ := (2 : ℝ) ^ ell
  let B : ℝ := (2 : ℝ) ^ n
  let C : ℝ := (2 : ℝ) ^ (4 * n * n)
  let C' : ℝ := (2 : ℝ) ^ (4 * (n + 1) * (n + 1))
  let P : ℝ := (2 : ℝ) ^ ((n + m) * ell)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hAB : 2 * B ≤ A := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnell
    simpa only [pow_succ, mul_comm] using h
  have hdiff : 0 < A - B := by linarith
  have hplus : (B + 1) ^ 2 ≤ 4 * B ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ B + 1 by positivity)
      (show B + 1 ≤ 2 * B by linarith)
    nlinarith only [hs]
  have hsquare : A ^ 2 ≤ 4 * (A - B) ^ 2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ A / 2 by positivity)
      (show A / 2 ≤ A - B by linarith)
    nlinarith only [hs]
  have hcoeff : B * (B + 1) ^ 2 * C ≤ 4 * B ^ 3 * C := by
    calc
      _ ≤ B * (4 * B ^ 2) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hplus hB.le) hC.le
      _ = _ := by ring
  have hconst : 16 * B ^ 3 * C ≤ C' := by
    calc
      _ = (2 : ℝ) ^ (4 + 3 * n + 4 * n * n) := by
        dsimp [B, C]
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hmain : B * (B + 1) ^ 2 * C * A ^ 2 ≤ C' * (A - B) ^ 2 := by
    calc
      _ ≤ (4 * B ^ 3 * C) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg A)
      _ ≤ (4 * B ^ 3 * C) * (4 * (A - B) ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (16 * B ^ 3 * C) * (A - B) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
  have hpower : (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell) = A ^ 2 * P := by
    dsimp [A, P]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  change B * (B + 1) ^ 2 * C / ((A - B) ^ 2 * P) ≤
    C' / (2 : ℝ) ^ (((n + 1) + (m + 1)) * ell)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [hpower]
  calc
    _ = (B * (B + 1) ^ 2 * C * A ^ 2) * P := by ring
    _ ≤ (C' * (A - B) ^ 2) * P := mul_le_mul_of_nonneg_right hmain hP.le
    _ = _ := by ring

end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

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

omit [Fintype (B →ₗ[F2] E)] [Fintype (J →ₗ[F2] (B × F2))]
  [Fintype (J →ₗ[F2] B)] [Fintype ((J × F2) →ₗ[F2] (B × F2))] in
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
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainTransport (e : F ≃ₗ[F2] F') (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F') → ℝ := fun X => f (e.symm.toLinearMap.comp X)

def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

theorem surjective_comp_codomainEquiv_iff (e : F ≃ₗ[F2] F') (T : F' →ₗ[F2] I) :
    Function.Surjective (T.comp e.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨e x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨e.symm x, ?_⟩
    simpa using hx

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)]

omit [Fintype (F' →ₗ[F2] E)] in
theorem linearCoeff_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (S' : F' →ₗ[F2] E) :
    linearCoeff (codomainTransport e f) S' = linearCoeff f (S'.comp e.toLinearMap) := by
  unfold codomainTransport
  rw [KMSFourthMoment.coefficient_codomain_pullback]
  have hc : (S'.comp e.toLinearMap).comp e.symm.toLinearMap = S' := by ext x; simp
  rw [Finset.sum_eq_single (S'.comp e.toLinearMap)]
  · rw [ite_eq_left hc]
  · intro S _ hS
    apply ite_eq_right
    intro h
    apply hS
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun R : F' →ₗ[F2] E => R (e x)) h
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (E →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E)] in

theorem basisInvariant_codomainTransport (e : F ≃ₗ[F2] F')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (codomainTransport e f) := by
  intro g X
  change f (e.symm.toLinearMap.comp (X.comp g.toLinearMap)) =
    f (e.symm.toLinearMap.comp X)
  rw [← LinearMap.comp_assoc]
  exact hf g (e.symm.toLinearMap.comp X)

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)] in
omit [Fintype (F' →ₗ[F2] E)] in
theorem smallCoeff_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F' →ₗ[F2] I) :
    smallCoeff ι (codomainTransport e f) T =
      smallCoeff ι f (T.comp e.toLinearMap) := by
  unfold smallCoeff
  rw [surjective_comp_codomainEquiv_iff]
  split_ifs
  · rw [linearCoeff_codomainTransport, LinearMap.comp_assoc]
  · rfl

omit [Fintype (F' →ₗ[F2] E)] in
theorem smallComponent_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent ι (codomainTransport e f) =
      codomainTransport e (smallComponent ι f) := by
  apply eq_of_coeff_eq
  intro T
  rw [coeff_smallComponent, linearCoeff_codomainTransport, coeff_smallComponent,
    smallCoeff_codomainTransport]

omit [FiniteDimensional F2 I] [Fintype (I →ₗ[F2] F)] [Fintype (I →ₗ[F2] F')]
  [Fintype (F' →ₗ[F2] E)] in
theorem fixedFrequencyEnergy_codomainTransport (e : F ≃ₗ[F2] F') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι (codomainTransport e f) π (A.comp e.symm.toLinearMap) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (codomainFrequencyEquiv (I := I) e)
  intro T
  have hp : π.comp (T.comp e.symm.toLinearMap) = A.comp e.symm.toLinearMap ↔
      π.comp T = A := by
    rw [← LinearMap.comp_assoc]
    exact (codomainFrequencyEquiv (I := J) e).injective.eq_iff
  simp only [codomainFrequencyEquiv_apply, smallCoeff_codomainTransport,
    codomainFrequency_cancel, hp]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w x y
variable {E : Type u} {F F' : Type v} {I : Type w} {J : Type x} {J' : Type y}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup J'] [Module F2 J']

theorem HomogeneousRestrictionBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : HomogeneousRestrictionBound s ε f) :
    HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ L hL hd
  exact hf C L hL (by omega)

theorem HomogeneousRestrictionBound.codomain_equiv
    [FiniteDimensional F2 F] [FiniteDimensional F2 F']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) (e : F ≃ₗ[F2] F') :
    HomogeneousRestrictionBound r ε (codomainTransport e f) := by
  intro C _ _ _ _ L hL hd
  have hd' : Module.finrank F2 F ≤ Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hd
  simpa only [codomainTransport, LinearMap.comp_assoc] using
    hf C (e.symm.toLinearMap.comp L) (e.symm.injective.comp hL) hd'

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_postcomp_injective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J)
    (e : J →ₗ[F2] J') (he : Function.Injective e) :
    fixedFrequencyEnergy ι f (e.comp π) (e.comp A) =
      fixedFrequencyEnergy ι f π A := by
  unfold fixedFrequencyEnergy
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    exact he (congrArg (fun L : F →ₗ[F2] J' => L x) h)
  · intro h
    rw [LinearMap.comp_assoc, h]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

def splitEquiv (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    F ≃ₗ[K] (a.ker × K) where
  toFun x := (⟨x - a x • t, by simp [LinearMap.mem_ker, ht]⟩, a x)
  invFun p := (p.1 : F) + p.2 • t
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - a (x + y) • t = (x - a x • t) + (y - a y • t)
      rw [map_add, add_smul]
      abel
    · exact a.map_add x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - a (c • x) • t = c • (x - a x • t)
      simp [smul_sub, smul_smul]
    · exact a.map_smul c x
  left_inv x := by
    change x - a x • t + a x • t = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : a (p.1 : F) = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : F) + p.2 • t - a ((p.1 : F) + p.2 • t) • t = p.1
      simp [hp, ht]
    · change a ((p.1 : F) + p.2 • t) = p.2
      simp [hp, ht]

@[simp] theorem splitEquiv_apply_snd (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    (splitEquiv a t ht x).2 = a x := rfl

@[simp] theorem splitEquiv_apply_fst_coe (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    ((splitEquiv a t ht x).1 : F) = x - a x • t := rfl

@[simp] theorem splitEquiv_symm_apply (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (p : a.ker × K) :
    (splitEquiv a t ht).symm p = (p.1 : F) + p.2 • t := rfl

@[simp] theorem splitEquiv_symm_apply_zero (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : (splitEquiv a t ht).symm (b, 0) = (b : F) := by
  simp

@[simp] theorem splitEquiv_apply_ker (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : splitEquiv a t ht (b : F) = (b, 0) := by
  apply (splitEquiv a t ht).symm.injective
  simp

@[simp] theorem splitEquiv_apply_unit (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    splitEquiv a t ht t = (0, 1) := by
  apply (splitEquiv a t ht).symm.injective
  simp

theorem finrank_eq_ker_add_one [FiniteDimensional K F]
    (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    Module.finrank K F = Module.finrank K a.ker + 1 := by
  have h := (splitEquiv a t ht).finrank_eq
  simpa [Module.finrank_prod] using h

end DFVSGames.Inverse.KMSAnalyticFunctionalSplit

namespace DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def targetEquiv (s : CompatibleSplitting π A) : K ≃ₗ[F2] (s.K0 × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv s.functional s.targetVector
    s.functional_targetVector

def leftEquiv (s : CompatibleSplitting π A) : I ≃ₗ[F2] (s.J × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

def rightEquiv (s : CompatibleSplitting π A) : F ≃ₗ[F2] (s.B × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

@[simp] theorem leftMap_apply_val (s : CompatibleSplitting π A) (x : s.J) :
    (s.leftMap x : K) = π x := rfl

@[simp] theorem rightMap_apply_val (s : CompatibleSplitting π A) (x : s.B) :
    (s.rightMap x : K) = A x := rfl

theorem leftMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.leftMap := by
  intro y
  obtain ⟨x, hx⟩ := s.left_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (π x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

theorem rightMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.rightMap := by
  intro y
  obtain ⟨x, hx⟩ := s.right_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (A x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

@[simp] theorem leftEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    s.leftEquiv.symm x = (x.1 : I) + x.2 • s.leftVector := rfl

@[simp] theorem rightEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    s.rightEquiv.symm x = (x.1 : F) + x.2 • s.rightVector := rfl

@[simp] theorem targetEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.K0 × F2) :
    s.targetEquiv.symm x = (x.1 : K) + x.2 • s.targetVector := rfl

theorem left_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    π (s.leftEquiv.symm x) = s.targetEquiv.symm (s.leftMap x.1, x.2) := by
  change π ((x.1 : I) + x.2 • s.leftVector) = π x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.leftVector_image]

theorem right_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    A (s.rightEquiv.symm x) = s.targetEquiv.symm (s.rightMap x.1, x.2) := by
  change A ((x.1 : F) + x.2 • s.rightVector) = A x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.rightVector_image]

theorem left_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (π.comp s.leftEquiv.symm.toLinearMap) =
      s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (π (s.leftEquiv.symm x)) = (s.leftMap x.1, x.2)
  rw [s.left_symm_apply, s.targetEquiv.apply_symm_apply]

theorem right_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (A.comp s.rightEquiv.symm.toLinearMap) =
      s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (A (s.rightEquiv.symm x)) = (s.rightMap x.1, x.2)
  rw [s.right_symm_apply, s.targetEquiv.apply_symm_apply]

theorem target_finrank [FiniteDimensional F2 K] (s : CompatibleSplitting π A) :
    Module.finrank F2 K = Module.finrank F2 s.K0 + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one s.functional s.targetVector
    s.functional_targetVector

theorem left_finrank [FiniteDimensional F2 I] (s : CompatibleSplitting π A) :
    Module.finrank F2 I = Module.finrank F2 s.J + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

theorem right_finrank [FiniteDimensional F2 F] (s : CompatibleSplitting π A) :
    Module.finrank F2 F = Module.finrank F2 s.B + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

end CompatibleSplitting

theorem exists_compatibleSplitting [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : Nonempty (CompatibleSplitting π A) := by
  classical
  let b := Module.finBasis F2 K
  let j : Fin (Module.finrank F2 K) := ⟨0, hdim⟩
  obtain ⟨i, hi⟩ := hπ (b j)
  obtain ⟨f, hf⟩ := hA (b j)
  refine ⟨⟨b.coord j, b j, ?_, i, hi, f, hf, hπ, hA⟩⟩
  simp

def chooseSplit [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : CompatibleSplitting π A :=
  Classical.choice (exists_compatibleSplitting π A hπ hA hdim)

end
end DFVSGames.Inverse.KMSAnalyticCompatibleSplitting

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSBasisInvariant

universe u v w x

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {E : Type u} [AddCommGroup E] [Module F2 E]
  [FiniteDimensional F2 E] [Fintype E]

private theorem fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction :
    ∀ (n : ℕ) (F : Type v) [AddCommGroup F] [Module F2 F]
      [FiniteDimensional F2 F] [Fintype F]
      (I : Type w) [AddCommGroup I] [Module F2 I]
      [FiniteDimensional F2 I] [Fintype I]
      (J : Type x) [AddCommGroup J] [Module F2 J]
      [FiniteDimensional F2 J] [Fintype J],
      Module.finrank F2 J = n →
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), IsBasisInvariant f →
      ∀ (ε : ℝ), HomogeneousRestrictionBound (Module.finrank F2 I) ε f →
      ∀ (π : I →ₗ[F2] J), Function.Surjective π → ∀ A : F →ₗ[F2] J,
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
          fixedFrequencyEnergy ι f π A ≤
        (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F _ _ _ _ I _ _ _ _ J _ _ _ _ hJn ι hι f hf ε hg π hπ A
    let : Finite (KMSKernelFiberCard.KernelClass F I) :=
      Finite.of_surjective (KMSKernelFiberCard.fullKernel (F := F) (I := I))
        (KMSKernelFiberCard.fullKernel_surjective (F := F) (I := I))
    let : Fintype (KMSKernelFiberCard.KernelClass F I) := Fintype.ofFinite _
    have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans
      (HomogeneousRestrictionBound.energy_le _ ε f hg)
    by_cases hn : n = 0
    · exact fixedFrequencyEnergy_zero_dim_bound ι hι f hf ε hg π A (hJn.trans hn)
    by_cases hA : Function.Surjective A
    · have hp : 0 < Module.finrank F2 J := by omega
      let s := KMSAnalyticCompatibleSplitting.chooseSplit π A hπ hA hp
      let ι' : (s.J × F2) →ₗ[F2] E := ι.comp s.leftEquiv.symm.toLinearMap
      let f' : (E →ₗ[F2] (s.B × F2)) → ℝ := codomainTransport s.rightEquiv f
      have hι' : Function.Injective ι' := hι.comp s.leftEquiv.symm.injective
      have hf' : IsBasisInvariant f' := basisInvariant_codomainTransport s.rightEquiv f hf
      have hg' : HomogeneousRestrictionBound (Module.finrank F2 s.J + 1) ε f' := by
        have h := HomogeneousRestrictionBound.codomain_equiv _ ε f hg s.rightEquiv
        simpa only [s.left_finrank] using h
      have hs : Module.finrank F2 s.K0 < n := by
        have hdim : Module.finrank F2 J = Module.finrank F2 s.K0 + 1 := s.target_finrank
        omega
      have hgfirst : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε
          (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X)) :=
        HomogeneousRestrictionBound.codomain_pullback _ 1 ε f' hg'
          (LinearMap.inl F2 s.B F2) (by intro x y h; exact congrArg Prod.fst h)
          (by simp only [Module.finrank_prod, Module.finrank_self]; omega)
      have hglower : HomogeneousRestrictionBound (Module.finrank F2 s.J) ε f' :=
        HomogeneousRestrictionBound.mono (Nat.le_succ _) ε f' hg'
      have hfirst := ih (Module.finrank F2 s.K0) hs s.B s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι')
        (fun X : E →ₗ[F2] s.B => f' ((LinearMap.inl F2 s.B F2).comp X))
        (basisInvariant_codomain_pullback f' hf' (LinearMap.inl F2 s.B F2))
        ε hgfirst s.leftMap s.leftMap_surjective s.rightMap
      have hlower (w : s.J) := ih (Module.finrank F2 s.K0) hs (s.B × F2) s.J s.K0 rfl
        (leftEmbedding ι') (leftEmbedding_injective ι' hι') f' hf'
        ε hglower s.leftMap s.leftMap_surjective (hyperplaneExtend s.rightMap (s.leftMap w))
      have hrec := fixedFrequencyEnergy_product_bound ι' hι' f' hf'
        s.leftMap s.rightMap ε hε hfirst hlower
      have htransport : fixedFrequencyEnergy ι' f'
          (s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2))
          (s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) =
          fixedFrequencyEnergy ι f π A := by
        rw [← s.left_conjugation, ← s.right_conjugation,
          fixedFrequencyEnergy_postcomp_injective _ _ _ _ s.targetEquiv.toLinearMap
            s.targetEquiv.injective]
        change fixedFrequencyEnergy (ι.comp s.leftEquiv.symm.toLinearMap)
          (codomainTransport s.rightEquiv f) (π.comp s.leftEquiv.symm.toLinearMap)
          (A.comp s.rightEquiv.symm.toLinearMap) = _
        rw [fixedFrequencyEnergy_codomainTransport, fixedFrequencyEnergy_transport]
      rw [htransport, ← s.leftEquiv.finrank_eq, ← s.targetEquiv.finrank_eq] at hrec
      exact hrec
    · rw [fixedFrequencyEnergy_eq_zero_of_not_surjective ι f π hπ A hA, mul_zero]
      positivity

theorem fixedFrequencyEnergy_le_of_homogeneous
    {F : Type v} [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 F] [Fintype F]
    {I : Type w} [AddCommGroup I] [Module F2 I]
    [FiniteDimensional F2 I] [Fintype I]
    {J : Type x} [AddCommGroup J] [Module F2 J]
    [FiniteDimensional F2 J] [Fintype J]
    (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (ε : ℝ) (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π) (A : F →ₗ[F2] J) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π A ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε :=
  fixedFrequencyEnergy_bound_induction_inline_KMSAnalyticCharacterInduction (Module.finrank F2 J) F I J rfl ι hι f hf ε hg π hπ A

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

universe u v
attribute [local instance] mapFintype

variable {E A I J : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 A]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J] [FiniteDimensional F2 F]
  [Fintype E] [Fintype A] [Fintype I] [Fintype J] [Fintype F]

theorem mixed_slice_bound (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ Module.finrank F2 A * ε := by
  have hi : Module.finrank F2 I ≤ R := by omega
  have hpow : (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) ≤
      2 ^ (4 * R * R) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hi
  apply mixed_bound_of_character_bound R ((2 : ℝ) ^ (4 * R * R)) ε
    (by positivity) hε π ν hπ ?_ (Module.finrank F2 A) E A rfl ι hι f hf hd a hr
  intro E' _ _ _ _ κ hκ g hg hgd
  exact (fixedFrequencyEnergy_le_of_homogeneous κ hκ g hg ε
    (AffineDensityBound.homogeneous _ ε g hgd) π hπ ν).trans
      (mul_le_mul_of_nonneg_right hpow hε)

def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

theorem mixedRankConstant_nonneg (R : ℕ) : 0 ≤ mixedRankConstant R := by
  unfold mixedRankConstant
  exact mul_nonneg (by positivity) (pow_nonneg (mixedStepFactor_nonneg R) _)

theorem mixed_slice_bound_uniform (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        mixedRankConstant R * ε := by
  apply (mixed_slice_bound R ε hε ι hι f hf hd a π hπ ν hr).trans
  unfold mixedRankConstant
  have hp : mixedStepFactor R ^ Module.finrank F2 A ≤ mixedStepFactor R ^ R :=
    pow_le_pow_right₀ (one_le_mixedStepFactor R) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) hε

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
