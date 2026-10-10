import OAI.NumberTheory.DirichletL.Moments.RowNorm
import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => ActualEisensteinCubic.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp [pairFourier, quotientTrace]

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) := by
          exact_mod_cast product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    eisEmbedding_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem productColumnCoefficient_sextic_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    (∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)) =
      ∑ K ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2),
        productColumnCoefficient S T β K * idealRowHom z K := by
  rw [← Finset.sum_product (f := fun p : Ideal O × Ideal O =>
    β p.1 p.2 * idealRowHom z (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ S ×ˢ T) => Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro K hK
  rw [productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem productColumnCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ),
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ 1) →
      ∀ (I : Ideal O) (X : ℝ), I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ X →
        ‖productColumnCoefficient S T β I‖ ≤ D * X ^ ε := by
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro S T β hβ I X hI hX
  exact (productColumnCoefficient_norm S T β hβ I hI).trans
    ((hd I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le) hD.le))

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  ConcretePrimeRowBridge.idealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

theorem productColumnCoefficient_norm_le (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖productColumnCoefficient S T β I‖ ≤ B * (IdealMobiusDivisorSum.idealDivisors I).card := by
  unfold productColumnCoefficient
  calc
    _ ≤ ∑ p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), ‖β p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = B * ((S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast product_fiber_card (S ×ˢ T) I hI) hB

theorem productColumns_supported (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J) :
    ∀ I ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2), Supported I := by
  intro I hI
  obtain ⟨⟨J, K⟩, hp, rfl⟩ := Finset.mem_image.mp hI
  have hh := Finset.mem_product.mp hp
  exact (supported_mul_iff J K).mpr ⟨hS J hh.1, hT K hh.2⟩

def productZeroEnergy (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (K : ℝ) : ℂ :=
  idealZeroEnergy ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (productColumns_supported S T hS hT) (productColumnCoefficient S T β) K

theorem product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖productZeroEnergy S T hS hT β K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := ideal_zero_energy_bound (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 4) (by positivity)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hs := productColumns_supported S T hS hT
  have hn (I : Ideal O) (hI : I ∈ P) : (Ideal.absNorm I : ℝ) ≤ X := by
    obtain ⟨⟨J, L⟩, hp, rfl⟩ := Finset.mem_image.mp hI
    have hh := Finset.mem_product.mp hp
    exact hN J hh.1 L hh.2
  have hb (I : Ideal O) (hI : I ∈ P) :
      ‖productColumnCoefficient S T β I‖ ≤ B * (D * X ^ (ε / 4)) := by
    apply (productColumnCoefficient_norm_le S T β B hB hβ I (hs I hI).1).trans
    apply mul_le_mul_of_nonneg_left _ hB
    exact (hd I (hs I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn I hI) (by positivity)) hD.le)
  have hh := hc P hs (productColumnCoefficient S T β) X K (B * (D * X ^ (ε / 4)))
    hX hK (by positivity) hn hb
  change ‖productZeroEnergy S T hS hT β K‖ ≤ _ at hh
  apply hh.trans_eq
  have hx0 : 0 < X := by linarith
  have hp : (X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    C * K * (B * (D * X ^ (ε / 4))) ^ 2 * X ^ (1 + ε / 2) =
        (C * D ^ 2) * K * B ^ 2 * ((X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hp]

theorem normalized_product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) * productZeroEnergy S T hS hT β K‖ ≤
        C * K * B ^ 2 * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  have hx0 : 0 < X := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  calc
    _ ≤ X⁻¹ * (C * K * B ^ 2 * X ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (hc S T hS hT β X K B hX hK hB hN hβ) (by positivity)
    _ = C * K * B ^ 2 * X ^ ε := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      field_simp

theorem aggregated_rowPolynomial (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowPolynomial Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) z =
      ∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J) := by
  dsimp only
  rw [rowPolynomial]
  simp only [idealColumn_span]
  rw [Finset.sum_coe_sort ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (fun I : Ideal O => productColumnCoefficient S T β I * idealRowHom z I)]
  exact (productColumnCoefficient_sextic_row_sum S T β z).symm

theorem aggregated_rowEnergy (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowEnergy Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) W K =
      ∑' z : O, ((‖∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)‖ ^ 2 : ℝ) : ℂ) *
        W (‖eisEmbedding z‖ ^ 2 / K) := by
  simp only [CenteredMomentRowNorm.rowEnergy, aggregated_rowPolynomial]

theorem idealZeroEnergy_first_frequency (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
        (pairFourier (idealColumn S I) (idealColumn S J)
          (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0 *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (K * ‖eisEmbedding (0 : O)‖ ^ 2 /
              ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2)))) =
      idealZeroEnergy S hS c K * EisensteinSchwartzPoisson.paperRadialFourier W 0 := by
  simp [idealZeroEnergy, Finset.sum_mul, mul_assoc]

theorem normalized_product_zero_mode_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        (productZeroEnergy S T hS hT β K * EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
        C * K * B ^ 2 * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := normalized_product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β W X K B hX hK hB hN hβ
  rw [← mul_assoc, norm_mul]
  calc
    _ ≤ (C * K * B ^ 2 * X ^ ε) * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ :=
      mul_le_mul_of_nonneg_right (hc S T hS hT β X K B hX hK hB hN hβ) (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.CenteredMomentZeroMode

end

end OAI
