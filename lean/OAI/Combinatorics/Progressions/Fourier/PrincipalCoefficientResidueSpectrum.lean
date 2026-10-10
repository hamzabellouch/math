import OAI.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
import OAI.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

private theorem independent_residue_weighted_product
    {B : Type*} [Fintype B] [DecidableEq B]
    {X R : B → Type*} [∀ b, Fintype (X b)] [∀ b, Fintype (R b)]
    [∀ b, DecidableEq (R b)]
    (p : ∀ b, FiniteProbabilityWeights (X b)) (label : ∀ b, X b → R b)
    (a : (∀ b, R b) → ℂ) (g : ∀ b, X b → ℂ) :
    (FiniteProbabilityWeights.pi p).complexMean
      (fun x => a (fun b => label b (x b)) * ∏ b, g b (x b)) =
        ∑ r, a r * ∏ b, (p b).fiberComplexMean (label b) (r b) (g b) := by
  let f := fun (r : ∀ b, R b) (x : ∀ b, X b) => a r * ∏ b, if label b (x b) = r b then g b (x b) else 0
  have hf (x : ∀ b, X b) : (∑ r, f r x) =
      a (fun b => label b (x b)) * ∏ b, g b (x b) := by
    simp only [f, Fintype.prod_ite_zero, ← funext_iff, mul_ite, mul_zero]
    simp
  rw [show (fun x => a (fun b => label b (x b)) * ∏ b, g b (x b)) =
      fun x => ∑ r, f r x from funext (fun x => (hf x).symm),
    FiniteProbabilityWeights.complexMean_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [show f r = fun x => a r * ∏ b,
      if label b (x b) = r b then g b (x b) else 0 from rfl,
    FiniteProbabilityWeights.complexMean_mul_left,
    FiniteProbabilityWeights.complexMean_pi_product p
      (fun b x => if label b x = r b then g b x else 0)]
  rfl

noncomputable def weightedModerateResidueBlockCoefficient
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (r : ZMod q) (M : ℕ) [NeZero M]
    (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M) : ℂ :=
  c.source.fiberComplexMean (fun z => ((z none : ℤ) : ZMod q)) r
    (fun z => (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean (fun x =>
      rectangularGridCharacter M k (weightedModerateIntegerBlock c s J offset (z, x))))

theorem weightedModerateIntegerJetSum_residue_coefficient
    {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (a : (B → ZMod q) → ℂ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I))
    (offset : B → ℤ) (shift : J → ℤ) (k : J → Fin M) :
    (weightedModerateIntegerProductSource c s).complexMean (fun x =>
      a (fun b => ((x b).1 none : ℤ)) *
        rectangularGridCharacter M k (weightedModerateIntegerJetSum c s J offset shift x)) =
      rectangularGridCharacter M k shift * ∑ r : B → ZMod q,
        a r * ∏ b, weightedModerateResidueBlockCoefficient (c b) (s b) q (r b) M J (offset b) k := by
  simp only [weightedModerateIntegerJetSum, rectangularGridCharacter_add,
    rectangularGridCharacter_fintype_sum]
  have he (x : ∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) : a (fun b => (((x b).1 none : ℤ) : ZMod q)) *
      (rectangularGridCharacter M k shift *
        ∏ b, rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (x b))) =
      rectangularGridCharacter M k shift *
        (a (fun b => (((x b).1 none : ℤ) : ZMod q)) *
          ∏ b, rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (x b))) := by ring
  simp_rw [he]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  rw [weightedModerateIntegerProductSource, independent_residue_weighted_product
    (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b z => ((z.1 none : ℤ) : ZMod q)) a
    (fun b z => rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) z))]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  unfold FiniteProbabilityWeights.fiberComplexMean weightedModerateIntegerSource
    weightedModerateResidueBlockCoefficient
  rw [FiniteProbabilityWeights.complexMean_prod]
  congr 1
  funext z
  by_cases hz : (z none : ℤ) = (r b : ZMod q)
  · simp only [hz, ite_true]
  · simp only [hz, ite_false, FiniteProbabilityWeights.complexMean_const]

theorem weightedModerateResidueBlockCoefficient_eq_condition
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (r : ZMod q) (M : ℕ) [NeZero M]
    (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M)
    (hr : 0 < c.source.mass (Finset.univ.filter
      (fun z => ((z none : ℤ) : ZMod q) = r))) :
    weightedModerateResidueBlockCoefficient c s q r M J offset k =
      (c.source.mass (Finset.univ.filter (fun z => ((z none : ℤ) : ZMod q) = r)) : ℂ) *
        (c.source.condition _ hr).complexMean (fun z =>
          (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean (fun x =>
            rectangularGridCharacter M k (weightedModerateIntegerBlock c s J offset (z, x)))) := by
  exact c.source.fiberComplexMean_eq_condition _ _ _ hr

theorem weightedModerateResidueBlockCoefficient_norm_le
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (r : ZMod q) (M : ℕ) [NeZero M]
    (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M) :
    ‖weightedModerateResidueBlockCoefficient c s q r M J offset k‖ ≤
      (c.source.fiberLaw (fun z => ((z none : ℤ) : ZMod q))).weight r := by
  unfold weightedModerateResidueBlockCoefficient FiniteProbabilityWeights.fiberComplexMean
  apply (c.source.norm_complexMean_le_mean_norm _).trans
  apply c.source.mean_mono
  intro z
  by_cases hz : ((z none : ℤ) : ZMod q) = r
  · simp only [hz, ite_true]
    have hb := (FiniteProbabilityWeights.pi (fun j => (s j).source)).norm_complexMean_le_mean_norm
      (fun x => rectangularGridCharacter M k (weightedModerateIntegerBlock c s J offset (z, x)))
    simpa only [rectangularGridCharacter_norm, FiniteProbabilityWeights.mean_const] using hb
  · simp only [hz, ite_false, norm_zero, le_refl]

theorem weightedModerateResidueProduct_coefficient_mass
    {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (a : (B → ZMod q) → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (k : J → Fin M) :
    (∑ r : B → ZMod q, ‖a r * ∏ b,
      weightedModerateResidueBlockCoefficient (c b) (s b) q (r b) M J (offset b) k‖) ≤ 1 := by
  let p := fun b => (c b).source.fiberLaw (fun z => ((z none : ℤ) : ZMod q))
  calc
    _ ≤ ∑ r : B → ZMod q, ∏ b, (p b).weight (r b) := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, norm_prod]
      apply (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (ha r)).trans
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun b _ => weightedModerateResidueBlockCoefficient_norm_le (c b) (s b) q (r b) M J (offset b) k)
    _ = 1 := (FiniteProbabilityWeights.pi p).total

theorem weighted_integerGridDensity_fourier
    {X O : Type*} [Fintype X] [Fintype O] [DecidableEq O]
    (p : FiniteProbabilityWeights X) (Y : X → O → ℤ) (a : X → ℂ)
    (K M : ℕ) [NeZero M] (z : O → ℤ) :
    (K : ℂ) ^ Fintype.card O * p.complexMean
      (fun x => if integerGridResidue M (Y x) = integerGridResidue M z then a x else 0) =
        ((K : ℂ) / M) ^ Fintype.card O * ∑ k : O → Fin M,
          p.complexMean (fun x => a x * rectangularGridCharacter M k (Y x)) *
            star (rectangularGridCharacter M k z) := by
  have hi : (∑ k : O → Fin M,
      p.complexMean (fun x => a x * rectangularGridCharacter M k (Y x)) *
        star (rectangularGridCharacter M k z)) =
      (M : ℂ) ^ Fintype.card O * p.complexMean
        (fun x => if integerGridResidue M (Y x) = integerGridResidue M z then a x else 0) := by
    calc
      _ = ∑ x, (p.weight x : ℂ) * a x *
          (∑ k : O → Fin M, rectangularGridCharacter M k (Y x) *
            star (rectangularGridCharacter M k z)) := by
        simp only [FiniteProbabilityWeights.complexMean, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        simp only [rectangularGridCharacter_orthogonality,
          FiniteProbabilityWeights.complexMean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : integerGridResidue M (Y x) = integerGridResidue M z <;> simp [hx, mul_comm, mul_left_comm]
  rw [hi, div_pow]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

theorem weightedModerateIntegerJetSum_residue_density_fourier
    {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (q : ℕ) [NeZero q] (a : (B → ZMod q) → ℂ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I))
    (offset : B → ℤ) (shift z : J → ℤ) :
    (K : ℂ) ^ J.card * (weightedModerateIntegerProductSource c s).complexMean (fun x =>
      if integerGridResidue M (weightedModerateIntegerJetSum c s J offset shift x) =
        integerGridResidue M z then a (fun b => ((x b).1 none : ℤ)) else 0) =
      ((K : ℂ) / M) ^ J.card * ∑ k : J → Fin M,
        (∑ r : B → ZMod q, a r * ∏ b,
          weightedModerateResidueBlockCoefficient (c b) (s b) q (r b) M J (offset b) k) *
          (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)) := by
  rw [show J.card = Fintype.card J from Fintype.card_coe J |>.symm,
    weighted_integerGridDensity_fourier]
  simp only [Fintype.card_coe, weightedModerateIntegerJetSum_residue_coefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weightedModerateIntegerJetSum_coefficient_mixture
    {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (a : (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I))
    (offset : B → ℤ) (shift : J → ℤ) (k : J → Fin M) :
    (weightedModerateIntegerProductSource c s).complexMean (fun x =>
      a (fun b => (x b).1) *
        rectangularGridCharacter M k (weightedModerateIntegerJetSum c s J offset shift x)) =
      rectangularGridCharacter M k shift *
        (FiniteProbabilityWeights.pi (fun b => (c b).source)).complexMean (fun z => a z * ∏ b,
          (FiniteProbabilityWeights.pi (fun j => (s b j).source)).complexMean (fun x =>
            rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (z b,x)))) := by
  simp only [weightedModerateIntegerJetSum, rectangularGridCharacter_add,
    rectangularGridCharacter_fintype_sum]
  have he (x : ∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :
      a (fun b => (x b).1) * (rectangularGridCharacter M k shift *
        ∏ b, rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (x b))) =
      rectangularGridCharacter M k shift * (a (fun b => (x b).1) *
        ∏ b, rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (x b))) := by ring
  simp_rw [he]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  rw [weightedModerateIntegerProductSource, independent_residue_weighted_product
    (fun b => weightedModerateIntegerSource (c b) (s b)) (fun _ z => z.1) a
    (fun b z => rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) z))]
  have hb (b) (z : IntegerScalarCubeBox Empty (c b).length) :
      (weightedModerateIntegerSource (c b) (s b)).fiberComplexMean (fun u => u.1) z
        (fun x => rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) x)) =
      ((c b).source.weight z : ℂ) *
        (FiniteProbabilityWeights.pi (fun j => (s b j).source)).complexMean (fun x =>
          rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (z,x))) := by
    unfold FiniteProbabilityWeights.fiberComplexMean weightedModerateIntegerSource
    rw [FiniteProbabilityWeights.complexMean_prod]
    change (∑ u, ((c b).source.weight u : ℂ) * _) = _
    have hi (u : IntegerScalarCubeBox Empty (c b).length) :
        (FiniteProbabilityWeights.pi (fun j => (s b j).source)).complexMean (fun x =>
          if u = z then rectangularGridCharacter M k
            (weightedModerateIntegerBlock (c b) (s b) J (offset b) (u,x)) else 0) =
        if u = z then (FiniteProbabilityWeights.pi (fun j => (s b j).source)).complexMean (fun x =>
          rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J (offset b) (u,x))) else 0 := by
      by_cases hu : u = z <;> simp [hu, FiniteProbabilityWeights.complexMean_const]
    simp only [hi, mul_ite, mul_zero]
    simp
  simp only [hb, Finset.prod_mul_distrib, ← Complex.ofReal_prod,
    FiniteProbabilityWeights.complexMean, FiniteProbabilityWeights.pi]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem spectrumTail_complexMean_weighted_on_support
    {R O : Type*} [Fintype R] [Fintype O] [DecidableEq O]
    (p : FiniteProbabilityWeights R) (a : R → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1)
    (f : R → O → ℂ) (S : Finset O) {ε : ℝ}
    (he : ∀ r, p.weight r ≠ 0 → spectrumTail S (fun k => ‖f r k‖) ≤ ε) :
    spectrumTail S (fun k => ‖p.complexMean (fun r => a r * f r k)‖) ≤ ε := by
  unfold spectrumTail
  calc
    _ ≤ ∑ k, if k ∈ S then 0 else p.mean (fun r => ‖f r k‖) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k ∈ S
      · simp only [hk, ite_true, le_refl]
      simp only [hk, ite_false]
      apply (p.norm_complexMean_le_mean_norm _).trans
      apply p.mean_mono
      intro r
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ha r)
    _ = p.mean (fun r => spectrumTail S (fun k => ‖f r k‖)) := by
      unfold FiniteProbabilityWeights.mean spectrumTail
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ S <;> simp [hk]
    _ ≤ ε := (p.mean_mono_on_support he).trans_eq (p.mean_const ε)

theorem weightedModerateIntegerProductSource_short_correlated_spectrum_tail
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n N : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (a : (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ)
    (ha : ∀ z, ‖a z‖ ≤ 1)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 →
      ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hshort : ∀ b, (c b).length ≤ N)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hbudget : scalarCubePrimitiveEnvelope Empty A 1 0 (N + 1) ≤ U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} [NeZero M] (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1) (shift : J → ℤ)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U (4 * V) *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U (4 * V) L ζ)
      (fun k => ‖(weightedModerateIntegerProductSource c s).complexMean (fun x =>
        a (fun b => (x b).1) * rectangularGridCharacter M k
          (weightedModerateIntegerJetSum c s J (fun _ => 0) shift x))‖) ≤ ε := by
  simp_rw [weightedModerateIntegerJetSum_coefficient_mixture,
    norm_mul, rectangularGridCharacter_norm, one_mul]
  apply spectrumTail_complexMean_weighted_on_support _ a ha
  intro z hz
  have hz' (b : B) : (c b).source.weight (z b) ≠ 0 := by
    intro hb
    apply hz
    exact Finset.prod_eq_zero (Finset.mem_univ b) hb
  have htail := fixedPositiveCoefficientSource_uniform_spectrum_tail c s z hz'
    hpositive hshort A hA hU hbudget h hV hW hL hζ hζ1 hε hlen hM hscale
    J hJ hB hsize haccuracy
  have he (b : B) (k : J → Fin M)
      (x : ∀ j, IntegerScalarCubeBox I (s b j).length) :
      rectangularGridCharacter M k (weightedModerateIntegerBlock (c b) (s b) J 0 (z b, x)) =
        CircleFourier.character
          (((z b none : ℝ) * booleanBlockPhase (gridJetFrequency M J k)
            (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle) := by
    rw [rectangularGridCharacter_eq]
    simp only [weightedModerateIntegerBlock, zero_add, integerBooleanBlockJet_scaled_pairing]
  simpa only [he] using htail

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
  (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
  (q : ℕ) [NeZero q] (hq : 0 < q)
  (hlength : scalarCubeNormalizationThreshold Empty q 32
    (256 * probabilityProfileLipschitz) ≤ principalIntervalLength K T γ)

theorem principalCoefficientResidueBlock_eq
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin n → NormalizedScalarCubeSource I) (r : ZMod q)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (k : J → Fin M) :
    weightedModerateResidueBlockCoefficient (principalNormalizedSource hK hT hγ hlarge)
      s q r M J 0 k =
      (((principalNormalizedSource hK hT hγ hlarge).source.fiberLaw
        (fun z => ((z none : ℤ) : ZMod q))).weight r : ℂ) *
      weightedModerateGridCoefficient
        (principalCoefficientResidueSource hK hT hγ hlarge q hq r hlength) s 0 M J k := by
  have hp := principalCoefficientResidue_mass_pos_filter hK hT hγ hlarge q hq r hlength
  rw [weightedModerateResidueBlockCoefficient_eq_condition _ s q r M J 0 k hp,
    FiniteProbabilityWeights.fiberLaw_weight_eq_mass]
  congr 1
  have hl := principalCoefficientResidueSource_law_filter hK hT hγ hlarge q hq r hlength
  unfold weightedModerateGridCoefficient
  rw [hl]
  congr 1
  funext z
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  simp only [weightedModerateIntegerBlock, integerBooleanBlockJet_scaled_pairing,
    zero_add]

include hq hlength in
theorem principalCoefficientResidue_correlated_spectrum_tail
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (a : (B → ZMod q) → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} [NeZero M] (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / ((principalIntervalLength K T γ : ℝ) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U V *
      2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
      (fun k => ‖∑ r : B → ZMod q, a r * ∏ b,
        weightedModerateResidueBlockCoefficient (principalNormalizedSource hK hT hγ hlarge)
          (s b) q (r b) M J 0 k‖) ≤ ε := by
  let p := (principalNormalizedSource hK hT hγ hlarge).source.fiberLaw
    (fun z => ((z none : ℤ) : ZMod q))
  let c := fun (r : B → ZMod q) b =>
    principalCoefficientResidueSource hK hT hγ hlarge q hq (r b) hlength
  have hc (r : B → ZMod q) (b : B) : ScalarCubePrimitiveBudget (c r b) A U :=
    (principalCoefficientResidueSource_primitive hK hT hγ hlarge q hq (r b) hlength A).mono hU
  have ht (r : B → ZMod q) :
      spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
        (fun k => ‖∏ b, weightedModerateGridCoefficient (c r b) (s b) 0 M J k‖) ≤ ε := by
    apply weightedPositiveModerate_uniform_spectrum_tail (c r) s A hA
      ((principalCoefficientResidueSource_primitive hK hT hγ hlarge q hq 0 hlength A).one_le.trans hU)
      (hc r) hs
      (fun b => principalCoefficientResidueSource_positive_support hK hT hγ hlarge q hq (r b) hlength)
      hV hW hL hζ hζ1 hε hlen hM hscale J hJ hB hsize haccuracy
  have he (k : J → Fin M) : (∑ r : B → ZMod q, a r * ∏ b,
      weightedModerateResidueBlockCoefficient (principalNormalizedSource hK hT hγ hlarge)
        (s b) q (r b) M J 0 k) =
      (FiniteProbabilityWeights.pi (fun _ : B => p)).complexMean
        (fun r => a r * ∏ b, weightedModerateGridCoefficient (c r b) (s b) 0 M J k) := by
    simp only [principalCoefficientResidueBlock_eq hK hT hγ hlarge q hq hlength,
      Finset.prod_mul_distrib, ← Complex.ofReal_prod,
      FiniteProbabilityWeights.complexMean, FiniteProbabilityWeights.pi]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [he]
  exact spectrumTail_complexMean_weighted_on_support _ a ha _ _ (fun r _ => ht r)

end Erdos3

end

end OAI
