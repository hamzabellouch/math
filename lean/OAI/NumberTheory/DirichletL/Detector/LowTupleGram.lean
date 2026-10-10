import OAI.NumberTheory.DirichletL.Detector.LowGramIntegrated
import OAI.NumberTheory.DirichletL.Detector.LowInverseEnergy

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramFactor (C : CalibrationData) (X Y δ : ℝ) : ℝ :=
  Real.sqrt ((lowPhysicalScale C X Y/Y)*(1+(Y^2/lowPhysicalScale C X Y)^(1/6:ℝ)+
    (Y^2/lowPhysicalScale C X Y)^2/Y)*Y^δ)

def lowInverseMass (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) : ℝ :=
  ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2)

lemma lowInverseMass_nonneg (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    0≤lowInverseMass C a b ha hb X Y hX hY B :=
  Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)

lemma low_mellin_normalizer_norm (Q : ℝ) (_hQ : 0<Q) :
    ‖(Real.sqrt Q:ℂ)⁻¹*(1/(2*Real.pi):ℂ)‖=(Real.sqrt Q)⁻¹/(2*Real.pi) := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_div,norm_one,norm_mul]
  norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  ring

theorem compensation_tuple_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
    ∃C : ℝ,0<C ∧ ∀(K : ℕ)(η : HeckeFamily.Character)(slots : Fin K→Finset O)
      (hslots : ∀i x,x∈slots i→x≠0)(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ)
      (X Y T t : ℝ)(hX : 0<X)(hY : 0<Y)(_hT : 0<T),
      (∀a : LowUnselectedTuple slots J,1≤Y/elementNorm (∏i : J,(a i).val))→
      (∀a : LowUnselectedTuple slots J,
        1≤(Y/elementNorm (∏i : J,(a i).val))^2/
          lowPhysicalScale (calibrationForSet S hS) (X/elementNorm (∏i : J,(a i).val))
            (Y/elementNorm (∏i : J,(a i).val)))→
      ‖∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
          selectedSlotFactor W P (fun i=>(p i).val) J t‖≤
      C*∑a : LowUnselectedTuple slots J,
        ‖lowUnselectedWeight slots J W P a‖*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (div_pos hX (lowUnselectedProduct_norm_pos slots hslots J a))
          (div_pos hY (lowUnselectedProduct_norm_pos slots hslots J a))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
            η S hS (lowSelectedIdeal slots J) T t) := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  intro S hS hbad
  obtain ⟨C,hC,hgram⟩ := lowSeparatedIntegral_actual_gram δ hδ hδ1 a1 b1 M ha1 hab1 hM
    W1 hW1c hW1 hW1s hWM (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) W0 a0 b0 ha0 hW0 hW0s S hS hbad
  refine ⟨C,hC,?_⟩
  intro K η slots hslots J W P X Y T t hX hY hT hYs hPs
  rw [compensation_tuple_low_polynomial η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    slots hslots J W P X Y T t hX hY hT]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  have hh := hgram (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
    (div_pos hX hL) (hYs a)
    (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
      η S hS (lowSelectedIdeal slots J) T t) (hPs a)
  rw [norm_mul,norm_mul,low_mellin_normalizer_norm _ (lowPhysicalScale_pos _ _ _ (div_pos hX hL) (div_pos hY hL))]
  calc
    _≤‖lowUnselectedWeight slots J W P a‖*
      ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
      (C*lowGramFactor (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
      lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
        (div_pos hX hL) (div_pos hY hL) _) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
