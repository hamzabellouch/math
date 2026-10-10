import OAI.NumberTheory.DirichletL.Detector.LowGramPoisson
import OAI.NumberTheory.DirichletL.Moments.SecondDiagonal

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramZeroMode (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  (Q:ℂ)*paperRadialFourier U 0*
    secondZeroEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property) (lowGaussColumn C W1 Y σ v)

lemma lowGramZeroMode_eq_source (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    lowGramZeroMode C W1 hW1 Y hY σ v U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) 0*paperRadialFourier U 0 := by
  unfold lowGramZeroMode secondZeroEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het]
  calc
    _ = ((lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
        ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ))))*
        actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val) _ _ 0*paperRadialFourier U 0 := by ring
    _ = _ := by rw [lowGram_pair_prefactor C W1 Y hY σ v Q s t];ring

lemma lowGramZeroMode_bound (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0≤Q) :
    ‖lowGramZeroMode C W1 hW1 Y hY σ v U Q‖≤
      Q*‖paperRadialFourier U 0‖*∑s∈lowGaussColumns W1 hW1 Y hY,‖lowGaussColumn C W1 Y σ v s‖^2 := by
  rw [lowGramZeroMode,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply secondZeroEnergy_bound
  · intro s
    exact (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).2
  · intro s hs t ht h
    apply Subtype.ext
    have hes := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
    have het := (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1
    rw [←hes,←het]
    exact congrArg (fun z : O=>Ideal.span {z}) h

theorem lowGramZeroMode_source_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b→(∀x,‖W1 x‖≤B)→
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0≤Q→
      ‖lowGramZeroMode (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q‖≤
        C*‖paperRadialFourier U 0‖*Q/Y := by
  obtain ⟨C,hC,hb⟩ := lowGaussColumn_l2_bound a b B ha hB
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hWS hWB Y hY σ v U Q hQ
  apply (lowGramZeroMode_bound (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q hQ).trans
  calc
    _ ≤ Q*‖paperRadialFourier U 0‖*(C/Y) := by
      exact mul_le_mul_of_nonneg_left (hb S hS W1 hW1 hWS hWB Y hY σ v) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
