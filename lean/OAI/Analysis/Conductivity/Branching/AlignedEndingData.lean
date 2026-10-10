import Mathlib
import OAI.Analysis.Conductivity.Fourier.CascadePeriodicity
import OAI.Analysis.Conductivity.Branching.EndingCoordinateTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma alignedEndingTensor_bounds {lam k J L K c C : ℝ}
    (hb : ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (finiteEndingTensor (lam/k) J L K x*ᵥv) ∧
      v ⬝ᵥ (finiteEndingTensor (lam/k) J L K x*ᵥv)≤C*(v ⬝ᵥ v))
    (x v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv) ∧
      v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  have h := hb (permutedDilation angularAxisSwap k x) (fun i => v (angularAxisSwap i))
  have hn : (fun i => v (angularAxisSwap i)) ⬝ᵥ (fun i => v (angularAxisSwap i))=v ⬝ᵥ v :=
    Equiv.sum_comp angularAxisSwap (fun i => v i*v i)
  rw [hn] at h
  have hq := permutedTensor_quadratic angularAxisSwap
    (finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k x)) v
  change v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)=_ at hq
  simpa only [hq] using h

lemma permutedDilation_angularShift (k : ℤ) (n : Fin 2 → ℤ) (x : Coord3) :
    permutedDilation angularAxisSwap (k:ℝ) (x+angularShift (2*Real.pi) n)=
      permutedDilation angularAxisSwap (k:ℝ) x+
        angularShift (2*Real.pi) ![k*n 1,k*n 0] := by
  ext i
  fin_cases i <;> simp [permutedDilation,angularAxisSwap_apply,angularShift] <;> ring

lemma alignedEndingValue_angularPeriodic (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (alignedEndingValue lam k J L K) := by
  intro n x
  dsimp only [alignedEndingValue]
  rw [permutedDilation_angularShift]
  exact finiteEndingValue_angularPeriodic _ _ _ _ _ _

lemma alignedEndingTensor_angularPeriodic (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (alignedEndingTensor lam k J L K) := by
  intro n x
  ext i j
  dsimp only [alignedEndingTensor]
  rw [permutedDilation_angularShift,finiteEndingTensor_angularPeriodic]

theorem aligned_positive_finite_ending {lam : ℝ} (hlam : 0<lam) {k : ℤ} (hk : 0<k) :
    ∃ J L K T c C : ℝ,0<J ∧ 1≤L ∧ 0<K ∧ 0<T ∧ 0<c ∧ c≤C ∧
      ContDiff ℝ 2 (alignedEndingValue lam k J L K) ∧
      AngularPeriodic (2*Real.pi) (alignedEndingValue lam k J L K) ∧
      AngularPeriodic (2*Real.pi) (alignedEndingTensor lam k J L K) ∧
      (∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv) ∧
        v ⬝ᵥ (alignedEndingTensor lam k J L K x*ᵥv)≤C*(v ⬝ᵥ v)) ∧
      (∀ x : Coord3,(k:ℝ)*x 0≤1 → alignedEndingValue lam k J L K x=exp (-lam*x 0)*cos ((k:ℝ)*x 2)) ∧
      (∀ x : Coord3,T≤x 0 → alignedEndingValue lam k J L K x=0) ∧
      (∀ x : Coord3,alignedEndingTensor lam k J L K x*ᵥPi.single 0 1=Pi.single 0 1) ∧
      ∀ (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
        (∫ x, ∑ i, (alignedEndingTensor lam k J L K x*ᵥ
          (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)) i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨J,L,K,c,C,hJ,hL,hK,hc,hcC,hb⟩ := exists_finiteEnding_parameters (div_pos hlam hkr)
  have hD := cascade_length_positive (lt_of_lt_of_le (by norm_num) hL) hK
  let T := (J+2+2*cascadeLength L K)/(k:ℝ)
  refine ⟨J,L,K,T,c,C,hJ,hL,hK,div_pos (by linarith) hkr,hc,hcC,
    alignedEndingValue_C2 hJ hL hK,alignedEndingValue_angularPeriodic _ _ _ _ _,
    alignedEndingTensor_angularPeriodic _ _ _ _ _,alignedEndingTensor_bounds hb,
    alignedEnding_initial hkr hJ,?_,alignedEndingTensor_normal _ _ _ _ _,?_⟩
  · intro x hx
    apply alignedEnding_terminal hJ hL hK
    have hh := (div_le_iff₀ hkr).mp hx
    linarith
  · intro ψ hcψ
    exact (alignedEnding_weak_equation hkr.ne' hJ hL hK ψ hcψ).2

end ScalarConductivity

end

end OAI
