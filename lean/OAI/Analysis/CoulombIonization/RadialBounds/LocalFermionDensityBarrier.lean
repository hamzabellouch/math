import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Density
import OAI.Analysis.CoulombIonization.RadialBounds.LocalDensityTraceBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoulombLT
open CoulombPauli CoulombPackets CoulombAtom
local instance : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem fermion_local_density {N : ℕ}
    (ψ : fermionL2 (V := Space) (N+1))
    (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1))
    (hw : ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ)
      (splitFermion i (u i a)) (EuclideanSpace.single a 1))
    (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ)
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*fermionDensity ψ x)^(5/3:ℝ)) ≤
      32*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2)+
      ENNReal.ofReal (4096/3:ℝ)*(∑ a : Fin 3,
        (coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
         coordinateWeightedTrace (fun _ => ψ)
           (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2))) := by
  let : MeasureTheory.IsSeparable (configMeasure N (spinSpaceMeasure (V := Space))) :=
    MeasureTheory.isSeparable_of_sigmaFinite _
  obtain ⟨κ,b,-⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space))))
  let : Countable κ := hilbertBasis_countable b
  let f := fermionFamily b ψ
  let g (a : Fin 3) := indexedFermionFamily b (fun i => u i a)
  have hg (a : Fin 3) (q : Fin (N+1) × Fin 2 × κ) :
      HasWeakDirectionalDerivative (f q) (g a q) (EuclideanSpace.single a 1) :=
    weak_derivative_smul_L2 (spinMarginal_weak_derivative (hw q.1 a) q.2.1 (b q.2.2)) _
  have hb := localized_family_lieb_thirring (fermionFamily_bessel b ψ hn ha) hg p hp
  have htrace : (∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2)) =
      ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2) := by
    rw [smoothMultiply_trace]
    exact fermionFamily_weighted b ψ _ (p.regular.continuous.pow 2).measurable
  have hgrad (a : Fin 3) :
      (∑' j, ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2)) ≤
        coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
        coordinateWeightedTrace (fun _ => ψ)
          (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2) := by
    have ht := smoothDerivative_trace_bound f (g a) p a
    rw [indexed_density_weighted b (fun i => u i a) (fun x => p.value x^2) (p.regular.continuous.pow 2).measurable,
      fermionFamily_weighted b ψ (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)
        ((p.derivative_continuous a).pow 2).measurable] at ht
    have hc : (2:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ) = 1 := by
      rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    simpa only [← mul_assoc,hc,one_mul,coordinateWeightedTrace] using ht
  rw [htrace] at hb
  have hgb := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hgrad a)
  have hc : (2:ℝ≥0∞)^(5/3:ℝ) ≤ 4 := by
    calc _ ≤ (2:ℝ≥0∞)^(2:ℝ) :=
           ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ = _ := by norm_num
  calc
    _ = ∫⁻ x, (2*(ENNReal.ofReal (p.value x^2)*infiniteDensity f x))^(5/3:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [fermionDensity_eq_family b ψ] with x hx
      rw [hx]
      congr 1
      ac_rfl
    _ ≤ ∫⁻ x, 4*(ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ) := by
      apply lintegral_mono
      intro x
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 5/3)]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4*(∫⁻ x, (ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ)) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4*(16*(ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j,
          ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 4*(16*(ENNReal.ofReal (1/2:ℝ)*coordinateWeightedTrace (fun _ => ψ) (fun x => p.value x^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a : Fin 3,
          (coordinateWeightedTrace (fun i => u i a) (fun x => p.value x^2)+
           coordinateWeightedTrace (fun _ => ψ)
             (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)))) := by
      gcongr
    _ = _ := by
      simp only [mul_add,← mul_assoc]
      congr 1
      · congr 1
        norm_num only [Nat.reduceMul]
        rw [show (64:ℝ≥0∞)=ENNReal.ofReal (64:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 64)]
        norm_num
      · congr 1
        rw [show (4:ℝ≥0∞)=ENNReal.ofReal (4:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num

end CoulombLT

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

lemma square_weight_integrable {L : ℕ} {v : Configuration L → ℂ}
    (hv : MemLp v 2) (r : Space → ℝ) (hr : Continuous r)
    (hb : ∃ C, ∀ x, |r x| ≤ C) (i : Fin L) :
    Integrable (fun x : Configuration L => r (x i)^2*‖v x‖^2) := by
  have hh := (memLp_bounded_mul (hr.comp (continuous_apply i))
    (by obtain ⟨C,hC⟩ := hb; exact ⟨C,fun x => hC (x i)⟩) hv).norm.integrable_sq
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,Function.comp_apply] using hh

lemma coordinateWeightedTrace_form {N : ℕ}
    (φ : Fin (N+1) → FormVector (N+1)) (hφ : ∀ i s, MemLp ((φ i).value s) 2)
    (w : Space → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hI : ∀ i s, Integrable (fun x : Configuration (N+1) => w (x i)*‖(φ i).value s x‖^2)) :
    coordinateWeightedTrace (fun i => toMany (φ i) (hφ i)) w =
      ENNReal.ofReal (∑ i : Fin (N+1), ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), w (x i)*‖(φ i).value s x‖^2) := by
  unfold coordinateWeightedTrace
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun s _ => integral_nonneg (fun x => mul_nonneg (hw0 _) (sq_nonneg _))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [toMany_coordinate_lintegral (φ i) (hφ i) i w hw,
    ENNReal.ofReal_sum_of_nonneg (fun s _ => integral_nonneg
      (fun x => mul_nonneg (hw0 _) (sq_nonneg _)))]
  apply Finset.sum_congr rfl
  intro s _
  rw [ofReal_integral_eq_lintegral_ofReal (hI i s)
    (ae_of_all _ (fun x => mul_nonneg (hw0 _) (sq_nonneg _)))]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_mul (hw0 _)).symm

lemma coordinateWeightedTrace_square_form {N : ℕ}
    (φ : Fin (N+1) → FormVector (N+1)) (hφ : ∀ i s, MemLp ((φ i).value s) 2)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun i => toMany (φ i) (hφ i)) (fun x => r x^2) =
      ENNReal.ofReal (∑ i : Fin (N+1), ∑ s : Spins (N+1),
        ∫ x : Configuration (N+1), r (x i)^2*‖(φ i).value s x‖^2) :=
  coordinateWeightedTrace_form φ hφ _ (hr.pow 2).measurable (fun _ => sq_nonneg _)
    (fun i s => square_weight_integrable (hφ i s) r hr hb i)

lemma coordinateWeightedTrace_square_mass {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : ∀ s, MemLp (ψ.value s) 2)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun _ : Fin (N+1) => toMany ψ hψ) (fun x => r x^2) =
      ENNReal.ofReal (weightedParticleCount ψ (fun x => r x^2)) := by
  rw [coordinateWeightedTrace_square_form (fun _ => ψ) (fun _ => hψ) r hr hb]
  congr 1
  exact Finset.sum_comm

lemma coordinateWeightedTrace_square_gradient {N : ℕ} (ψ : FormVector (N+1))
    (hψ : FormAdmissible ψ) (a : Fin 3)
    (r : Space → ℝ) (hr : Continuous r) (hb : ∃ C, ∀ x, |r x| ≤ C) :
    coordinateWeightedTrace (fun i => gradientMany ψ hψ i a) (fun x => r x^2) =
      ENNReal.ofReal (∑ s : Spins (N+1), ∑ i : Fin (N+1),
        ∫ x, r (x i)^2*‖ψ.gradient s i a x‖^2) := by
  have he := coordinateWeightedTrace_square_form
    (fun i => gradientVector ψ i a) (fun i s => hψ.2.1 s i a) r hr hb
  exact he.trans (congrArg ENNReal.ofReal Finset.sum_comm)

end CoulombAtom.Pauli

end

end OAI
