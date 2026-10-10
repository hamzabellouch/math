import OAI.InformationTheory.DimensionTen.ChoiTransfer
import OAI.InformationTheory.DimensionTen.StateDensity
import OAI.InformationTheory.DimensionTen.FiniteReadout

namespace OAI

/-! Dimension-ten key bounds for finite total terminal readouts and their trace-norm closure. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped ComplexOrder Kronecker ENNReal

namespace DimensionTen
universe u

lemma rho_inClass : ZeroKey.InClass rho := by
  refine ⟨rho_density,10,10,phiOneSharp,phiTwoLinear,
    (fun i => ((Real.sqrt (trace compositeChoi).re)⁻¹ : ℝ) * omega 10 i),
    phiOneSharp_pptType,phiTwo_pptType,?_⟩
  have hc : ((((Real.sqrt (trace compositeChoi).re)⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (trace compositeChoi).re)⁻¹ : ℝ) : ℂ)) = (trace compositeChoi)⁻¹ := by
    have hl : 0 ≤ (trace compositeChoi).re :=
      (RCLike.nonneg_iff.mp compositeChoi_trace_nonneg).1
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hl,
      Complex.ofReal_inv, compositeChoi_trace_re]
  have ho : ZeroKey.outer
      (fun i => ((Real.sqrt (trace compositeChoi).re)⁻¹ : ℝ) * omega 10 i)
      (fun i => ((Real.sqrt (trace compositeChoi).re)⁻¹ : ℝ) * omega 10 i) =
        (trace compositeChoi)⁻¹ • ZeroKey.outer (omega 10) (omega 10) := by
    ext i j
    simp only [ZeroKey.outer, star_mul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_apply, smul_eq_mul]
    rw [← hc]
    ring
  rw [ho, ZeroKey.tensorMap_smul, compositeChoi_transfer]
  rfl

def SecretBitSeparation {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R) : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (O M : Type u) [MeasurableSpace O] [MeasurableSpace M]
    [StandardBorelSpace O] [Nonempty O] [StandardBorelSpace M] [Nonempty M]
    (d : ZeroKey.Discussion O M) (A B : ℕ → Type u)
    [∀ k, AddCommGroup (A k)] [∀ k, Module ℂ (A k)] [∀ k, One (A k)] [∀ k, LE (A k)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module ℂ (B k)] [∀ k, One (B k)] [∀ k, LE (B k)]
    (TA TB CA CB : Type u)
    [AddCommGroup TA] [Module ℂ TA] [One TA] [LE TA]
    [AddCommGroup TB] [Module ℂ TB] [One TB] [LE TB]
    [AddCommGroup CA] [Module ℂ CA] [One CA] [LE CA]
    [AddCommGroup CB] [Module ℂ CB] [One CB] [LE CB]
    (p : ZeroKey.BitProtocol (ι := Fin (ZeroKey.copyDim a (n-1)))
      (η := Fin (ZeroKey.copyDim b (n-1))) d A B TA TB CA CB)
    (e : ℕ) (P : Matrix
      (Fin (ZeroKey.copyDim a (n-1)) × Fin (ZeroKey.copyDim b (n-1))) (Fin e) ℂ)
    (hP : P * Pᴴ = ZeroKey.positiveCopies R (n-1))
    (sigma : ZeroKey.PositiveMatrixMeasure (ℕ → M) (Fin e)),
    (trace (sigma.value Set.univ)).re = 1 →
      (1/5 ≤ p.purifiedSecretBitError (ZeroKey.positiveCopies R (n-1))
        (hR.positiveCopies (n-1)) P hP sigma ∧
       1/10 ≤ p.purifiedSecretBitError (ZeroKey.positiveCopies R (n-1))
        (hR.positiveCopies (n-1)) P hP sigma / 2)

def CompletedBitSeparation {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R) : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ p : ZeroKey.CompletedKeyTrial.{u} (ZeroKey.positiveCopies R (n-1))
      (hR.positiveCopies (n-1)) 1,
      1/5 ≤ p.error ∧ 1/10 ≤ p.error / 2

lemma secretBitSeparation_of_inClass {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R)
    (hc : ZeroKey.InClass R) : SecretBitSeparation.{u} R hR := by
  intro n hn O M _ _ _ _ _ _ d A B _ _ _ _ _ _ _ _ TA TB CA CB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p e P hP sigma hs
  have hg := ZeroKey.class_uniformProtocolGap R hR hc (n-1) O M d A B TA TB CA CB p e P hP sigma hs
  change 1 / 5 ≤ p.purifiedSecretBitError (ZeroKey.positiveCopies R (n-1))
    (hR.positiveCopies (n-1)) P hP sigma at hg
  exact ⟨hg, by linarith⟩

lemma completedBitSeparation_of_inClass {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R)
    (hc : ZeroKey.InClass R) : CompletedBitSeparation.{u} R hR := by
  intro n hn p
  have hg := ZeroKey.class_uniformCompletedGap R hR hc (n-1) 1 (by decide) p
  exact ⟨hg, by linarith⟩

theorem main_state :
    ZeroKey.Density rho ∧
    ¬ ZeroKey.Separable rho ∧
    (∀ u v : Fin 10 → ℂ,
      productVector u v ∈ Set.range (fun w => rho *ᵥ w) → productVector u v = 0) ∧
    distillableSecretKey.{u} rho rho_density = 0 ∧
    SecretBitSeparation.{u} rho rho_density ∧
    CompletedBitSeparation.{u} rho rho_density := by
  exact ⟨rho_density, rho_entangled, rho_range_contains_no_nonzero_product,
    distillableSecretKey_zero_of_inClass rho rho_density rho_inClass,
    secretBitSeparation_of_inClass rho rho_density rho_inClass,
    completedBitSeparation_of_inClass rho rho_density rho_inClass⟩

end DimensionTen

end

end OAI
