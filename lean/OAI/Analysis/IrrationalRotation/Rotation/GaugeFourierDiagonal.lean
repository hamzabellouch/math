import OAI.Analysis.IrrationalRotation.Rotation.DiagonalGauge
import OAI.Analysis.IrrationalRotation.Operators.StrongOperatorIntegral
import OAI.Analysis.IrrationalRotation.Analysis.FejerKernel
import OAI.Analysis.IrrationalRotation.Operators.LpOperatorExt

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.DiagonalGauge

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def coordinate (k : ℤ) : Lp Fiber 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).compLpL 2 μ

def inclusion (j : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp Fiber 2 μ :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 μ

theorem coordinate_ae (k : ℤ) (v : Lp Fiber 2 μ) :
    coordinate μ k v =ᵐ[μ] fun x => v x k :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).coeFn_compLpL v

theorem inclusion_ae (j : ℤ) (v : Lp ℂ 2 μ) :
    inclusion μ j v =ᵐ[μ] fun x => lp.single 2 j (v x) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).coeFn_compLpL v

theorem coordinate_ext {v w : Lp Fiber 2 μ}
    (h : ∀ k : ℤ, coordinate μ k v = coordinate μ k w) : v = w := by
  have hc (k : ℤ) : ∀ᵐ x ∂μ, v x k = w x k := by
    apply (coordinate_ae μ k v).symm.trans
    rw [h k]
    exact coordinate_ae μ k w
  apply Lp.ext
  filter_upwards [MeasureTheory.ae_all_iff.mpr hc] with x hx
  exact lp.ext (funext hx)

theorem inclusion_indicatorConstLp (j : ℤ) (s : Set X)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℂ) :
    inclusion μ j (indicatorConstLp 2 hs hμs c) =
      indicatorConstLp 2 hs hμs (lp.single 2 j c : Fiber) := by
  apply Lp.ext
  filter_upwards [inclusion_ae μ j (indicatorConstLp 2 hs hμs c),
    (indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := c)),
    (indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs)
      (c := (lp.single 2 j c : Fiber)))] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

theorem operator_ext_inclusion {A B : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ}
    (h : ∀ j : ℤ, ∀ v : Lp ℂ 2 μ, A (inclusion μ j v) = B (inclusion μ j v)) :
    A = B := by
  apply Fields.lp_operator_ext_basis_indicator
    (default : HilbertBasis ℤ ℂ Fiber) (by norm_num) A B
  intro j s hs hμs
  have hb : (default : HilbertBasis ℤ ℂ Fiber) j =
      (lp.single 2 j (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) j).symm
  rw [hb, ← inclusion_indicatorConstLp]
  exact h j _

theorem operator_ext_entries {A B : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ}
    (h : ∀ k j : ℤ, ∀ v : Lp ℂ 2 μ,
      coordinate μ k (A (inclusion μ j v)) = coordinate μ k (B (inclusion μ j v))) :
    A = B :=
  operator_ext_inclusion μ (fun j v => coordinate_ext μ (fun k => h k j v))

theorem coordinate_fieldOperator (k : ℤ) (t : Circle) (v : Lp Fiber 2 μ) :
    coordinate μ k (fieldOperator μ t v) = fourier k t • coordinate μ k v := by
  apply Lp.ext
  filter_upwards [coordinate_ae μ k (fieldOperator μ t v),
    fieldOperator_ae μ t v, coordinate_ae μ k v,
    Lp.coeFn_smul (fourier k t) (coordinate μ k v)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, fiberOperator_apply, h₄]
  change fourier k t * v x k = fourier k t * coordinate μ k v x
  rw [h₃]

theorem fieldOperator_inclusion (j : ℤ) (t : Circle) (v : Lp ℂ 2 μ) :
    fieldOperator μ t (inclusion μ j v) = fourier j t • inclusion μ j v := by
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ t (inclusion μ j v), inclusion_ae μ j v,
    Lp.coeFn_smul (fourier j t) (inclusion μ j v)] with x h₁ h₂ h₃
  rw [h₁, h₃]
  change fiberOperator t (inclusion μ j v x) = fourier j t • inclusion μ j v x
  rw [h₂]
  apply lp.ext
  funext k
  change fourier k t * (lp.single 2 j (v x) : Fiber) k =
    fourier j t * (lp.single 2 j (v x) : Fiber) k
  by_cases h : j = k
  · subst k
    rfl
  · simp [lp.single_apply, h]

theorem fourier_neg_argument (j : ℤ) (t : Circle) :
    fourier j (-t) = fourier (-j) t := by
  simp only [fourier_apply, smul_neg, neg_smul]

theorem coordinate_conjugate_inclusion
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (k j : ℤ) (t : Circle)
    (v : Lp ℂ 2 μ) :
    coordinate μ k (conjugate μ A t (inclusion μ j v)) =
      fourier (k - j) t • coordinate μ k (A (inclusion μ j v)) := by
  change coordinate μ k
    (fieldOperator μ t (A (fieldOperator μ (-t) (inclusion μ j v)))) = _
  rw [fieldOperator_inclusion]
  simp only [map_smul]
  rw [coordinate_fieldOperator, fourier_neg_argument, smul_smul]
  rw [mul_comm, ← fourier_add]
  rfl

variable [IsFiniteMeasure μ]

theorem integrable_fourier_conjugate_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (v : Lp Fiber 2 μ) :
    Integrable (fun t : Circle => fourier (-r) t • conjugate μ A t v)
      AddCircle.haarAddCircle :=
  ((fourier (-r)).continuous.smul (continuous_conjugate_apply μ A v)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [IsFiniteMeasure μ] in
theorem norm_fourier_conjugate_le
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (t : Circle) :
    ‖fourier (-r) t • conjugate μ A t‖ ≤ ‖A‖ := by
  rw [norm_smul, show ‖fourier (-r) t‖ = 1 from Circle.norm_coe _, one_mul]
  exact norm_conjugate_le μ A t

def fourierOperator (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  StrongOperatorIntegral.operator
    (fun t : Circle => fourier (-r) t • conjugate μ A t)
    (integrable_fourier_conjugate_apply μ A r) ‖A‖
    (Filter.Eventually.of_forall (norm_fourier_conjugate_le μ A r))

@[simp] theorem fourierOperator_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (v : Lp Fiber 2 μ) :
    fourierOperator μ A r v =
      ∫ t : Circle, fourier (-r) t • conjugate μ A t v ∂AddCircle.haarAddCircle := rfl

theorem norm_fourierOperator_le
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) :
    ‖fourierOperator μ A r‖ ≤ ‖A‖ :=
  StrongOperatorIntegral.norm_operator_le _ _ _ (norm_nonneg A) _

theorem coordinate_fourierOperator_inclusion
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r k j : ℤ) (v : Lp ℂ 2 μ) :
    coordinate μ k (fourierOperator μ A r (inclusion μ j v)) =
      if k - j = r then coordinate μ k (A (inclusion μ j v)) else 0 := by
  rw [fourierOperator_apply,
    ← (coordinate μ k).integral_comp_comm (integrable_fourier_conjugate_apply μ A r _)]
  simp_rw [map_smul, coordinate_conjugate_inclusion, smul_smul, ← fourier_add]
  rw [integral_smul_const, Fejer.integral_fourier]
  have heq : -r + (k - j) = 0 ↔ k - j = r := by omega
  simp only [heq]
  split_ifs <;> simp

end Invariant233.DiagonalGauge

end

end OAI
