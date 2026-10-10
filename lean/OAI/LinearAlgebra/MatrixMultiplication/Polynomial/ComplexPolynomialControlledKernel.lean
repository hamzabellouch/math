import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialLocalConstruction
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace PolynomialControlledKernel

open Tensor LocalMaps PolynomialLocalConstruction
open scoped BigOperators

section ScalarCoefficients

variable {F : Type*} [Field F]

theorem expanded_mul_coeff_window (P Q : Polynomial F) (d k : ℕ) (a : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (j : ℕ) (hj : j ≤ d * (k + 1) + k) :
    (Polynomial.expand F (k + 1) P * Q).coeff j =
      if d * (k + 1) ≤ j then a * Q.coeff (j - d * (k + 1)) else 0 := by
  obtain ⟨P₀, hP₀⟩ := Polynomial.X_pow_dvd_iff.mpr hP
  have hconstant : P₀.coeff 0 = a := by
    rw [hP₀] at hPa
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using hPa
  have hfactor : Polynomial.expand F (k + 1) P * Q =
      Polynomial.X ^ (d * (k + 1)) *
        (Q * Polynomial.expand F (k + 1) P₀) := by
    rw [hP₀, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul]
    rw [Nat.mul_comm (k + 1) d]
    ring
  rw [hfactor, Polynomial.coeff_X_pow_mul']
  split_ifs with hdj
  · have hsmall : j - d * (k + 1) ≤ k := by omega
    rw [Tensor.coeff_mul_expand_eq_constant Q P₀ a hconstant k _ hsmall,
      Polynomial.coeff_mul_C, mul_comm]
  · rfl

theorem expanded_mul_vanishes_of_leading_support (P Q : Polynomial F)
    (d k : ℕ) (a : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (hQ : a ≠ 0 → ∀ j, j < k → Q.coeff j = 0)
    (j : ℕ) (hj : j < d * (k + 1) + k) :
    (Polynomial.expand F (k + 1) P * Q).coeff j = 0 := by
  rw [expanded_mul_coeff_window P Q d k a hP hPa j (Nat.le_of_lt hj)]
  split_ifs with hdj
  · by_cases ha : a = 0
    · simp [ha]
    · rw [hQ ha _ (by omega), mul_zero]
  · rfl

theorem expanded_mul_leading_of_leading_support (P Q : Polynomial F)
    (d k : ℕ) (a b : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (hQb : a ≠ 0 → Q.coeff k = b) :
    (Polynomial.expand F (k + 1) P * Q).coeff (d * (k + 1) + k) = a * b := by
  rw [expanded_mul_coeff_window P Q d k a hP hPa _ le_rfl]
  simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  by_cases ha : a = 0
  · simp [ha]
  · rw [hQb ha]

end ScalarCoefficients

abbrev Output (Prefix New OldCoord NewCoord : Type*) :=
  (Prefix × OldCoord) × (New × NewCoord)

section ActualMatrices

variable {X Y Z Prefix New PX PY PZ NX NY NZ AP BP CP AS BS CS : Type*}
variable [Fintype AP] [Fintype BP] [Fintype CP]
variable [Fintype AS] [Fintype BS] [Fintype CS]

def expandMap {O A : Type*} (factor : ℕ) (M : X → O → A → Polynomial ℂ) :
    X → O → A → Polynomial ℂ :=
  fun x output input => Polynomial.expand ℂ factor (M x output input)

def controlledMap (kStep : ℕ)
    (previous : X → (Prefix × PX) → AP → Polynomial ℂ)
    (step : Prefix → X → (New × NX) → AS → Polynomial ℂ) :
    X → Output Prefix New PX NX → (AP × AS) → Polynomial ℂ :=
  fun x output input =>
    Polynomial.expand ℂ (kStep + 1) (previous x output.1 input.1) *
      step output.1.1 x output.2 input.2

omit [Fintype AP] [Fintype AS] in
theorem controlledMap_degree (kStep dPrevious dStep : ℕ)
    (previous : X → (Prefix × PX) → AP → Polynomial ℂ)
    (step : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (hp : ∀ x output input, (previous x output input).degree ≤ dPrevious)
    (hs : ∀ prior x output input, (step prior x output input).degree ≤ dStep)
    (x : X) (output : Output Prefix New PX NX) (input : AP × AS) :
    (controlledMap kStep previous step x output input).degree ≤
      dPrevious * (kStep + 1) + dStep := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_mul_le_of_le
  · rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (kStep + 1)
      (Polynomial.natDegree_le_of_degree_le (hp x output.1 input.1))
  · exact Polynomial.natDegree_le_of_degree_le
      (hs output.1.1 x output.2 input.2)

theorem kernel_expandMap (factor : ℕ) (auxiliary : Tensor ℂ AP BP CP)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (x : X × (Prefix × PX)) (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) :
    kernel auxiliary (expandMap factor MX) (expandMap factor MY) (expandMap factor MZ)
        x y z = Polynomial.expand ℂ factor (kernel auxiliary MX MY MZ x y z) := by
  simp only [kernel, fiberTransform, expandMap, map_sum, map_mul, Polynomial.expand_C]

def mixedStageKernel (auxiliary : Tensor ℂ AS BS CS)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × Output Prefix New PX NX)
      (Y × Output Prefix New PY NY) (Z × Output Prefix New PZ NZ) :=
  fun x y z => kernel auxiliary (SX x.2.1.1) (SY y.2.1.1) (SZ z.2.1.1)
    (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2)

def controlledKernel (kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × Output Prefix New PX NX)
      (Y × Output Prefix New PY NY) (Z × Output Prefix New PZ NZ) :=
  kernel (Tensor.product previousAuxiliary stepAuxiliary)
    (controlledMap kStep MX SX) (controlledMap kStep MY SY) (controlledMap kStep MZ SZ)

theorem controlledKernel_factor (kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    (x : X × Output Prefix New PX NX) (y : Y × Output Prefix New PY NY)
    (z : Z × Output Prefix New PZ NZ) :
    controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z =
      Polynomial.expand ℂ (kStep + 1)
        (kernel previousAuxiliary MX MY MZ (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1)) *
      mixedStageKernel stepAuxiliary SX SY SZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.restrict_product (expandMap (kStep + 1) MX x.1)
      (expandMap (kStep + 1) MY y.1) (expandMap (kStep + 1) MZ z.1)
      (SX x.2.1.1 x.1) (SY y.2.1.1 y.1) (SZ z.2.1.1 z.1)
      (fun a b c => Polynomial.C (previousAuxiliary a b c))
      (fun a b c => Polynomial.C (stepAuxiliary a b c))) x.2) y.2) z.2
  have hproduct :
      controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z =
        kernel previousAuxiliary (expandMap (kStep + 1) MX)
          (expandMap (kStep + 1) MY) (expandMap (kStep + 1) MZ)
          (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
        mixedStageKernel stepAuxiliary SX SY SZ x y z := by
    simpa only [controlledKernel, kernel, fiberTransform, Tensor.restrict, Tensor.product,
      controlledMap, expandMap, mixedStageKernel, map_mul] using h
  rw [hproduct, kernel_expandMap]

theorem controlledKernel_substitution (kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    (original : Tensor ℂ X Y Z) :
    fiberTransform (controlledMap kStep MX SX) (controlledMap kStep MY SY)
        (controlledMap kStep MZ SZ)
        (fun x y z => Polynomial.C
          (Tensor.product original (Tensor.product previousAuxiliary stepAuxiliary) x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ) := by
  have h := fiberTransform_originalScale (controlledMap kStep MX SX)
    (controlledMap kStep MY SY) (controlledMap kStep MZ SZ)
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (Tensor.product previousAuxiliary stepAuxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C
        (Tensor.product original (Tensor.product previousAuxiliary stepAuxiliary) x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C
            (Tensor.product previousAuxiliary stepAuxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [controlledKernel, kernel] using h

def controlledLeading
    (previous : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ)))
    (step : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ))) :
    Tensor ℂ (X × Output Prefix New PX NX) (Y × Output Prefix New PY NY)
      (Z × Output Prefix New PZ NZ) :=
  fun x y z => previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
    step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2)

theorem controlledKernel_coefficients (dPrevious kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    (previous : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ)))
    (step : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ)))
    (support : X → Y → Z → Prop) (eligible : Prefix → X → Y → Z → Prop)
    (hprevious_low : ∀ x y z, support x.1 y.1 z.1 → ∀ j, j < dPrevious →
      (kernel previousAuxiliary MX MY MZ x y z).coeff j = 0)
    (hprevious_leading : ∀ x y z, support x.1 y.1 z.1 →
      (kernel previousAuxiliary MX MY MZ x y z).coeff dPrevious = previous x y z)
    (hprevious_support : ∀ x y z, support x.1 y.1 z.1 → previous x y z ≠ 0 →
      x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible x.2.1 x.1 y.1 z.1)
    (hstep_low : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
      ∀ j, j < kStep →
      (kernel stepAuxiliary (SX prior) (SY prior) (SZ prior) x y z).coeff j = 0)
    (hstep_leading : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
      (kernel stepAuxiliary (SX prior) (SY prior) (SZ prior) x y z).coeff kStep =
        step prior x y z) :
    (∀ x y z, support x.1 y.1 z.1 → ∀ j, j < dPrevious * (kStep + 1) + kStep →
      (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z).coeff j = 0) ∧
    (∀ x y z, support x.1 y.1 z.1 →
      (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z).coeff
        (dPrevious * (kStep + 1) + kStep) = controlledLeading previous step x y z) := by
  have hselected : ∀ (x : X × Output Prefix New PX NX)
      (y : Y × Output Prefix New PY NY) (z : Z × Output Prefix New PZ NZ),
      support x.1 y.1 z.1 →
      previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) ≠ 0 →
      (∀ j, j < kStep → (mixedStageKernel stepAuxiliary SX SY SZ x y z).coeff j = 0) ∧
        (mixedStageKernel stepAuxiliary SX SY SZ x y z).coeff kStep =
          step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) := by
    intro x y z hs hn
    obtain ⟨hxy, hxz, he⟩ :=
      hprevious_support (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) hs hn
    have hy : y.2.1.1 = x.2.1.1 := hxy.symm
    have hz : z.2.1.1 = x.2.1.1 := hxz.symm
    constructor
    · intro j hj
      simpa only [mixedStageKernel, hy, hz] using
        hstep_low x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) he j hj
    · simpa only [mixedStageKernel, hy, hz] using
        hstep_leading x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) he
  constructor
  · intro x y z hs j hj
    rw [controlledKernel_factor]
    exact expanded_mul_vanishes_of_leading_support _ _ dPrevious kStep
      (previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1))
      (hprevious_low _ _ _ hs) (hprevious_leading _ _ _ hs)
      (fun hn => (hselected x y z hs hn).1) j hj
  · intro x y z hs
    rw [controlledKernel_factor]
    exact expanded_mul_leading_of_leading_support _ _ dPrevious kStep
      (previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1))
      (step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2))
      (hprevious_low _ _ _ hs) (hprevious_leading _ _ _ hs)
      (fun hn => (hselected x y z hs hn).2)

theorem controlledKernel_rank [Fintype X] [Fintype Y] [Fintype Z]
    (kStep : ℕ) (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    {rPrevious rStep : ℕ} (hp : RankAtMost previousAuxiliary rPrevious)
    (hs : RankAtMost stepAuxiliary rStep) :
    RankAtMost (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ)
      (rPrevious * rStep) := by
  classical
  have hsource := ((hp.product hs).map Polynomial.C).pullback
    (fun x : X × (AP × AS) => x.2) (fun y : Y × (BP × BS) => y.2)
    (fun z : Z × (CP × CS) => z.2)
  unfold controlledKernel kernel
  rw [fiberTransform_eq_restrict]
  exact hsource.restrict _ _ _

end ActualMatrices

end PolynomialControlledKernel
end MatrixMultiplication.Foundation

end

end OAI
