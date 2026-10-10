import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
def transverseSum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space) : Space → Space :=
  fun x => ∑ i, f i (P x) • v i

theorem transverseSum_hasFDerivAt {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (x : Space) (hf : ∀ i, DifferentiableAt ℝ (f i) (P x)) :
    HasFDerivAt (transverseSum P f v)
      (∑ i, ((fderiv ℝ (f i) (P x)).comp P).smulRight (v i)) x := by
  apply HasFDerivAt.fun_sum
  intro i _
  exact ((hf i).hasFDerivAt.comp x P.hasFDerivAt).smul_const (v i)

theorem transverseSum_fderiv_apply {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (x y : Space) (hf : ∀ i, DifferentiableAt ℝ (f i) (P x)) :
    fderiv ℝ (transverseSum P f v) x y =
      ∑ i, fderiv ℝ (f i) (P x) (P y) • v i := by
  rw [(transverseSum_hasFDerivAt P f v x hf).fderiv]
  simp

theorem sum_coordinates_basis (v : Space) : ∑ j, v j • basis j = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

theorem coordinate_trace (ℓ : Space →L[ℝ] ℝ) (v : Space) :
    ∑ j, ℓ (basis j) * v j = ℓ v := by
  calc
    ∑ j, ℓ (basis j) * v j = ∑ j, ℓ (v j • basis j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_smul, smul_eq_mul, mul_comm]
    _ = ℓ (∑ j, v j • basis j) := (map_sum ℓ _ _).symm
    _ = ℓ v := congrArg ℓ (sum_coordinates_basis v)

theorem transverseSum_divergence {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0)
    (x : Space) (hf : ∀ i, DifferentiableAt ℝ (f i) (P x)) :
    divergence (transverseSum P f v) x = 0 := by
  unfold divergence derivative
  simp_rw [transverseSum_fderiv_apply P f v x _ hf,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have heq := coordinate_trace ((fderiv ℝ (f i) (P x)).comp P) (v i)
  simpa only [ContinuousLinearMap.comp_apply, hv i, map_zero] using heq

theorem transverseSum_advection {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0)
    (x : Space) (hf : ∀ i, DifferentiableAt ℝ (f i) (P x)) :
    advection (transverseSum P f v) x = 0 := by
  have hP : P (transverseSum P f v x) = 0 := by
    simp [transverseSum, map_sum, hv]
  unfold advection
  rw [transverseSum_fderiv_apply P f v x _ hf]
  simp only [hP, map_zero, zero_smul, Finset.sum_const_zero]

def selectTwo (j k : Fin 3) : Space →L[ℝ] Plane :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj j, ContinuousLinearMap.proj k]

theorem selectTwo_basis {j k l : Fin 3} (hj : l ≠ j) (hk : l ≠ k) :
    selectTwo j k (basis l) = 0 := by
  ext a
  fin_cases a <;> simp [selectTwo, basis, Ne.symm hj, Ne.symm hk]

def sevenFields {n : ℕ} (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ) :
    Fin 7 → Space → Space :=
  letI := neZeroTwo
  letI := neZeroThree
  ![transverseSum (selectTwo 0 1) (fun i X => (z i - z₀) * Am i X) (fun _ => basis 2),
    transverseSum (selectTwo 0 2) (fun i X => (-lam i) * Z i (X 1) * gx i (X 0))
      (fun _ => basis 1),
    transverseSum (selectTwo 1 2) (fun i X => ((lam i)⁻¹ - 1) *
      Z i (X 1) * gy i (X 0)) (fun _ => basis 0),
    transverseSum (selectTwo 0 2) (fun i X => Z i (X 1) * gx i (X 0)) (fun _ => basis 1),
    transverseSum (selectTwo 1 2) (fun i X => (lam i - 1) * Z i (X 1) * gy i (X 0))
      (fun _ => basis 0),
    transverseSum (ContinuousLinearMap.proj 2) Z (fun i => atHeight (q i - p i) 0),
    transverseSum (selectTwo 0 1) (fun i X => (z₀ - z i) * Ap i X) (fun _ => basis 2)]

theorem sevenFields_divergence_advection {n : ℕ}
    (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ)
    (hAm : ∀ i, Differentiable ℝ (Am i)) (hAp : ∀ i, Differentiable ℝ (Ap i))
    (hZ : ∀ i, Differentiable ℝ (Z i)) (hgx : ∀ i, Differentiable ℝ (gx i))
    (hgy : ∀ i, Differentiable ℝ (gy i)) :
    ∀ j x, divergence (sevenFields p q lam z z₀ Am Ap Z gx gy j) x = 0 ∧
      advection (sevenFields p q lam z z₀ Am Ap Z gx gy j) x = 0 := by
  intro j x
  have hx : Differentiable ℝ (fun X : Plane => X 0) := differentiable_apply 0
  have hy : Differentiable ℝ (fun X : Plane => X 1) := differentiable_apply 1
  have h01 (i : Fin n) : selectTwo 0 1 (basis 2) = 0 := selectTwo_basis (by decide) (by decide)
  have h02 (i : Fin n) : selectTwo 0 2 (basis 1) = 0 := selectTwo_basis (by decide) (by decide)
  have h12 (i : Fin n) : selectTwo 1 2 (basis 0) = 0 := selectTwo_basis (by decide) (by decide)
  have hz (i : Fin n) : (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ)
      (atHeight (q i - p i) 0) = 0 := rfl
  have both {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (P : Space →L[ℝ] E) (f : Fin n → E → ℝ) (v : Fin n → Space)
      (hv : ∀ i, P (v i) = 0) (hf : ∀ i, Differentiable ℝ (f i)) :
      divergence (transverseSum P f v) x = 0 ∧ advection (transverseSum P f v) x = 0 :=
    ⟨transverseSum_divergence P f v hv x (fun i => hf i _),
      transverseSum_advection P f v hv x (fun i => hf i _)⟩
  fin_cases j <;> simp [sevenFields]
  · apply both _ _ _ h01
    intro i
    exact (hAm i).const_mul _
  · apply both _ _ _ h02
    intro i
    exact ((((hZ i).comp hy).const_mul (lam i)).mul ((hgx i).comp hx)).neg
  · apply both _ _ _ h12
    intro i
    exact (((hZ i).comp hy).const_mul _).mul ((hgy i).comp hx)
  · apply both _ _ _ h02
    intro i
    exact ((hZ i).comp hy).mul ((hgx i).comp hx)
  · apply both _ _ _ h12
    intro i
    exact (((hZ i).comp hy).const_mul _).mul ((hgy i).comp hx)
  · exact both _ _ _ hz hZ
  · apply both _ _ _ h01
    intro i
    exact (hAp i).const_mul _

end ShearFlows

end

end OAI
