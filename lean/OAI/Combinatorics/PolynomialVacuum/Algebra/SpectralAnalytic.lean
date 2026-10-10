import OAI.Combinatorics.PolynomialVacuum.Algebra.InhomogeneousRow
import OAI.Combinatorics.PolynomialVacuum.Pairing.TransferMatrix

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical
open scoped Topology

noncomputable def extendData (N : ℕ) (X : Fin N → ℂ) : ℕ → ℂ :=
  fun j=>if h : j<N then X ⟨j,h⟩ else 1
@[simp] theorem extendData_fin (N : ℕ) (X : Fin N → ℂ) (j : Fin N) : extendData N X j=X j := by
  simp [extendData,j.isLt]
@[simp] theorem extendData_one (N : ℕ) : extendData N (fun _=>1)=fun _=>1 := by
  funext j; simp [extendData]

theorem analytic_extendData (N j : ℕ) (X : Fin N → ℂ) : AnalyticAt ℂ (fun Y=>extendData N Y j) X := by
  unfold extendData
  split_ifs with h
  · exact (ContinuousLinearMap.proj (⟨j,h⟩ : Fin N) : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt X
  · exact analyticAt_const

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {u : E}

theorem analytic_exchangeNumerator (c : ℂ) (f : E → ℂ) (hf : AnalyticAt ℂ f u) (p q : Pair) :
    AnalyticAt ℂ (fun x=>exchangeNumerator c (f x) p q) u := by
  simp only [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

theorem analytic_exchangeDenominator (c : ℂ) (f : E → ℂ) (hf : AnalyticAt ℂ f u) :
    AnalyticAt ℂ (fun x=>exchangeDenominator c (f x)) u := by
  unfold exchangeDenominator
  fun_prop

theorem analytic_trainDenominator (N k : ℕ) (c : ℂ) (X : E → ℕ → ℂ)
    (hX : ∀ j,AnalyticAt ℂ (fun x=>X x j) u) :
    AnalyticAt ℂ (fun x=>trainDenominator c (X x) k N) u := by
  induction N generalizing k with
  | zero => exact analyticAt_const
  | succ N ih => exact (ih (k+1)).mul (analytic_exchangeDenominator c _ (hX k))

theorem analytic_rowKernel (N : ℕ) (c : ℂ) (X : E → ℕ → ℂ)
    (hX : ∀ j,AnalyticAt ℂ (fun x=>X x j) u) (out inp : Fin N → Spin) (a b : Spin) :
    AnalyticAt ℂ (fun x=>rowKernel N c (X x) out inp a b) u := by
  induction N generalizing X a b with
  | zero => exact analyticAt_const
  | succ N ih =>
    apply Finset.analyticAt_fun_sum
    intro h _
    apply (analytic_exchangeNumerator c _ (hX 0) _ _).mul
    exact ih (fun x=>skipOne 0 (X x)) (fun j=>hX (j+1)) _ _ _ _

theorem analytic_transferMatrix (N : ℕ) (κ c : ℂ) (X : E → ℕ → ℂ)
    (hX : ∀ j,AnalyticAt ℂ (fun x=>X x j) u) (out inp : Fin N → Spin) :
    AnalyticAt ℂ (fun x=>transferMatrix N κ c (X x) out inp) u := by
  apply Finset.analyticAt_fun_sum
  intro h _
  exact analyticAt_const.mul (analytic_rowKernel N c X hX out inp h h)

theorem analytic_finite_product {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i∈s,AnalyticAt ℂ (f i) u) : AnalyticAt ℂ (fun x=>∏i∈s,f i x) u := by
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const (𝕜:=ℂ) (E:=E) (x:=u) (v:=(1:ℂ)))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (by simp)).mul (ih (fun j hj=>hf j (by simp [hj])))

theorem analytic_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : E → Matrix ι ι ℂ) (hA : ∀ i j,AnalyticAt ℂ (fun x=>A x i j) u) :
    AnalyticAt ℂ (fun x=>(A x).det) u := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (analytic_finite_product _ _ (fun i _=>hA _ _))

theorem analytic_matrix_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : E → Matrix ι ι ℂ) (hA : ∀ i j,AnalyticAt ℂ (fun x=>A x i j) u) (i j : ι) :
    AnalyticAt ℂ (fun x=>(A x).adjugate i j) u := by
  simp only [Matrix.adjugate_apply]
  apply analytic_matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  split_ifs <;> first | exact analyticAt_const | exact hA _ _
end Generic
end PolynomialVacuumAlgebra

end OAI
