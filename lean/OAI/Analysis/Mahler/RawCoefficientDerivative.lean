import OAI.Analysis.Mahler.RawClosedPower
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rawCoefficientDerivative (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (v : ι → E) : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
  { toFun w := D w v
    map_add' w z := by simp
    map_smul' r w := by simp }

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma rawCoefficientDerivative_apply [Fintype ι] [DecidableEq ι]
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) (w : E) :
    rawCoefficientDerivative D v w = D w v := rfl

/-- A coefficientwise derivative records actual HasFDerivAt proofs for
all tuples. It adds no differentiability or exterior-calculus assumptions. -/
def HasRawFDerivAt (a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (x : E) : Prop :=
  ∀ v, HasFDerivAt (fun y => a y v) (rawCoefficientDerivative D v) x

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem HasRawFDerivAt.product [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {b : E → MultilinearMap ℝ (fun _ : κ => E) ℂ}
    {Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a Da x) (hb : HasRawFDerivAt b Db x) :
    HasRawFDerivAt (fun y => rawProduct (a y) (b y))
      (rawProductVariation (a x) Da (b x) Db) x := by
  intro v
  have hd := (ha (fun i => v (Sum.inl i))).mul (hb (fun i => v (Sum.inr i)))
  apply hd.congr_fderiv
  ext w
  simp [rawCoefficientDerivative_apply, rawProductVariation, rawProduct_apply,
    smul_eq_mul]
  ring

theorem HasRawFDerivAt.power {B : E → MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ}
    {DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ} {x : E}
    (hB : HasRawFDerivAt B DB x) (k : ℕ) :
    HasRawFDerivAt (fun y => rawPower (B y) k) (rawPowerVariation (B x) DB k) x := by
  induction k with
  | zero =>
    intro v
    have hz : rawCoefficientDerivative (rawPowerVariation (B x) DB 0) v = 0 := by ext w; rfl
    rw [hz]
    exact hasFDerivAt_const (1 : ℂ) x
  | succ k ih => exact hB.product ih

end
end Mahler

end OAI
