import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAverage

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

@[reducible] def CascadeSpace (E : Type) : ℕ → Type
  | 0 => E
  | n+1 => CascadeSpace E n × ℝ

instance cascadeNormedGroup (E : Type) [NormedAddCommGroup E] :
    (n : ℕ) → NormedAddCommGroup (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedAddCommGroup E)
  | n+1 => letI := cascadeNormedGroup E n
    inferInstanceAs (NormedAddCommGroup (CascadeSpace E n × ℝ))

instance cascadeNormedSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (n : ℕ) → NormedSpace ℝ (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedSpace ℝ E)
  | n+1 => letI := cascadeNormedSpace E n
    inferInstanceAs (NormedSpace ℝ (CascadeSpace E n × ℝ))

section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeLift : (n : ℕ) → E → CascadeSpace E n
  | 0,u => u
  | n+1,u => (cascadeLift n u,0)

def cascadePressure : (n : ℕ) → (Fin n → ℝ) → (CascadeSpace E n → ℝ) → E → ℝ
  | 0,_,f => f
  | n+1,m,f => cascadePressure n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)

def cascadeMoment : (n : ℕ) → (Fin n → ℝ) → (CascadeSpace E n → ℝ) →
    (CascadeSpace E n → ℝ) → E → ℝ
  | 0,_,_,g => g
  | n+1,m,f,g => cascadeMoment n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g)

theorem cascadePressure_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) : BoundedDerivs (cascadePressure n m f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _)

theorem cascadeMoment_bounded_continuous (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (g : CascadeSpace E n → ℝ)
    (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) :
    Continuous (cascadeMoment n m f g) ∧ ∀ x, ‖cascadeMoment n m f g x‖ ≤ C := by
  induction n with
  | zero => exact ⟨hg,hb⟩
  | succ n ih =>
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous hf _ hg hC hb) (fun x => gaussianAverage_norm_le hf _ hb x)

theorem cascadePressure_gradient (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (x u : E) :
    fderiv ℝ (cascadePressure n m f) x u =
      cascadeMoment n m f (fun z => fderiv ℝ f z (cascadeLift n u)) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadePressure,ih (fun i => m i.castSucc) _ (hf.gaussianStep _)]
    simp_rw [fderiv_gaussianStep_apply hf]
    rfl

theorem cascade_curvature_domination (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (A : CascadeSpace E n → ℝ)
    (hA : Continuous A) {C upper lower : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖A z‖ ≤ C)
    (hmlu : lower ≤ upper) (hm : ∀ i, lower ≤ m i) (hmu : ∀ i, m i ≤ upper)
    (hmono : Monotone m) (u : E)
    (hV : ∀ z, 0 ≤ A z-(fderiv ℝ f z (cascadeLift n u))^2)
    (hH : ∀ z, upper*(A z-(fderiv ℝ f z (cascadeLift n u))^2) ≤
      fderiv ℝ (fderiv ℝ f) z (cascadeLift n u) (cascadeLift n u)) (x : E) :
    0 ≤ cascadeMoment n m f A x-(fderiv ℝ (cascadePressure n m f) x u)^2 ∧
    lower*(cascadeMoment n m f A x-(fderiv ℝ (cascadePressure n m f) x u)^2) ≤
      fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u := by
  induction n generalizing upper with
  | zero =>
    refine ⟨hV x,?_⟩
    exact (mul_le_mul_of_nonneg_right hmlu (hV x)).trans (hH x)
  | succ n ih =>
    let q := m (Fin.last n)
    let f' := gaussianStep q f
    let A' := gaussianAverage q f A
    have hv' (z : CascadeSpace E n) : 0 ≤ A' z-(fderiv ℝ f' z (cascadeLift n u))^2 :=
      gaussianStep_variance_nonneg hf hA hb q (cascadeLift n u) z (fun y => hV (z,y))
    have hh' (z : CascadeSpace E n) :
        q*(A' z-(fderiv ℝ f' z (cascadeLift n u))^2) ≤
          fderiv ℝ (fderiv ℝ f') z (cascadeLift n u) (cascadeLift n u) := by
      apply gaussianStep_curvature_domination hf hA hb q (cascadeLift n u) z
      intro y
      exact (mul_le_mul_of_nonneg_right (hmu (Fin.last n)) (hV (z,y))).trans (hH (z,y))
    exact ih (fun i => m i.castSucc) f' (hf.gaussianStep _) A'
      (gaussianAverage_continuous hf _ hA hC hb) (fun z => gaussianAverage_norm_le hf _ hb z)
      (hm (Fin.last n)) (fun i => hm i.castSucc) (fun i => hmono (Fin.le_last _))
      (fun i j hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij)) hv' hh'

end Cascade
end SK.Analytic

end
end
end
end
end
end
end

end OAI
