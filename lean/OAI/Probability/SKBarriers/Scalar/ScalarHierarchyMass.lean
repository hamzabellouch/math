import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMassOne
import OAI.Probability.SKBarriers.Scalar.ScalarMassStability

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Congr
variable {E : Type}
theorem gaussianStep_section_congr (m : ℝ) (f g : E × ℝ → ℝ) (x y : E)
    (hfg : ∀ z, f (x,z)=g (y,z)) : gaussianStep m f x=gaussianStep m g y := by
  unfold gaussianStep positiveGaussianLogStep
  simp_rw [hfg]
end Congr

theorem scalarStep_translate (m v c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    scalarStep m v (fun t => f (c+t)) x=scalarStep m v f (c+x) := by
  apply gaussianStep_section_congr
  intro z
  simp only [add_assoc]

theorem scalarStep_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {m : ℝ} (hm : 0 ≤ m) (v : ℝ) :
    LipschitzWith K (scalarStep m v f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb (z : ℝ) : |f ((x-y)+z)-f z| ≤ (K:ℝ)*|x-y| := by
    simpa only [Real.norm_eq_abs,add_sub_cancel_right] using hLip.norm_sub_le ((x-y)+z) z
  have H := scalarStep_uniform_nonexpansive (hf.translate (x-y)) hf hm hb v y
  rw [scalarStep_translate,sub_add_cancel] at H
  simpa only [Real.dist_eq] using H

theorem scalarHierarchy_regular (n : ℕ) (m v : Fin n → ℝ) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (scalarStep_regular hf _ _)

theorem scalarHierarchy_lipschitz (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hLip : LipschitzWith K f) :
    LipschitzWith K (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hLip
  | succ n ih =>
    exact ih _ _ (fun i => hm i.castSucc) (scalarStep_regular hf _ _)
      (scalarStep_lipschitz hf hLip (hm _) _)

theorem scalarHierarchy_uniform_nonexpansive (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hfg : ∀ z, |f z-g z| ≤ ε) (x : ℝ) :
    |scalarHierarchy n m v f x-scalarHierarchy n m v g x| ≤ ε := by
  induction n generalizing f g with
  | zero => exact hfg x
  | succ n ih =>
    exact ih _ _ (fun i => hm i.castSucc) (scalarStep_regular hf _ _)
      (scalarStep_regular hg _ _) (scalarStep_uniform_nonexpansive hf hg (hm _) hfg _)

theorem scalarHierarchy_mass_lipschitz (n : ℕ) (m m' v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hm' : ∀ i, m' i ∈ Icc (0:ℝ) 1)
    {B : ℝ} (hvB : ∀ i, |v i| ≤ B) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (x : ℝ) :
    |scalarHierarchy n m' v f x-scalarHierarchy n m v f x| ≤
      gaussianMassBound B * ∑ i, (v i)^2 * |m' i-m i| := by
  induction n generalizing f with
  | zero => simp [scalarHierarchy]
  | succ n ih =>
    let a := Fin.last n
    let f₁ := scalarStep (m' a) (v a) f
    let f₀ := scalarStep (m a) (v a) f
    have h₁ := scalarHierarchy_uniform_nonexpansive n (fun i => m' i.castSucc)
      (fun i => v i.castSucc) (fun i => (hm' i.castSucc).1)
      (scalarStep_regular hf (m' a) (v a)) (scalarStep_regular hf (m a) (v a))
      (scalarStep_mass_lipschitz hf hLip (hvB a) (hm a) (hm' a)) x
    have h₂ := ih (fun i => m i.castSucc) (fun i => m' i.castSucc) (fun i => v i.castSucc)
      (fun i => hm i.castSucc) (fun i => hm' i.castSucc) (fun i => hvB i.castSucc)
      (scalarStep_regular hf (m a) (v a)) (scalarStep_lipschitz hf hLip (hm a).1 (v a))
    calc
      _ ≤ |scalarHierarchy n (fun i => m' i.castSucc) (fun i => v i.castSucc) f₁ x-
             scalarHierarchy n (fun i => m' i.castSucc) (fun i => v i.castSucc) f₀ x|+
           |scalarHierarchy n (fun i => m' i.castSucc) (fun i => v i.castSucc) f₀ x-
             scalarHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc) f₀ x| :=
          abs_sub_le _ _ _
      _ ≤ gaussianMassBound B*(v a)^2*|m' a-m a|+
          gaussianMassBound B*∑ i : Fin n, (v i.castSucc)^2*|m' i.castSucc-m i.castSucc| :=
          add_le_add h₁ h₂
      _ = _ := by rw [Fin.sum_univ_castSucc]; dsimp [a]; ring

end SK.Analytic

end
end

end OAI
