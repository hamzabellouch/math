import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterMoments
import OAI.Probability.SKBarriers.Interpolation.SKHamiltonianDerivative

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockPressure_hasDerivAt {N k : ℕ} (hN : 0 < N)
    (h : ℝ → ℝ) (v : ℝ → Fin (k+1) → ℝ) {t h' : ℝ} {v' : Fin (k+1) → ℝ}
    (hh : HasDerivAt h h' t) (hv : HasDerivAt v v' t) :
    let D := Fintype.card (Edge N)
    let n := blockDimension D N k
    let U := blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
    HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
      ((h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
        hierarchyReplicaSecond n (blockMass D N k) U (fun s i => spin (s i)) (blockLevel D N k l))+
      ∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
        hierarchyMeanOverlap n (blockMass D N k) U (fun i s => spin (s i)) (blockLevel D N k l) else 0)) t := by
  dsimp only
  let D := Fintype.card (Edge N)
  let n := blockDimension D N k
  let a := fun u => fun _ : Fin D => h u/Real.sqrt (N:ℝ)
  let a' : Fin D → ℝ := fun _ => h'/Real.sqrt (N:ℝ)
  let P := fun c : Fin n → ℝ => hierarchyPressure n (blockMass D N k)
    (affineLogPartition (fun _ => 0) (spinExponent n c (blockInteraction (skInteraction N)))) 0
  have hd : Differentiable ℝ P :=
    (parameter_contDiff_at_field (spinPressure_paramRegular n (blockInteraction (skInteraction N))
      (fun _ => 0) (blockMass D N k)).1 (0:ℝ)).differentiable (by norm_num)
  have ha : HasDerivAt a a' t := hasDerivAt_pi.mpr (fun _ => hh.div_const _)
  have hc := blockCoefficients_hasDerivAt (N := N) ha hv
  have H := ((hd (blockCoefficients (a t) (v t))).hasFDerivAt.comp_hasDerivAt t hc).div_const (N:ℝ)
  change HasDerivAt (fun u => skBlockRoot N k (h u) (v u)/(N:ℝ))
    (fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients a' v')/(N:ℝ)) t at H
  apply H.congr_deriv
  rw [blockCoefficients_add_split a' v',map_add]
  rw [show fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients (fun _ : Fin D => 0) v') =
    (N:ℝ)*∑ b, v' b*v t b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap n (blockMass D N k) (blockExponent (skInteraction N) (a t) (v t))
        (fun i s => spin (s i)) (blockLevel D N k l) else 0) from
    blockPressure_field_differential hN (skInteraction N) (a t) (v t) v']
  rw [show fderiv ℝ P (blockCoefficients (a t) (v t)) (blockCoefficients a' (fun _ : Fin (k+1) => 0)) =
    (N:ℝ)*(h t*h'/2)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
      hierarchyReplicaSecond n (blockMass D N k) (blockExponent (skInteraction N) (a t) (v t))
        (fun s i => spin (s i)) (blockLevel D N k l)) from
    skBlock_disorder_differential hN (h t) h' (v t)]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [a,D,n]
  field_simp
  ring
end SK.Analytic

end
end

end

end OAI
