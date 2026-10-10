import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockAdaptiveOverlap
import OAI.Probability.SKBarriers.Interpolation.AdaptiveSummation
import OAI.Probability.SKBarriers.Interpolation.SKPressureCurve

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def skAdaptivePressure (N k : ℕ) (β : ℝ) (q : Fin (k+1) → ℝ) (u : ℝ) : ℝ :=
  skBlockRoot N k (β*Real.sqrt (1-u))
    (fun b => β*Real.sqrt (cumulativeGapMap k q b))/(N:ℝ)

def skAdaptiveExponent (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) :=
  blockExponent (skInteraction N) (fun _ => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ))
    (fun b => β*Real.sqrt (cumulativeGapMap k q b))

def skAdaptiveMean (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (skAdaptiveExponent N k β u q)
    (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k j)

def skAdaptiveError (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyOverlapError (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (skAdaptiveExponent N k β u q)
    (fun s i => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k j)

theorem skAdaptiveMean_eq_block (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) :
    skAdaptiveMean N k β u q = blockAdaptiveOverlap (skInteraction N)
      (fun _ => β/Real.sqrt (N:ℝ)) β
      (Real.sqrt (1-u),fun b => Real.sqrt (cumulativeGapMap k q b)) := by
  have ha : (fun _ : Fin (Fintype.card (Edge N)) => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ)) =
      (fun _ => Real.sqrt (1-u)*(β/Real.sqrt (N:ℝ))) := by
    funext i
    ring
  funext j
  simp only [skAdaptiveMean,skAdaptiveExponent,blockAdaptiveOverlap,ha]

theorem skAdaptivePressure_hasDerivAt {N k : ℕ} (hN : 0 < N)
    (β : ℝ) (q : ℝ → Fin (k+1) → ℝ) {u : ℝ} (hu : u < 1)
    (hgap : ∀ b, 0 < cumulativeGapMap k (q u) b)
    (hq : HasDerivAt q (skAdaptiveMean N k β u (q u)) u) :
    HasDerivAt (fun t => skAdaptivePressure N k β (q t) t)
      ((β^2/4)*(-1+2*skAdaptiveMean N k β u (q u) (Fin.last k)-
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(skAdaptiveMean N k β u (q u) j)^2+
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*skAdaptiveError N k β u (q u) j)) u := by
  let r := skAdaptiveMean N k β u (q u)
  let h : ℝ → ℝ := fun t => β*Real.sqrt (1-t)
  let v : ℝ → Fin (k+1) → ℝ := fun t b => β*Real.sqrt (cumulativeGapMap k (q t) b)
  let hp : ℝ := β*(-1/(2*Real.sqrt (1-u)))
  let vp : Fin (k+1) → ℝ := fun b => β*(cumulativeGapMap k r b/(2*Real.sqrt (cumulativeGapMap k (q u) b)))
  have hh : HasDerivAt h hp u := by
    have H := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).sqrt (by linarith : 1-u ≠ 0)
    simpa [h,hp] using H.const_mul β
  have hv : HasDerivAt v vp u := by
    apply hasDerivAt_pi.mpr
    intro b
    have H := hasDerivAt_pi.mp ((cumulativeGapMap k).hasFDerivAt.comp_hasDerivAt u hq) b
    exact (H.sqrt (hgap b).ne').const_mul β
  have hham : h u*hp/2 = -(β^2/4) := by
    have hs : Real.sqrt (1-u) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    dsimp only [h,hp]
    field_simp [hs]
    ring
  have hvp (b : Fin (k+1)) : vp b*v u b = (β^2/2)*cumulativeGapMap k r b := by
    have hs : Real.sqrt (cumulativeGapMap k (q u) b) ≠ 0 := (Real.sqrt_pos.mpr (hgap b)).ne'
    dsimp only [v,vp]
    field_simp [hs]
  have hsecond (j : Fin (k+1)) : hierarchyReplicaSecond
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (blockLevel (Fintype.card (Edge N)) N k j) = (r j)^2+skAdaptiveError N k β u (q u) j := by
    have H := hierarchyOverlapError_eq_second_sub_sq
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (fun s i => by cases s i <;> norm_num [spin]) (blockLevel (Fintype.card (Edge N)) N k j)
    change skAdaptiveError N k β u (q u) j = _-(r j)^2 at H
    linarith
  have H := skBlockPressure_hasDerivAt hN h v hh hv
  dsimp only at H
  change HasDerivAt (fun t => skAdaptivePressure N k β (q t) t) _ u at H
  apply H.congr_deriv
  rw [hham]
  simp only [hvp]
  change -(β^2/4)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*hierarchyReplicaSecond
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (blockLevel (Fintype.card (Edge N)) N k j))+
    (∑ b, (β^2/2)*cumulativeGapMap k r b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) = _
  simp_rw [hsecond]
  simpa only [mul_assoc,← Finset.mul_sum] using adaptive_pressure_algebra k r (fun _ => ((k+1:ℕ):ℝ)⁻¹) (skAdaptiveError N k β u (q u)) β
end SK.Analytic

end
end

end

end OAI
