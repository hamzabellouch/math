import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchySegmentTrace
import OAI.Probability.SKBarriers.Hierarchy.BlockMassValue

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section BlockTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem equalBlock_trace_integral (D N k : ℕ) (hN : 0 < N)
    (U : S → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (scale : Fin (k+1) → ℝ) (ha : ∀ b, 0 < scale b)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s b i, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = scale b*v s i)
    (j : Fin k) :
    (∫ z, hierarchyTraceSquare (blockDimension D N k) (blockMass D N k) U v (blockLevel D N k j.castSucc) z
      ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => v s i) (blockLevel D N k j.succ)-
      hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => v s i) (blockLevel D N k j.castSucc)+
      1/((N : ℝ)*(scale j.succ)^2*(((j.val+1 : ℕ) : ℝ)/((k+1 : ℕ) : ℝ))^2) := by
  let n := blockDimension D N k
  let a := D+(j.val+1)*N
  let p : ℝ := ((j.val+1 : ℕ) : ℝ)/((k+1 : ℕ) : ℝ)
  have hseg : a+N ≤ n := by
    dsimp [a,n,blockDimension]
    have h : (j.val+2)*N ≤ (k+1)*N := Nat.mul_le_mul_right N (by omega)
    nlinarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : (0 : ℝ) < ((k+1 : ℕ) : ℝ))).2
    exact_mod_cast (show j.val+1 ≤ k+1 by omega)
  have hb (i : Fin N) : blockMass D N k ⟨a+i,by omega⟩ = p := by
    simpa only [p,a,fieldIndex,Fin.val_succ] using blockMass_at_field D N k j.succ i
  have hm (i : Fin n) (hi : a+N ≤ i.val) : p ≤ blockMass D N k i := by
    rw [← hb ⟨0,hN⟩]
    exact (blockMass_valid D N k).2.2 (by change a+0 ≤ i.val; omega)
  have HV (s : S) (i : Fin N) : U s (coordinateAxis n ⟨a+i,by omega⟩) = scale j.succ*v s i :=
    hv s j.succ i
  have H := hierarchySegment_trace_integral n a N hseg hN (blockMass D N k) U p (scale j.succ)
    hp (ha j.succ) hp1 hb hm (blockMass_valid D N k).2.1 (blockMass_valid D N k).2.2 v hvb HV
  have he : (⟨a+N,by omega⟩ : Fin (n+1)) = blockLevel D N k j.succ := by
    apply Fin.ext
    simp only [blockLevel_val,Fin.val_succ,a]
    ring
  rw [he] at H
  exact H
end BlockTrace
end SK.Analytic

end
end

end

end OAI
