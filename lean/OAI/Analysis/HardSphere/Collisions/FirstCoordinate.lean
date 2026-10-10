import Mathlib
import OAI.Analysis.HardSphere.Geometry.FrozenChecks
import OAI.Analysis.HardSphere.Conditioning.BathPhase

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HardSphere
lemma insertFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
    MeasurePreserving (fun p : Torus L×Configuration (N-1) L ↦ insertFirst hN p.1 p.2)
      ((volume : Measure (Torus L)).prod volume) volume := by
  cases N with
  | zero => omega
  | succ n =>
    unfold insertFirst
    have h := (cons_preserving (n:=n) L).comp
      (Measure.measurePreserving_swap (μ:=(volume : Measure (Torus L))) (ν:=volume))
    convert h using 1 <;> simp [Function.comp_def]

lemma bathFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
    MeasurePreserving (fun p : Configuration (N-1) L×Torus L ↦ insertFirst hN p.2 p.1)
      ((volume : Measure (Configuration (N-1) L)).prod volume) volume :=
  (insertFirst_preserving hN L).comp (Measure.measurePreserving_swap)

lemma ground_slice_memLp {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
    MemLp (fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)) 2
      ((volume : Measure (Configuration (N-1) L)).prod volume) :=
  (Lp.memLp ψ).comp_measurePreserving (bathFirst_preserving hN L)

lemma occupation_nonneg {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
    0≤occupation hN ψ := by
  unfold occupation
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg L.property.le _))
    (integral_nonneg fun _ ↦ sq_nonneg _)

end HardSphere

end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype C] in
lemma frozen_uniformInsertion_on (checks : C → LocalCheck X) (U S : Finset I)
    (hSU : S⊆U) (x : ∀i,X i) (μ : ∀i,Measure (X i)) {a : ℝ≥0∞}
    (h : UniformInsertionOn checks μ a S) :
    UniformInsertionOn (frozenChecks checks U x) μ a S := by
  intro i hi s his y
  have hin : i∉s∪(Finset.univ\U) := by simp [Finset.mem_union,his,hSU hi]
  apply (h i hi (s∪(Finset.univ\U)) hin (freezeOutside U x y)).trans
  apply lintegral_mono
  intro v
  dsimp only
  rw [←freezeOutside_update U x y (hSU hi) v]
  by_cases hp : freezeOutside U x (Function.update y i v)∈insertionEvent checks (s∪(Finset.univ\U)) i
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (frozen_insertion checks U s x (Function.update y i v) i hp)]
  · rw [Set.indicator_of_notMem hp]
    exact bot_le
end HardSphere.Comparison

end
end

end

end OAI
