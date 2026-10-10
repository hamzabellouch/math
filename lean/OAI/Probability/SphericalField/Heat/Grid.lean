import Mathlib
import OAI.Probability.SphericalField.Heat.Backward

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianGrid (N : ℕ) (p v : Fin N → ℝ) (f : E → ℝ) : E → ℝ :=
  gaussianBackward (stdGaussian E) (List.ofFn fun i => (p i,Real.sqrt (v i))) f

lemma gaussianGrid_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p v : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    LipschitzWith L (gaussianGrid N p v f) := by
  apply gaussianBackward_lipschitz _ hf
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact hp i

omit [BorelSpace E] in
lemma gaussianGrid_succ (N : ℕ) (p v : Fin (N+1) → ℝ) (f : E → ℝ) :
    gaussianGrid (N+1) p v f = gaussianEntropic (stdGaussian E) (p 0) (Real.sqrt (v 0))
      (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f) := by
  simp only [gaussianGrid,List.ofFn_succ,gaussianBackward]

lemma gaussianGrid_zero {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    gaussianGrid N p (fun _ => 0) f=f := by
  induction N with
  | zero => simp [gaussianGrid,gaussianBackward]
  | succ N ih =>
    rw [gaussianGrid_succ,Real.sqrt_zero,ih (fun i => p i.succ) (fun i => hp i.succ)]
    funext x
    exact gaussianEntropic_variance_zero hf _ _

lemma gaussianGrid_absorb {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p v : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hv : ∀ i, 0 ≤ v i)
    (j : Fin N) (a : ℝ) (ha : 0 ≤ a) (hpre : ∀ i, i < j → v i=0) :
    gaussianEntropic (stdGaussian E) (p j) (Real.sqrt a) (gaussianGrid N p v f)=
      gaussianGrid N p (fun i => v i+if i=j then a else 0) f := by
  induction N with
  | zero => exact j.elim0
  | succ N ih =>
    revert hpre
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hpre
      have ht := gaussianGrid_lipschitz hf N (fun i => p i.succ) (fun i => v i.succ)
        (fun i => hp i.succ)
      rw [gaussianGrid_succ,gaussianGrid_succ]
      simp only [ite_true,Fin.succ_ne_zero,ite_false,add_zero]
      funext x
      have H := gaussianEntropic_semigroup ht (hp 0) (Real.sqrt a) (Real.sqrt (v 0)) x
      rw [Real.sq_sqrt ha,Real.sq_sqrt (hv 0),add_comm a (v 0)] at H
      exact H
    · intro hpre
      have hv0 : v 0=0 := hpre 0 (by simp [Fin.lt_def])
      have ht := gaussianGrid_lipschitz hf N (fun i => p i.succ) (fun i => v i.succ)
        (fun i => hp i.succ)
      have ht' := gaussianGrid_lipschitz hf N (fun i => p i.succ)
        (fun i => v i.succ+if i=j then a else 0) (fun i => hp i.succ)
      have H := ih (fun i => p i.succ) (fun i => v i.succ) (fun i => hp i.succ)
        (fun i => hv i.succ) j (fun i hij => hpre i.succ (Fin.succ_lt_succ_iff.mpr hij))
      rw [gaussianGrid_succ,gaussianGrid_succ]
      simp only [hv0,(Ne.symm (Fin.succ_ne_zero j)),ite_false,add_zero,Real.sqrt_zero,Fin.succ_inj]
      have e₁ : gaussianEntropic (stdGaussian E) (p 0) 0
          (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f)=
          gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f := by
        funext x; exact gaussianEntropic_variance_zero ht _ _
      have e₂ : gaussianEntropic (stdGaussian E) (p 0) 0
          (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ+if i=j then a else 0) f)=
          gaussianGrid N (fun i => p i.succ) (fun i => v i.succ+if i=j then a else 0) f := by
        funext x; exact gaussianEntropic_variance_zero ht' _ _
      rw [e₁,e₂]
      exact H

end

def gridVariance {N : ℕ} (l : List (Fin N×ℝ)) (i : Fin N) : ℝ :=
  (l.map fun c => if c.1=i then c.2 else 0).sum

lemma gridVariance_nonneg {N : ℕ} (l : List (Fin N×ℝ))
    (hl : ∀ c ∈ l, 0 ≤ c.2) (i : Fin N) : 0 ≤ gridVariance l i := by
  unfold gridVariance
  apply List.sum_nonneg
  intro x hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact hl c hc
  · exact le_rfl

lemma gridVariance_below {N : ℕ} (l : List (Fin N×ℝ)) {j i : Fin N}
    (hl : ∀ c ∈ l, j ≤ c.1) (hij : i < j) : gridVariance l i=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  rw [ite_eq_right (ne_of_gt (hij.trans_le (hl c hc)))]

lemma gridVariance_cons {N : ℕ} (c : Fin N×ℝ) (l : List (Fin N×ℝ)) :
    gridVariance (c::l)=fun i => gridVariance l i+if i=c.1 then c.2 else 0 := by
  funext i
  simp only [gridVariance,List.map_cons,List.sum_cons,eq_comm,add_comm]

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianBackward_compress {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (l : List (Fin N×ℝ))
    (hl : l.Pairwise (fun a b => a.1 ≤ b.1)) (hv : ∀ c ∈ l, 0 ≤ c.2) :
    gaussianBackward (stdGaussian E) (l.map fun c => (p c.1,Real.sqrt c.2)) f=
      gaussianGrid N p (gridVariance l) f := by
  induction l with
  | nil =>
    simp only [List.map_nil,gaussianBackward]
    exact (gaussianGrid_zero hf N p hp).symm
  | cons c l ih =>
    have hpair := List.pairwise_cons.mp hl
    have hv' := fun d hd => hv d (List.mem_cons_of_mem c hd)
    simp only [List.map_cons,gaussianBackward,ih hpair.2 hv',gridVariance_cons]
    exact gaussianGrid_absorb hf N p (gridVariance l) hp (gridVariance_nonneg l hv')
      c.1 c.2 (hv c List.mem_cons_self) (fun i hi => gridVariance_below l hpair.1 hi)

end
end SphericalPerceptron
end
end

end OAI
