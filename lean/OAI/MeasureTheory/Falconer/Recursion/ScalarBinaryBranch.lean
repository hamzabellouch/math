import OAI.MeasureTheory.Falconer.Estimates.ScalarSwitchProgression

namespace OAI

/-! A nonporous binary state produces many separated children in a
 fixed-fold sumset. Only actual bit updates of original words are used. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 def ScalarBinaryTail {N : ℕ} (n : ℕ) (w : Fin N → Bool) : Prop :=
  ∀ j : Fin N, n ≤ (j:ℕ) → w j = false

noncomputable def scalarBinaryStep {N k : ℕ} (c : Fin k → Fin N → Bool)
    (n : Fin N) (F : Finset (Fin k)) : Fin k → Fin N → Bool :=
  fun i => if i ∈ F then Function.update (c i) n true else c i

noncomputable def scalarBinarySum {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) : ℝ := ∑ i, f (c i)

 theorem scalar_binary_step_tail {N k : ℕ} (c : Fin k → Fin N → Bool)
    (n : Fin N) (F : Finset (Fin k)) (hc : ∀ i, ScalarBinaryTail n (c i)) :
    ∀ i, ScalarBinaryTail ((n:ℕ)+1) (scalarBinaryStep c n F i) := by
  intro i j hj
  have hjn : j ≠ n := by intro h; subst j; omega
  unfold scalarBinaryStep
  split_ifs
  · rw [Function.update_of_ne hjn]
    exact hc i j (by omega)
  · exact hc i j (by omega)

 theorem scalar_binary_step_sum {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) (n : Fin N) (F : Finset (Fin k)) :
    scalarBinarySum f (scalarBinaryStep c n F) =
      scalarSwitchSum Finset.univ F (fun i => f (c i))
        (fun i => f (Function.update (c i) n true)) := by
  apply Finset.sum_congr rfl
  intro i hi
  unfold scalarBinaryStep
  split_ifs <;> rfl

 theorem scalar_binary_sum_mem {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (A : Finset ℝ) (hf : ∀ w, f w ∈ A) (c : Fin k → Fin N → Bool) :
    scalarBinarySum f c ∈ k • A := by
  simpa [scalarBinarySum] using scalar_sum_mem_nsmul Finset.univ (fun i => f (c i)) A
    (fun i _ => hf (c i))

 theorem scalar_binary_branch {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) (n : Fin N) (hc : ∀ i, ScalarBinaryTail n (c i))
    {ε R ell ρ : ℝ} (hε : 0 < ε)
    (hlo : ∀ w, ScalarBinaryTail n w → ell ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ w, ScalarBinaryTail n w → |f (Function.update w n true)-f w| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ k) (hmargin : ρ+2*(J:ℝ)*ε ≤ ell) :
    ∃ e : ℕ → Fin k, Set.InjOn e (Finset.range J : Set ℕ) ∧
      (∀ j ≤ J, ∀ i, ScalarBinaryTail ((n:ℕ)+1)
        (scalarBinaryStep c n ((Finset.range j).image e) i)) ∧
      (∀ j ≤ J, |scalarBinarySum f (scalarBinaryStep c n ((Finset.range j).image e))-
        scalarBinarySum f c| ≤ (j:ℝ)*R) ∧
      (∀ i ≤ J, ∀ j ≤ J, i ≠ j →
        ρ ≤ |scalarBinarySum f (scalarBinaryStep c n ((Finset.range i).image e))-
          scalarBinarySum f (scalarBinaryStep c n ((Finset.range j).image e))|) := by
  let p : Fin k → ℝ := fun i => f (c i)
  let q : Fin k → ℝ := fun i => f (Function.update (c i) n true)
  have hl : ∀ i ∈ (Finset.univ : Finset (Fin k)), ell ≤ |q i-p i| :=
    fun i _ => hlo (c i) (hc i)
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin k)), |q i-p i| ≤ R :=
    fun i _ => hhi (c i) (hc i)
  obtain ⟨e,he,hinj,a,ha,hd⟩ := scalar_increment_ordering hε (Finset.univ : Finset (Fin k))
    (fun i => q i-p i) hl hu L J hJ hR (by simpa using hsize)
  refine ⟨e,hinj,fun j _ => scalar_binary_step_tail c n _ hc,?_,?_⟩
  · intro j hj
    rw [scalar_binary_step_sum]
    have hh := scalar_switch_prefix_displacement Finset.univ p q e J j hj he hinj hu
    simpa only [p,q,scalarBinarySum] using hh
  · intro i hi j hj hij
    rw [scalar_binary_step_sum,scalar_binary_step_sum]
    have hh := scalar_switch_progression_separated Finset.univ p q e hε.le J he hinj
      (fun m hm => (hd m hm).le) (hmargin.trans ha) i hi j hj hij
    simpa only [p,q] using hh

end Falconer

end OAI
