import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryTranscript
import OAI.Probability.CriticalPercolation.Criticality.ReverseReference
import OAI.Probability.CriticalPercolation.Entropy.MarkedBits

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance kernelsFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pivotGuess (i : Fin n) (ω : E → Bool) (e : E) : ℝ :=
  (LazyDFS.search G order (stepLeft (E := E) d x n D i) (stepTargets (E := E) d x n D i)).reverseGuess
    p (fun σ => ∃ b ∈ stepTargets (E := E) d x n D i,
      (G.openGraph σ).Reachable (stepLeft (E := E) d x n D i) b) w (configuration ω) 0 e

lemma pivotGuess_subprobability (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    (∀ e, 0 ≤ pivotGuess G order d x p w n D i ω e) ∧
      (∑ e, pivotGuess G order d x p w n D i ω e) ≤ 1 := by
  apply SearchTree.reverseGuess_subprobability _ ∅ (LazyDFS.compile_valid G order _ _ _ _) hp
  · rintro a b hab ⟨v,hv,hr⟩
    exact ⟨v,hv,hr.mono (G.openGraph_mono hab)⟩
  · exact homogeneous_normalized w p h0 h1
  · exact fun e b => (homogeneous_positive w hp h0 h1 e b).le
  · exact fun e _ => ⟨h0 e,h1 e⟩

noncomputable def inverseKernel (j : ℕ) (ω : E → Bool) (m : Option E) : ℝ :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => 0 | some e => pivotGuess G order d x p w n D ⟨j,hj⟩ ω e
    else if m = none then 1 else 0
  else if m = none then 1 else 0

noncomputable def inverseUpdate (j : ℕ) (ω : E → Bool) (m : Option E) : E → Bool :=
  if hj : j < n then
    if (⟨j,hj⟩ : Fin n) ∈ activeSteps n D then
      match m with | none => ω | some e => Function.update ω e false
    else ω
  else ω

lemma inverseKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) (m : Option E) : 0 ≤ inverseKernel G order d x p w n D j ω m := by
  unfold inverseKernel
  split_ifs with hj hi hm hm
  · cases m with
    | none => exact le_rfl
    | some e => exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).1 e
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl

lemma inverseKernel_sum (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) : (∑ m, inverseKernel G order d x p w n D j ω m) ≤ 1 := by
  unfold inverseKernel
  split_ifs with hj hi
  · rw [Fintype.sum_option]
    simp only [zero_add]
    exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).2
  · simp
  · simp

noncomputable def contactTotal (i : Fin n) (ω : E → Bool) : ℝ :=
  ∑ m, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def inactiveKernel (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if i ∈ activeSteps n D then if m=none then 1 else 0
  else if contactTotal G order d x p w n D i ω = 0 then if m=none then 1 else 0
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m /
    contactTotal G order d x p w n D i ω

lemma contactTotal_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    0 ≤ contactTotal G order d x p w n D i ω :=
  Finset.sum_nonneg fun m _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m

lemma inactiveKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (ω : E → Bool) (m : Option E) : 0 ≤ inactiveKernel G order d x p w n D i ω m := by
  unfold inactiveKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m)
      (contactTotal_nonneg G order d x p w n D hp h0 h1 i ω)

lemma inactiveKernel_sum (i : Fin n) (ω : E → Bool) :
    (∑ m, inactiveKernel G order d x p w n D i ω m) = 1 := by
  unfold inactiveKernel
  split_ifs with hi ht
  · simp
  · simp
  · rw [← Finset.sum_div]
    exact div_self ht

noncomputable def inverseReference : ((E → Bool) × (Fin n → Option E) × (Fin n → Option E)) → ℝ :=
  ReverseReference.joint (FiniteProduct.density (QueryTree.bitWeight p))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inactiveKernel G order d x p w n D) n

lemma inverseReference_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (z) :
    0 ≤ inverseReference G order d x p w n D z :=
  ReverseReference.joint_nonneg _ (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    _ _ (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    _ (inactiveKernel_nonneg G order d x p w n D hp h0 h1) n z

lemma inverseReference_marginal (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Bool) :
    pushMass Prod.fst (inverseReference G order d x p w n D) ω ≤
      FiniteProduct.density (QueryTree.bitWeight p) ω := by
  have he := ReverseReference.joint_marginal_le
    (FiniteProduct.density (QueryTree.bitWeight p) : (E → Bool) → ℝ)
    (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    (inverseKernel_sum G order d x p w n D hp h0 h1)
    (inactiveKernel G order d x p w n D) (inactiveKernel_sum G order d x p w n D) n ω
  refine Eq.trans_le ?_ he
  unfold pushMass
  apply Finset.sum_congr
  · ext z
    simp only [Finset.mem_univ]
  · intro z _
    rfl

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
