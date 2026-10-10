import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowDeletionCount

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance boundsBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance boundsIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)

omit [Nonempty (Fin n)] in
lemma surviving_domain_card (hE : E.Nonempty) (k c τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10)
    (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t (Finset.univ,Finset.univ)
      (survivingEncoded f r p u sel E hE (W hE) σ hσ hq hd.le c (9/10) τ P (by norm_num) t z) j).card:ℝ)≤
    2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp ((k+2*s+Real.log 4)+1) := by
  exact variableTreeDomain_card f r t (Finset.univ,Finset.univ)
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
    (fun i=>(W hE).firstSupport i (z.1 i)) (fun i=>(W hE).secondSupport i (z.2 i))
    (fun i=>(W hE).first_nonempty i _) (fun i=>(W hE).second_nonempty i _)
    c τ P (k+2*s+Real.log 4) hc hc9 hb
    (fun i=>(W hE).support_product k
      (fun v=>hdrop _ (survivingOriginal_mem E hE v)) i (z.1 i) (z.2 i)) j

omit [Nonempty (Fin n)] in
theorem allWindow_domain_card (k c τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10)
    (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd.le c (9/10) τ P (by norm_num) t z) j).card:ℝ)≤
    2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp ((k+2*s+Real.log 4)+1) := by
  unfold allWindowEncoded
  split_ifs with hE
  · exact surviving_domain_card f r p u sel E W σ hσ hq hd hE k c τ P hc hc9 hb hdrop t z j
  · rw [variableTreeEmpty_domain]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

lemma log_card_of_card_bound {A : Type*} (E : Finset A) (C M : ℝ)
    (hC : (E.card:ℝ)≤C) (hM : 0≤M) (hlog : Real.log C≤M) : Real.log E.card≤M := by
  by_cases he : E.card=0
  · simpa only [he,Nat.cast_zero,Real.log_zero] using hM
  · have hp : (0:ℝ)<E.card := by exact_mod_cast Nat.pos_of_ne_zero he
    exact (Real.log_le_log hp hC).trans hlog
end
end SharpRamseyFive.Marking

end OAI
