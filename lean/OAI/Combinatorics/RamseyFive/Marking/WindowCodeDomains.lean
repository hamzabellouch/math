import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.AllWindowBounds

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows ReverseCap ScoreGeometry PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance wcdBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance wcdIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
def codeDomainSlack (k s : ℝ) := k+2*s+Real.log 4+1+Real.log (2*(320/((9:ℝ)/100000)+320)^2)
lemma codeDomain_log {q σ k s : ℝ} (hq : 0<q) (hσ : 0≤σ) (he : Real.log q=σ)
    (hb : 0≤k+2*s+Real.log 4) :
    0≤4*σ+codeDomainSlack k s ∧
    Real.log (2*((320/((9:ℝ)/100000)+320)^2)*q^4*Real.exp ((k+2*s+Real.log 4)+1))=
      4*σ+codeDomainSlack k s := by
  have hc : 0≤Real.log (2*(320/((9:ℝ)/100000)+320)^2) := Real.log_nonneg (by norm_num)
  constructor
  · unfold codeDomainSlack;linarith
  · rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,he,Real.log_exp]
    dsimp [codeDomainSlack]
    ring
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
lemma allWindow_domain_log
    (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
    (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
    {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (k τ P : ℝ) (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd.le (9/100000) (9/10) τ P (by norm_num) t z) j).card≤
      4*σ+codeDomainSlack k s := by
  have hlog:=codeDomain_log (q:=(Nat.card K:ℝ)) (σ:=σ) (k:=k) (s:=s)
    (by rw [←hq];positivity) (zero_le_one.trans hσ) (by rw [←hq,Real.log_exp]) hb
  exact log_card_of_card_bound _ _ _
    (allWindow_domain_card f r p u sel E W σ hσ hq hd k (9/100000) τ P
      (by norm_num) (by norm_num) hb hdrop t z j) hlog.1 hlog.2.le
end
end SharpRamseyFive.Marking

end OAI
