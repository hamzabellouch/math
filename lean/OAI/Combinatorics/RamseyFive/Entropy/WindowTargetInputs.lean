import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowReciprocalScores
import OAI.Combinatorics.RamseyFive.Entropy.ConditionPullback

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]
lemma map_first_value (p : Law Ω) (z : Ω→α×β) :
    map p (fun x=>(z x).1)=first (map p z) := by
  rw [←map_first, map_comp]; rfl
lemma map_second_value (p : Law Ω) (z : Ω→α×β) :
    map p (fun x=>(z x).2)=second (map p z) := by
  rw [←map_second, map_comp]; rfl
lemma eventMass_bad_map (p : Law Ω) (f : Ω→α) (G : Finset α) :
    eventMass p (Finset.univ.filter fun x=>f x∉G)=eventMass (map p f) Gᶜ := by
  rw [eventMass_map_preimage]
  congr 1
  ext x
  simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance inputWinBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance inputWinIDE : DecidableEq (Slots w r) := Classical.decEq _

omit [FiniteDimensional K V] [Nonempty (Fin r)] in
theorem window_bad_target (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r)) (s d ε C₀ : ℝ)
    (hs : 0<s)
    (hA : ((support (first (map p (fun x=>x (middleSlot v t))))).card:ℝ) ≤
      32*Real.exp (5*Real.log (Nat.card K)-u (middleSlot v t)))
    (hB : ((support (second (map p (fun x=>x (middleSlot v t))))).card:ℝ) ≤
      32*Real.exp (u (middleSlot v t)))
    (hflag : ((support (map p (fun x=>x (middleSlot v t)))).card:ℝ) ≤ C₀*(Nat.card K:ℝ)^4)
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p
      (orderedCollision p (slotEquiv w r) u s) sel (middleSlot v t)=0) :
    eventMass p (Finset.univ.filter fun x=>(x (middleSlot v t)).1∉
      reciprocalGoodA (map p (fun y=>y (middleSlot v t))) (u (middleSlot v t)) s) ≤
        reciprocalBadMass s d C₀ ∧
    eventMass p (Finset.univ.filter fun x=>(x (middleSlot v t)).2∉
      reciprocalGoodB (map p (fun y=>y (middleSlot v t))) (u (middleSlot v t)) s) ≤
        reciprocalBadMass s d C₀ := by
  have hent:=(good_index_scores (4*Real.log (Nat.card K)) d ε p _
    (fun i j=>orderedCollision_nonneg p (slotEquiv w r) u s i j) sel _ hgood).1
  have hh:=reciprocal_bad_endpoints (map p (fun x=>x (middleSlot v t))) _ s d C₀
    hs hA hB hflag hent
  rw [eventMass_bad_map,eventMass_bad_map,map_first_value,map_second_value]
  exact hh
end
end SharpRamseyFive.Marking

end OAI
