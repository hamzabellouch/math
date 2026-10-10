import OAI.Computability.MatchingCount.ScaledAlgorithm

namespace OAI

section

namespace BinaryMatching.Algorithm
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

lemma Q_pos (G : Input) (hn : 2≤G.n) : 0<Q G :=
  Nat.mul_pos (D₀_pos G hn) (by positivity)

def decodeIntegral (G : Input) (s : IntegralState G.n) : State G.n :=
  ⟨s.numerators,s.best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ))⟩

lemma integralValue_div (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)/(Q G:ℚ)=trialValue G a r := by
  rw [integralValue_cast G hn]
  have hQ : (Q G:ℚ)≠0 := by exact_mod_cast (Q_pos G hn).ne'
  exact mul_div_cancel_left₀ _ hQ

lemma decodeIntegral_step (G : Input) (hn : 2≤G.n) (s : IntegralState G.n) :
    decodeIntegral G (integralStep G s)=step G (decodeIntegral G s) := by
  obtain ⟨a,b⟩ := s
  dsimp only [decodeIntegral,integralStep,step]
  rw [integralRow_eq _ (D₀_pos G hn),integralUpdate_eq G hn]
  congr 1
  cases b with
  | none => simp only [Option.map_none,Option.elim_none,Option.map_some,integralValue_div G hn]
  | some v =>
    simp only [Option.map_some,Option.elim_some,Int.cast_max]
    rw [←max_div_div_right (by positivity : (0:ℚ)≤Q G),integralValue_div G hn]

lemma decodeIntegral_iterate (G : Input) (hn : 2≤G.n) (j : ℕ) :
    decodeIntegral G (integralIterate G j)=iterate G j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [integralIterate,decodeIntegral_step G hn,ih,iterate]

lemma integralIterate_table (G : Input) (hn : 2≤G.n) (j : ℕ) :
    (integralIterate G j).numerators=(iterate G j).numerators :=
  congrArg State.numerators (decodeIntegral_iterate G hn j)

lemma integralIterate_best (G : Input) (hn : 2≤G.n) (j : ℕ) :
    ((integralIterate G j).best.map (fun v : ℤ => (v:ℚ)/(Q G:ℚ)))=(iterate G j).best :=
  congrArg State.best (decodeIntegral_iterate G hn j)

def integralR (G : Input) : ℤ := ((integralIterate G (q G.n*D₀ G)).best).getD 0/(Q G:ℤ)

lemma integralR_eq (G : Input) (hn : 2≤G.n) : integralR G=R G := by
  unfold integralR R
  rw [←integralIterate_best G hn]
  cases h : (integralIterate G (q G.n*D₀ G)).best with
  | none => simp
  | some v => simp only [Option.getD_some,Option.map_some,Int.floor_div_natCast,Int.floor_intCast]

def integralEstimate (G : Input) : ℕ :=
  let r := integralR G
  if r < -10*(G.n:ℤ) then 0 else 2^(r-5*(G.n:ℤ)).toNat

lemma integralEstimate_eq (G : Input) (hn : 2≤G.n) : integralEstimate G=estimate G := by
  simp only [integralEstimate,estimate,integralR_eq G hn]

def integralApproximate (G : Input) : ℕ :=
  if G.n=0 then 1 else
  if Odd G.n then 0 else
  if G.n=2 then rawMultiplicity G 0 1 else
  if (covered G).card<G.n then 0 else integralEstimate G

lemma integralApproximate_eq (G : Input) : integralApproximate G=approximate G := by
  unfold integralApproximate approximate
  split_ifs with hzero hodd htwo hguard
  any_goals rfl
  apply integralEstimate_eq
  have hne : G.n≠1 := by intro h; rw [h] at hodd; exact hodd (by decide)
  omega

lemma integralApproximate_correct (G : Input) :
    integralApproximate G≤count G ∧ count G≤2^(9*G.n)*integralApproximate G ∧
      (integralApproximate G=0 ↔ count G=0) := by
  rw [integralApproximate_eq]
  exact approximate_correct G

end BinaryMatching.Algorithm
end

end OAI
