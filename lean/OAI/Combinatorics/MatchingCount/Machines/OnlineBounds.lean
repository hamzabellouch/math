import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineInitialLaw
import OAI.Combinatorics.MatchingCount.Complexity.OnlineInitialCost
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineHistorySize

namespace OAI

namespace MatchingFPRAS.OnlineSourceBounds
open BitComplexity Transport Polynomial TreeTyped

def normBound (x : ℕ) : ℕ :=
  2*x+boundK x+boundN x+boundD x+boundS x+
    tierPolynomial (boundN x) (boundD x) (boundK x)+
    ladderQ (boundN x) (boundD x)+(2*x)^2+3
lemma normBound_polynomial : PolynomiallyBounded normBound := by
  have hn := (PolynomiallyBounded.const 2).mul PolynomiallyBounded.id
  exact ((((((((hn.add boundK_polynomial).add boundN_polynomial).add boundD_polynomial).add boundS_polynomial).add
    (tier_polynomial boundN_polynomial boundD_polynomial boundK_polynomial)).add
    (ladderQ_polynomial boundN_polynomial boundD_polynomial)).add (hn.pow 2)).add (PolynomiallyBounded.const 3))
lemma polynomial_bound {f : ℕ→ℕ} (h : PolynomiallyBounded f) :
    ∃ q : Polynomial ℕ,∀ x,1≤x→f x≤q.eval x := by
  obtain ⟨C,d,h⟩:=h
  exact ⟨Polynomial.C C*Polynomial.X^d,fun x hx=>by simpa using h x hx⟩
variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma norm_le (hn : 2≤G.n) (hev : Even G.n) (ε : ℚ) (he : 0<ε) (he1 : ε<1)
    (x : ℕ) (hnx : G.n≤2*x) (hex : ⌈ε⁻¹⌉₊≤x) (g : ExecutableAdaptive.GraphData) :
    OnlineTrial.sizeNorm (FiniteTrial.parameters G hn hev ε he he1) g≤normBound x+weight g := by
  let p:=FiniteTrial.parameters G hn hev ε he he1
  have hk:=parameters_K_le hn hev ε he he1 x hnx hex
  have hN:=parameters_N_le p x hnx hk
  have hD:=parameters_D_le p x hnx hN
  have hS:=parameters_S_le p x hnx hk hD hex
  have hT : p.T≤tierPolynomial (boundN x) (boundD x) (boundK x) := by
    have ht := endpoint_le_polynomial p.N p.D p.K p.N_pos
    rw [endpoint_eq] at ht
    apply ht.trans
    unfold tierPolynomial
    gcongr
  have hq : p.q≤ladderQ (boundN x) (boundD x) := by
    change ladderQ p.N p.D≤_
    unfold ladderQ ladderL
    gcongr
  have hz : (Z (completeGraph G.n)+1).size≤(2*x)^2+3 := by
    apply (BitArithmetic.complete_count_size G.n).trans
    have hs : G.n.size≤G.n := Nat.size_le.mpr Nat.lt_two_pow_self
    have hd : G.n/2≤G.n := Nat.div_le_self _ _
    calc
      _≤G.n*G.n+3 := by gcongr
      _≤(2*x)^2+3 := by rw [pow_two];gcongr
  unfold OnlineTrial.sizeNorm normBound
  dsimp only [p] at *
  omega

lemma numeric_le (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1)
    (x : ℕ) (hnx : G.n≤2*x) (hex : ⌈ε⁻¹⌉₊≤x) :
    OnlineInitial.configNumeric (OnlineInitial.config (OnlineInitial.sourceSeed (G:=G) ε δ))≤normBound x := by
  let p:=FiniteTrial.parameters G hn hev ε he he1
  rw [OnlineInitial.config_source hn hev ε δ he he1]
  dsimp only [OnlineInitial.configNumeric,OnlineInitial.sourceSeed]
  have hl : (ExecutableAdaptive.graphRep G).1.length=G.n := by simp [ExecutableAdaptive.graphRep]
  rw [hl,OnlineSchedule.ladderSchedule_eq _ _ _ p.N_pos,endpoint_eq,FiniteTrial.sourceD_eq]
  have hs:=norm_le hn hev ε he he1 x hnx hex (ExecutableAdaptive.graphRep G)
  unfold OnlineTrial.sizeNorm at hs
  change G.n+p.K+p.N+p.D+p.T+p.q≤normBound x
  dsimp only [p] at *
  omega
end MatchingFPRAS.OnlineSourceBounds

end OAI
