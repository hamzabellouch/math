import OAI.Computability.MeanPayoff.WinnerCorrespondence

namespace OAI

namespace MeanPayoff.Label

def callBound (s H B : ℕ) : ℕ := (H+1)*(1+H*s)^B

theorem callBound_pos (s H B : ℕ) : 0 < callBound s H B := by
  unfold callBound
  positivity

theorem callBound_mono {s H B s' H' B' : ℕ}
    (hs : s ≤ s') (hH : H ≤ H') (hB : B ≤ B') :
    callBound s H B ≤ callBound s' H' B' := by
  unfold callBound
  apply Nat.mul_le_mul (by omega)
  exact (Nat.pow_le_pow_left (by gcongr) B).trans
    (Nat.pow_le_pow_right (by omega) hB)

theorem callBound_step (s H B : ℕ) :
    1 + callBound s H (B+1) + s*callBound s H B ≤ callBound s (H+1) (B+1) := by
  let x := 1+H*s
  let y := 1+(H+1)*s
  have hxy : x ≤ y := by dsimp [x,y]; gcongr; omega
  have hp : x^B ≤ y^B := Nat.pow_le_pow_left hxy B
  have hq : (x+s)*x^B ≤ y^(B+1) := by
    rw [pow_succ]
    have he : x+s=y := by dsimp [x,y]; ring
    rw [he, Nat.mul_comm]
    exact Nat.mul_le_mul_right y hp
  have hy : 1 ≤ y^(B+1) := Nat.one_le_pow _ _ (by dsimp [y]; omega)
  have hh := Nat.mul_le_mul_left (H+1) hq
  change 1+(H+1)*x^(B+1)+s*((H+1)*x^B) ≤ (H+1+1)*y^(B+1)
  rw [pow_succ]
  nlinarith only [hh,hy]

theorem down_budget {n : ℕ} {a b : Fin n → ℚ}
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ¬∀ i, 1<a i*b i) :
    budget a (fun i => 4/3*b i) ha (fun i => mul_pos (by norm_num) (hb i)) <
    budget a b ha hb := by
  apply budget_decreases ha hb ha _ hbase
  intro i
  have h := mul_pos (ha i) (hb i)
  nlinarith only [h]

theorem up_budget {n : ℕ} {a b : Fin n → ℚ}
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ¬∀ i, 1<a i*b i) :
    budget (fun i => 4/3*a i) b (fun i => mul_pos (by norm_num) (ha i)) hb <
    budget a b ha hb := by
  apply budget_decreases ha hb _ hb hbase
  intro i
  have h := mul_pos (ha i) (hb i)
  nlinarith only [h]

theorem cont_budget {n : ℕ} {a b : Fin n → ℚ}
    (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hbase : ¬∀ i, 1<a i*b i)
    (labels : Fin n → Bool) :
    budget (reweight a labels) (reweight b (fun i => !(labels i)))
      (reweight_pos ha _) (reweight_pos hb _) < budget a b ha hb := by
  apply budget_decreases ha hb _ _ hbase
  intro i
  rw [reweight_product]

theorem initial_budget_le (G : Game) :
    budget (uniformMass G) (uniformMass G) (uniformMass_pos G) (uniformMass_pos G) ≤
      6*Nat.clog 2 (G.n+1) := by
  apply Nat.find_min'
  intro i
  have hn : (0:ℚ)<G.n := Nat.cast_pos.mpr G.positive
  have hk : G.n+1 ≤ 2^Nat.clog 2 (G.n+1) := Nat.le_pow_clog (by norm_num) _
  have hkq : (G.n:ℚ)+1 ≤ (2:ℚ)^Nat.clog 2 (G.n+1) := by exact_mod_cast hk
  have hp : (2:ℚ)^Nat.clog 2 (G.n+1) ≤ ((32/25:ℚ)^3)^Nat.clog 2 (G.n+1) := by
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
  have hsq : (G.n:ℚ)^2 < (32/25:ℚ)^(6*Nat.clog 2 (G.n+1)) := by
    have hlt : (G.n:ℚ)<((32/25:ℚ)^3)^Nat.clog 2 (G.n+1) := by linarith
    have hh := pow_lt_pow_left₀ hlt hn.le (by norm_num : (2:ℕ)≠0)
    rw [←pow_mul,←pow_mul] at hh
    convert hh using 1; congr 1
    all_goals omega
  dsimp [uniformMass]
  have hden : 0 < (G.n:ℚ)*(G.n:ℚ) := mul_pos hn hn
  rw [one_div_mul_one_div, mul_one_div, lt_div_iff₀ hden]
  nlinarith only [hsq]

end MeanPayoff.Label

end OAI
