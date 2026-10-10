import OAI.Computability.SpaceSimulation.Epoch.Nodes

namespace OAI

namespace Fifths
namespace Tour
open Modulus Finset Radix
variable (D : Tour)

attribute [local irreducible] Modulus.chosen Bin.pair

def Required (v : D.Vertex) (z : ℕ) : Prop :=
  let h := D.valueOf (D.header v)
  (∑ y ∈ range (2^D.guesses v),
    (D.offer v z y h : D.circuit.F) *
      ∏ i ∈ range D.N, (D.validAt v z y i h (D.valueOf (D.childrenOf v i)) :
        D.circuit.F)) = (Modulus.augBit D.width (D.valueOf v) z : D.circuit.F)

section
variable (g : D.FiniteWords)
include g

theorem value_bounded (v : D.Vertex) : D.valueOf v < 2^D.width := by
  rw [width,D.powers]
  unfold valueOf
  split
  · apply lt_of_lt_of_le ((D.finite_story g _).2 _)
    exact Nat.pow_le_pow_right D.m_pos (by omega)
  · apply lt_of_lt_of_le (D.log_lt g _ _)
    exact Nat.pow_le_pow_right D.m_pos <| Nat.add_le_add_right
      (Nat.mul_le_mul_right D.k (D.round_le v)) 1

theorem req_array {e i : ℕ} (h : e+1 < D.E) (p : i < D.N) (z : ℕ) :
    D.Required (D.mkV (e+1) i) z := by
  let v := D.mkV (e+1) i
  have f : D.col v = i := D.ac h p
  have k : D.epoch v = e+1 := D.ae h p
  have l : e<D.E := by omega
  let t := e*D.b
  have a : D.valueOf (D.header v) = D.log t D.b := by
    unfold header
    simp only [f,k,p.le,↓reduceIte,Nat.add_sub_cancel]
    exact D.at_history l le_rfl
  have b (j : ℕ) : D.valueOf (D.childrenOf v j) = (D.story t).cells i := by
    unfold childrenOf
    simp only [f,p,↓reduceIte,k,Nat.add_sub_cancel]
    exact D.at_array l p
  have c : D.valueOf v = (D.story (t+D.b)).cells i := by
    rw [show D.valueOf v = _ from D.at_array h p]
    simp [t,add_mul]
  have w := D.replay_true g D.b (D.log_agrees g t D.b) i
  have j : (D.replay i (D.log t D.b) ((D.story t).cells i) D.b).1 =
      (D.story (t+D.b)).cells i := congrArg Prod.fst w
  change D.Required v z
  unfold Required
  simp only [guesses,offer,validAt,f,p,p.le,a,b,c,j,↓reduceIte,pow_zero, Nat.cast_one,
    range_one, sum_singleton]
  simp [D.blocks, apply_ite (fun k : ℕ => (k : D.circuit.F))]

omit g in
theorem log_zero (t : ℕ) : D.log t 0 = (D.story t).ctrl := by
  simp [log,pack]

theorem req_copy {e : ℕ} (h : e+1 < D.E) (z : ℕ) :
    D.Required (D.hV (e+1) 0) z := by
  let v := D.hV (e+1) 0
  have f : D.col v = D.N := D.hc h (Nat.zero_le _)
  have k : D.epoch v = e+1 := D.he h (Nat.zero_le _)
  have l : e<D.E := by omega
  let t := e*D.b
  have a : D.valueOf (D.header v) = D.log t D.b := by
    unfold header; simp only [f,k,le_refl,↓reduceIte,Nat.add_sub_cancel]
    exact D.at_history l le_rfl
  have b : get D.m (D.valueOf (D.header v)) D.b = D.valueOf v := by
    rw [a,D.log_agrees g t D.b D.b le_rfl,show D.valueOf v = _ from
      D.at_history h (Nat.zero_le _)]
    simp [log_zero D,t,add_mul]
  change D.Required v z
  simp [Required,offer,validAt,b,guesses,f]

theorem req_round {e j : ℕ} (l : e < D.E) (h : j+1 ≤ D.k) (z : ℕ) :
    D.Required (D.hV e (j+1)) z := by
  let v := D.hV e (j+1)
  have c : D.col v = D.N + (j+1) := D.hc l h
  have r : D.round v = j+1 := D.hr l h
  have a : D.N < D.col v := by omega
  let t := e*D.b
  have ep : D.epoch v = e := D.he l h
  let n := j*D.k
  let H := D.valueOf (D.header v)
  have Hv : H = D.log t n := by
    unfold H header
    simp only [not_le.mpr a,↓reduceIte,ep,r,Nat.add_sub_cancel]
    exact D.at_history l (show j ≤ D.k by omega)
  let Z := fun y => D.proposal v H y
  have Zv (y) : Z y = D.log t n + D.m^(n+1)*y := by
    simp [Z,proposal,r,Hv,n,Nat.mod_eq_of_lt (D.log_lt g t (j*D.k))]
  let w := D.suffix t n
  have q : Z w = D.log t (n+D.k) := by rw [Zv,D.log_extend]
  have m (i) (p : i<D.N) :
      D.valueOf (D.childrenOf v i) = (D.story t).cells i := by
    unfold childrenOf
    simp only [Nat.not_lt.mpr a.le,a.ne.symm,↓reduceIte,ep]
    exact D.at_array l p
  have p (i y) (u : i<D.N) :
      D.validAt v z y i H (D.valueOf (D.childrenOf v i)) =
        (D.replayOn i (Z y) t (n+D.k)).2.toNat := by
    simp [validAt,Nat.not_lt.mpr a.le,a.ne.symm,replayOn,Z,r,m i u,n,add_mul]
  have offer_bit (y) : D.offer v z y H = Modulus.augBit D.width (Z y) z := by
    simp only [offer,Nat.not_lt.mpr a.le,a.ne.symm,↓reduceIte,Z]
  have s : 2^D.guesses v = D.m^D.k := by
    rw [guesses, ite_eq_right (not_le.mpr a),guessLength,D.powers]
  have tv : D.valueOf v = D.log t (n+D.k) := by
    rw [show D.valueOf v = _ from D.at_history l h]
    simp [t,n,add_mul]
  change D.Required v z
  dsimp only [Required]
  rw [s,sum_eq_single_of_mem w (mem_range.mpr (D.suffix_lt g _ _))]
  · rw [offer_bit w, tv]
    rw [prod_eq_one]
    · rw [mul_one,q]
    · intro i u
      rw [p i w (mem_range.mp u),q,D.replay_true g _ (D.log_agrees g t _) i]
      simp
  intro y b o
  have i : ∃ i < D.N, (D.replayOn i (Z y) t (n+D.k)).2 = false := by
    by_contra! u
    have y₀ : get D.m (Z y) 0 = (D.story t).ctrl := by
      rw [Zv, get_join_zero D.m (n+1) _ _ (by omega)]
      simpa only [Nat.add_zero] using D.log_agrees g t n 0 (by omega)
    have k := D.passes_agree g (n := n+D.k) y₀ (fun i p => ?_) -- placeholder
    · have q' : D.log t (n+D.k) = Z y := D.agrees_log g (by
        rw [Zv]
        rw [show n+D.k+1 = n+1+D.k by omega]
        exact join_lt (D.log_lt g t n) (mem_range.mp b)) k
      apply o
      have g' : D.m^(n+1)*w = D.m^(n+1)*y :=
        Nat.add_left_cancel (show _ from by rw [← Zv, ← Zv, q,q'])
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos D.m_pos _) g').symm
    · exact (Bool.eq_true_of_not_eq_false (u _ p))
  obtain ⟨i,h,k⟩ := i
  rw [prod_eq_zero (mem_range.mpr h),mul_zero]
  rw [p i y h,k]; simp

end

theorem certified (g : D.FiniteWords) : D.circuit.Good := by
  refine ⟨D.value_bounded g, fun v => ?_,fun v => ?_,fun v => ?_⟩
  · change D.guesses v ≤ D.width
    unfold guesses
    split
    · omega
    · apply Nat.mul_le_mul_left
      have := D.k_le; omega
  · intro h
    change D.baseOf v = true at h
    simp only [baseOf,Bool.and_eq_true,decide_eq_true_eq] at h
    change D.valueOf v = D.firstOf v
    unfold firstOf valueOf
    simp only [h.1,zero_mul]
    split
    · rfl
    next e =>
      have q := le_antisymm h.2 (le_of_not_gt e)
      simp [round,q, D.log_zero, story]
  · intro h z _
    change D.Required v z
    change D.baseOf v = false at h
    obtain (⟨e,l,j,b,rfl⟩ | ⟨e,l,j,b,rfl⟩) := D.either v
    · cases e with
      | zero => simp [baseOf,D.ac l b,D.ae l b,b.le] at h
      | succ e => exact D.req_array g l b z
    · cases j with
      | zero =>
        cases e with
        | zero => simp [baseOf,D.hc l b,D.he l b] at h
        | succ e => exact D.req_copy g l z
      | succ j => exact D.req_round g l b z
end Tour
end Fifths

end OAI
