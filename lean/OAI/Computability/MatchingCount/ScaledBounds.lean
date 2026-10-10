import OAI.Computability.MatchingCount.RawOptimizerRows

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
variable {n : ℕ}
private lemma int_two_abs : (2:ℤ).natAbs=2 := rfl

lemma beta_abs_nat (G : Input) (e : Pair G.n) : (beta G e).natAbs ≤ L G := by
  have h := beta_bound G e
  have h' : |beta G e| ≤ (L G:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma indexed_slope_abs (k j : ℕ) (hj : j ≤ k) : (indexedPiece k j).slope.natAbs ≤ k := by
  have hm : indexedPiece k j∈pieces k := by
    rw [pieces_indexed]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩
  have h := piece_slope_bound k _ hm
  have h' : |(indexedPiece k j).slope| ≤ (k:ℤ) := by exact_mod_cast h
  rw [←Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma pieceNumerator_abs (k D j : ℕ) (hj : j ≤ k) (a : ℤ) (ha : a.natAbs ≤ D) :
    (pieceNumerator k D a j).natAbs ≤ (k+1)*D*2^k := by
  have hs := indexed_slope_abs k j hj
  have hp : 2^(k-j) ≤ 2^k := Nat.pow_le_pow_right (by omega) (Nat.sub_le k j)
  unfold pieceNumerator
  refine (Int.natAbs_add_le _ _).trans ?_
  simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
  split_ifs
  · have h₁ := Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul hs ha)
    have h₂ := Nat.mul_le_mul_left D hp
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    nlinarith
  · simpa only [Int.natAbs_zero,Nat.add_zero] using
      (Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul (hs.trans (Nat.le_succ k)) ha))

lemma integralRow_mem (D : ℕ) (a : Table n ℤ) : integralRow D a∈integralRows a := by
  unfold integralRow
  cases h : (integralRows a).argmax (rowNumerator D a) with
  | none => simp [integralRows]
  | some r => exact List.argmax_mem h

lemma integral_row_coeff (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a)
    (e : Pair n) : (r.coeff e).natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl
  · simp [zeroRow]
  · simp only [degreeRow,↓reduceIte]; split_ifs <;> norm_num
  · simp only [degreeRow,Bool.false_eq_true,↓reduceIte]; split_ifs <;> norm_num
  · simp only [cutRow]; split_ifs <;> norm_num

lemma integral_row_constant (a : Table n ℤ) (r : Affine n) (hr : r∈integralRows a) :
    r.constant.natAbs ≤ 1 := by
  rw [integralRows_eq] at hr
  rcases (mem_activeRows a r).mp hr with rfl|⟨v,rfl|rfl⟩|rfl <;>
    simp [zeroRow,degreeRow,cutRow]

lemma rowNumerator_abs (D : ℕ) (a : Table n ℤ) (ha : ∀ e,(entry a e).natAbs ≤ D)
    (r : Affine n) (hr : r∈integralRows a) : (rowNumerator D a r).natAbs ≤ (q n+1)*D := by
  have hs : (∑ e,r.coeff e*entry a e).natAbs ≤ q n*D := by
    calc
      _  ≤  ∑ e,(r.coeff e*entry a e).natAbs := Int.natAbs_sum_le _ _
      _  ≤  ∑ _e : Pair n,D := sum_le_sum fun e _ => by
        rw [Int.natAbs_mul]
        simpa using Nat.mul_le_mul (integral_row_coeff a r hr e) (ha e)
      _ = _ := by simp [q]
  have hc : (r.constant*(D:ℤ)).natAbs ≤ D := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    simpa using Nat.mul_le_mul_right D (integral_row_constant a r hr)
  exact (Int.natAbs_add_le _ _).trans (by nlinarith)

lemma scaledPsi_abs (k D : ℕ) (a : ℤ) (ha : a.natAbs ≤ D) :
    (scaledPsi k D a).natAbs ≤ (k+1)*D*2^k :=
  pieceNumerator_abs k D _ (selectedIndex_le k D a) a ha

lemma scaledSlope_abs (k D : ℕ) (a : ℤ) : (scaledSlope k D a).natAbs ≤ k :=
  indexed_slope_abs k _ (selectedIndex_le k D a)

def operandBound (G : Input) : ℕ :=
  Q G*(q G.n*(K G.n+L G+1)+M₀ G*(q G.n+1))

lemma integralValue_abs (G : Input) (a : Table G.n ℤ)
    (ha : ∀ e,(entry a e).natAbs ≤ D₀ G) (r : Affine G.n) (hr : r∈integralRows a) :
    (integralValue G a r).natAbs ≤ operandBound G := by
  have he (e : Pair G.n) :
      (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs
         ≤ (K G.n+L G+1)*Q G := by
    have h₁ := scaledPsi_abs (K G.n) (D₀ G) (entry a e) (ha e)
    have h₂ : (beta G e*entry a e*2^(K G.n)).natAbs ≤ L G*Q G := by
      simp only [Int.natAbs_mul,Int.natAbs_pow,int_two_abs]
      calc
        _  ≤  L G*D₀ G*2^(K G.n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (beta_abs_nat G e) (ha e))
        _ = _ := by unfold Q; ring
    exact (Int.natAbs_add_le _ _).trans (by unfold Q at *; nlinarith)
  have hs : (∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))).natAbs
       ≤ q G.n*((K G.n+L G+1)*Q G) := by
    calc
      _ ≤ ∑ e,(scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n)).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _e : Pair G.n,(K G.n+L G+1)*Q G := sum_le_sum (fun e _ => he e)
      _ = _ := by simp only [sum_const,card_univ,smul_eq_mul,q]
  have hc : ((M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)).natAbs ≤ M₀ G*(q G.n+1)*Q G := by
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,int_two_abs]
    calc
      _  ≤  M₀ G*((q G.n+1)*D₀ G)*2^(K G.n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rowNumerator_abs _ a ha r hr))
      _ = _ := by unfold Q; ring
  exact (Int.natAbs_sub_le _ _).trans (by unfold operandBound; nlinarith)

lemma integralGradient_abs (G : Input) (a : Table G.n ℤ) (r : Affine G.n)
    (hr : r∈integralRows a) (e : Pair G.n) :
    (integralGradient G a r e).natAbs ≤ K G.n+L G+M₀ G := by
  have h₁ := scaledSlope_abs (K G.n) (D₀ G) (entry a e)
  have h₂ := beta_abs_nat G e
  have h₃ : ((M₀ G:ℤ)*r.coeff e).natAbs ≤ M₀ G := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    simpa using Nat.mul_le_mul_left (M₀ G) (integral_row_coeff a r hr e)
  exact (Int.natAbs_sub_le _ _).trans (by
    have hh := Int.natAbs_add_le (scaledSlope (K G.n) (D₀ G) (entry a e)) (beta G e)
    omega)

lemma integralIterate_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (e : Pair G.n) :
    (entry (integralIterate G t).numerators e).natAbs ≤ D₀ G := by
  rw [integralIterate_table G hn]
  have h := iterate_box G t e
  have hh : |entry (iterate G t).numerators e| ≤ (D₀ G:ℤ) := by rw [abs_of_nonneg h.1]; exact h.2
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

lemma integralBest_abs (G : Input) (hn : 2 ≤ G.n) (t : ℕ) (v : ℤ)
    (hv : v∈(integralIterate G t).best) : v.natAbs ≤ operandBound G := by
  induction t generalizing v with
  | zero => simp [integralIterate,integralInitial] at hv
  | succ t ih =>
    let a := (integralIterate G t).numerators
    let r := integralRow (D₀ G) a
    have hrow : r∈integralRows a := integralRow_mem _ _
    have hval := integralValue_abs G a (integralIterate_abs G hn t) r hrow
    change v∈some ((integralIterate G t).best.elim (integralValue G a r) (max (integralValue G a r))) at hv
    have he := Option.mem_some_iff.mp hv
    subst v
    cases hb : (integralIterate G t).best with
    | none => simpa only [Option.elim_none] using hval
    | some w =>
      have hw := ih w hb
      simp only [Option.elim_some]
      by_cases hh : w ≤ integralValue G a r
      · rwa [max_eq_left hh]
      · rwa [max_eq_right (le_of_not_ge hh)]

lemma operandBound_polynomial (G : Input) (hn : 2 ≤ G.n) :
    operandBound G ≤ 5052*1313^2*(tau G)^27 := by
  have ht := tau_pos G
  have hq := q_le_tau_sq G
  have hkl : K G.n+L G+1 ≤ 102*(tau G)^3 := by
    have hp : 1 ≤ (tau G)^3 := one_le_pow₀ ht
    have hh := K_L_bound G
    omega
  have hq1 : q G.n+1 ≤ 2*(tau G)^2 := by
    have hp : 1 ≤ (tau G)^2 := one_le_pow₀ ht
    omega
  have hsmall : q G.n*(K G.n+L G+1) ≤ 102*(tau G)^9 := by
    calc
      _  ≤  (tau G)^2*(102*(tau G)^3) := Nat.mul_le_mul hq hkl
      _ = 102*(tau G)^5 := by ring
      _  ≤  _ := Nat.mul_le_mul_left _ (tau_pow_mono G (by omega))
  have hlarge : M₀ G*(q G.n+1) ≤ 2424*(tau G)^9 := by
    calc
      _  ≤  (1212*(tau G)^7)*(2*(tau G)^2) := Nat.mul_le_mul (M₀_bound G) hq1
      _ = _ := by ring
  calc
    _  ≤  (2*1313^2*(tau G)^18)*(2526*(tau G)^9) :=
      Nat.mul_le_mul (Q_bound G hn) (by omega)
    _ = _ := by ring

end BinaryMatching.Algorithm
end

end OAI
