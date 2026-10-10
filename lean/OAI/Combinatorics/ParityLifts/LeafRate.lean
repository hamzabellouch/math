import OAI.Combinatorics.ParityLifts.SparseRates

namespace OAI

namespace ParityWL.Complexity

noncomputable def leafSlope (t r : ℕ) : ℝ := 3*(densityFactor r : ℝ)/t

lemma leafSlope_nonneg (t r : ℕ) : 0 ≤ leafSlope t r := by unfold leafSlope; positivity

lemma ExpBound.scale {f : ℕ → ℝ} {r : ℝ} (h : ExpBound f r) (C : ℝ) (hC : 0 ≤ C) :
    ExpBound (fun n => C*f n) r := by simpa using (ExpBound.const C hC).mul h

lemma ExpBound.add_const {f : ℕ → ℝ} {r : ℝ} (h : ExpBound f r) (hr : 0 ≤ r)
    (C : ℝ) (hC : 0 ≤ C) : ExpBound (fun n => f n+C) r :=
  h.add_same ((ExpBound.const C hC).mono_rate hr)

lemma nat_two_exp_cast (E q : ℕ) : ((2^(E*q) : ℕ) : ℝ)=(2 : ℝ)^((E : ℝ)*q) := by
  rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,Nat.cast_mul]

lemma cost_mono (T U V W A B : ℝ) (d : ℕ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hA : 0 ≤ A) (ht : T ≤ U) (hv : V ≤ W) :
    T+A*(T+V+1)^d+B+2 ≤ U+A*(U+W+1)^d+B+2 := by
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ T+V+1)
    (show T+V+1 ≤ U+W+1 by linarith) d
  nlinarith [mul_le_mul_of_nonneg_left hp hA]

lemma leafTime_rate : ∃ E : ℕ, 0 < E ∧ ∀ t : ℕ, ∀ [NeZero t], ∀ R : ℕ,
    ∃ T : ℕ → ℝ, ExpBound T ((E : ℝ)*leafSlope t R) ∧
      ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
        F.length ≤ sparseDensity R N → (leafTime t F : ℝ) ≤ T N := by
  obtain ⟨E,hE,hB⟩ := leafOutput_bound
  refine ⟨E,hE,?_⟩
  intro t _ R
  obtain ⟨C,d,hC,hB⟩ := hB t (Nat.pos_of_neZero t)
  let T : ℕ → ℝ := fun N => C*(literalSizeBound N+1 : ℝ)^d*
    2^((E : ℝ)*(leafSlope t R*N+6))
  refine ⟨T,?_,?_⟩
  · have hp := sparseSize_rate.add_same (ExpBound.const 1 (by norm_num))
    have hp' := (hp.polypow d).scale (C : ℝ) (Nat.cast_nonneg _)
    simpa only [zero_add] using hp'.mul (ExpBound.affine_exp_mul E (leafSlope t R) 6)
  · intro N F hsz hlen
    have ht := hB F
    have hc : (leafTime t F : ℝ) ≤ C*((treeEncode F).size+1 : ℝ)^d*
        (2 : ℝ)^((E : ℝ)*leafWords t F) := by
      unfold leafTime
      rw [←nat_two_exp_cast]
      exact_mod_cast ht
    have hq := sparse_leafWords_bound t R N (Nat.pos_of_neZero t) F hlen
    have hsz' : ((treeEncode F).size : ℝ) ≤ literalSizeBound N := by exact_mod_cast hsz
    apply hc.trans
    dsimp only [T]
    gcongr
    · norm_num
    · exact hq

lemma leafCost_rate : ∃ P : ℕ, 0 < P ∧ ∀ t : ℕ, ∀ [NeZero t], ∀ R : ℕ,
    ∀ M : Machine, ∀ C r : ℝ, 0 < C → 0 ≤ r →
    ∃ W : ℕ → ℝ, ExpBound W ((P : ℝ)*(r+1)*leafSlope t R) ∧
      ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
        F.length ≤ sparseDensity R N → leafCost t M C r F ≤ W N := by
  obtain ⟨E,hE,hT⟩ := leafTime_rate
  let P := (simulationDegree+1)*(E+1)
  refine ⟨P,by dsimp [P]; positivity,?_⟩
  intro t _ R M C r hC hr
  obtain ⟨T,hT,hTF⟩ := hT t R
  let s := leafSlope t R
  have hs : 0 ≤ s := leafSlope_nonneg _ _
  let U : ℕ → ℝ := fun N => C*2^(r*(s*N+6))
  have hU : ExpBound U (r*s) := (ExpBound.affine_exp_mul r s 6).scale C hC.le
  let W : ℕ → ℝ := fun N => T N+simulationCoefficient M*(T N+U N+1)^simulationDegree+negateCost+2
  have ha : 0 ≤ (E : ℝ)*s := by positivity
  have hb : 0 ≤ r*s := by positivity
  have hinner := (hT.add hU ha hb).add_const (by positivity) 1 (by norm_num)
  have hpow := (hinner.pow simulationDegree).scale (simulationCoefficient M) (Nat.cast_nonneg _)
  have hW := ((hT.add hpow ha (by positivity)).add_const (by positivity) negateCost (Nat.cast_nonneg _)).add_const (by positivity) 2 (by norm_num)
  refine ⟨W,hW.mono_rate ?_,?_⟩
  · change (E : ℝ)*s+(simulationDegree : ℝ)*((E : ℝ)*s+r*s) ≤ (P : ℝ)*(r+1)*s
    dsimp only [P]
    push_cast
    have h₁ := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) E) hr) hs
    have h₂ := mul_nonneg (Nat.cast_nonneg (α:=ℝ) simulationDegree) h₁
    have h₃ := mul_nonneg hr hs
    nlinarith
  · intro N F hsz hlen
    have ht := hTF N F hsz hlen
    have hq := sparse_leafWords_bound t R N (Nat.pos_of_neZero t) F hlen
    have hu : C*2^(r*leafWords t F) ≤ U N := by
      dsimp only [U]
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left hq hr
    exact cost_mono (leafTime t F) (T N) (C*2^(r*leafWords t F)) (U N)
      (simulationCoefficient M) negateCost simulationDegree (Nat.cast_nonneg _)
      (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _))
      (Nat.cast_nonneg _) ht hu
end ParityWL.Complexity

end OAI
