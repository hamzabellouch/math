import OAI.Combinatorics.ParityLifts.ExpBounds

namespace OAI

namespace ParityWL.Complexity

def densityFactor (r : ℕ) : ℕ := 2*(1+r^2+2*(r^4)^2)

lemma sparseDensity_eq (r N : ℕ) : sparseDensity r N=1+densityFactor r*N := by
  simp only [sparseDensity,densityFactor]; ring

lemma ExpBound.polymul {f g : ℕ → ℝ} (hf : ExpBound f 0) (hg : ExpBound g 0) :
    ExpBound (fun n => f n*g n) 0 := by simpa using hf.mul hg

lemma ExpBound.polypow {f : ℕ → ℝ} (hf : ExpBound f 0) (d : ℕ) :
    ExpBound (fun n => f n^d) 0 := by simpa using hf.pow d

lemma sparseSize_rate : ExpBound (fun N => (literalSizeBound N : ℝ)) 0 := by
  have hN : ExpBound (fun N => (N : ℝ)) 0 :=
    (ExpBound.poly 1).mono (fun N => Nat.cast_nonneg N) (by intro N; simp)
  have h1 := ExpBound.const 1 (by norm_num)
  have h2 := ExpBound.const 2 (by norm_num)
  have h3 := ExpBound.const 3 (by norm_num)
  have h4 := ExpBound.const 4 (by norm_num)
  have h6 := ExpBound.const 6 (by norm_num)
  have he := h1.add_same (h4.polymul (((h2.polymul hN).add_same h1).polypow 3) |>.polymul
    (h2.add_same (h3.polymul ((h4.polymul hN).add_same h6))))
  simpa only [literalSizeBound,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    Nat.cast_pow,add_zero,zero_add,mul_zero,zero_mul] using he

lemma ceilWidth_bound (m t : ℕ) (ht : 0<t) :
    (((m+t-1)/t : ℕ) : ℝ) ≤ (m : ℝ)/t+1 := by
  have hmul : ((m+t-1)/t)*t ≤ m+t :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hc : ((((m+t-1)/t : ℕ) : ℝ)) * t ≤ (m : ℝ)+t := by exact_mod_cast hmul
  have ht' : (0 : ℝ)<t := by exact_mod_cast ht
  have he : ((m : ℝ)/t+1)*t=(m : ℝ)+t := by
    rw [add_mul,div_mul_cancel₀ _ (ne_of_gt ht'),one_mul]
  nlinarith

lemma sparse_leafWords_bound (t r N : ℕ) (ht : 0<t) (F : BitFormula)
    (hlen : F.length ≤ sparseDensity r N) :
    (leafWords t F : ℝ) ≤ (3*(densityFactor r : ℝ)/t)*N+6 := by
  have hw := ceilWidth_bound F.length t ht
  have hl : (F.length : ℝ) ≤ 1+(densityFactor r : ℝ)*N := by
    rw [sparseDensity_eq] at hlen
    exact_mod_cast hlen
  have ht' : (0 : ℝ)<t := by exact_mod_cast ht
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  simp only [leafWords,chunkWidth,Nat.cast_mul,Nat.cast_ofNat]
  apply (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 3)).trans
  apply (mul_le_mul_iff_right₀ ht').mp
  field_simp
  nlinarith

lemma ExpBound.affine_exp (a b : ℝ) :
    ExpBound (fun n => (2 : ℝ)^(a*n+b)) a := by
  refine ⟨fun _ => (Real.rpow_pos_of_pos (by norm_num) _).le,
    2^b,Real.rpow_pos_of_pos (by norm_num) _,0,?_⟩
  intro n
  change 2^(a*(n : ℝ)+b)≤2^b*(n+1 : ℝ)^0*2^(a*n)
  rw [pow_zero,mul_one,Real.rpow_add (by norm_num),mul_comm]

lemma ExpBound.affine_exp_mul (a b c : ℝ) :
    ExpBound (fun n => (2 : ℝ)^(a*(b*n+c))) (a*b) := by
  convert ExpBound.affine_exp (a*b) (a*c) using 1
  funext n
  congr 1
  ring

lemma polynomial_program_rate {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → β} (P : PolyProgram α β f) (S : ℕ → ℕ)
    (hS : ExpBound (fun N => (S N : ℝ)) 0) :
    ExpBound (fun N => (P.coefficient*(S N+1)^P.degree : ℕ)) 0 := by
  have h := (ExpBound.const P.coefficient (Nat.cast_nonneg _)).mul
    ((hS.add_same (ExpBound.const 1 (by norm_num))).pow P.degree)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,mul_zero,add_zero] using h
end ParityWL.Complexity

end OAI
