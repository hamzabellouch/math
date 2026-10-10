import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifier

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (zeroWord a).net.count ≤ a.net.count+97*n+21 := by
  have h := equalOn_count a (wordConstant (n:=k) (BitVec.ofNat n 0))
  rw [wordConstant_count] at h
  dsimp [zeroWord]
  omega

lemma primeOrZero_count {k n : ℕ} (a : BooleanNetwork k n) :
    (primeOrZero a).net.count ≤ 2*a.net.count+146*n+35+rootWidth n+primalityBound n := by
  have h₁ := zeroWord_count a
  have h₂ := primeWord_count n
  simp only [primeOrZero,count_bor,count_comp]
  omega

lemma paddedPair_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (paddedPair a b).net.count ≤ 2*a.net.count+2*b.net.count+242*n+57 := by
  have h₁ := zeroWord_count a
  have h₂ := zeroWord_count b
  have h₃ := wordLe_count a b
  simp only [paddedPair,count_bor,count_band,count_bnot]
  omega

lemma unpadWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (unpadWord a).net.count ≤ 2*a.net.count+105*n+21 := by
  have h := zeroWord_count a
  simp only [unpadWord,wordMux_count,wordConstant_count]
  omega

lemma productNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as, a.net.count≤c) :
    (productNet as).net.count≤as.length*(c+90*w*w+14*w+6)+w := by
  induction as with
  | nil => simp [productNet,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hb := ih (fun b hb => h b (by simp [hb]))
    have hm := mul_count w
    simp only [productNet,count_comp,count_pair,List.length_cons]
    nlinarith

abbrev candidateProductBound (n c : ℕ) :=
  n*(2*c+105*n+21+rootWidth n+90*rootWidth n*rootWidth n+14*rootWidth n+6)+rootWidth n

lemma candidateProduct_count {k n c : ℕ} (as : Fin n→BooleanNetwork k n)
    (h : ∀ i, (as i).net.count≤c) :
    (candidateProduct as).net.count≤candidateProductBound n c := by
  have hh := productNet_count (c:=2*c+105*n+21+rootWidth n)
    (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have h₁ := unpadWord_count (as i)
      have h₂ := resizeWord_count n (rootWidth n)
      have h₃ := h i
      simp only [count_comp]
      omega)
  simpa only [candidateProduct,candidateProductBound,List.length_ofFn] using hh

abbrev factorVerifierBound (n c : ℕ) :=
  n*(2*c+146*n+35+rootWidth n+primalityBound n+1)+1+
  (n*n*(4*c+242*n+58)+1)+1+
  (candidateProductBound n c+c+rootWidth n+96*rootWidth n+21)+1

lemma factorVerifierOn_count {k n c : ℕ} (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (hN : N.net.count≤c) (ha : ∀ i, (as i).net.count≤c) :
    (factorVerifierOn N as).net.count≤factorVerifierBound n c := by
  have h₁ := all_count (c:=2*c+146*n+35+rootWidth n+primalityBound n)
    (List.ofFn (fun i => primeOrZero (as i))) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      have := primeOrZero_count (as i)
      have := ha i
      omega)
  have h₂ := all_count (c:=4*c+242*n+57)
    (List.ofFn (fun i : Fin (n*n) =>
      if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
      else constant true)) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      by_cases hij : (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) =
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2) := ite_eq_left hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have := paddedPair_count (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        have := ha (finProdFinEquiv.symm i).1
        have := ha (finProdFinEquiv.symm i).2
        omega
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) = (constant (n:=k) true) := ite_eq_right hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have ht : (constant (n:=k) true).net.count=1 := rfl
        omega)
  have h₃ := equalOn_count (candidateProduct as) (N.comp (resizeWord n (rootWidth n)))
  have h₄ := candidateProduct_count as ha
  have h₅ := resizeWord_count n (rootWidth n)
  simp only [List.length_ofFn] at h₁ h₂
  rw [show 4*c+242*n+57+1 = 4*c+242*n+58 by omega] at h₂
  simp only [count_comp] at h₃
  simp only [factorVerifierOn,count_band]
  dsimp [factorVerifierBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
