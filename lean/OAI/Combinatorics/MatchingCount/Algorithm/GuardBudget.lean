import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.GuardBits

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open BitComplexity Amplification

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma oneBits_le_trial (p : Trial.Parameters G) : oneBits p ≤ p.K*stageBits p := by
  have hk : 1≤p.K := p.K_pos
  have hs : 1≤p.S := p.S_pos
  unfold stageBits
  have h := Nat.mul_le_mul hk hs
  have hh := Nat.mul_le_mul_right (oneBits p) h
  simpa only [one_mul, Nat.mul_assoc] using hh
lemma guardedBits_le (p : Trial.Parameters G) : guardedBits p≤17*(p.K*stageBits p) := by
  unfold guardedBits guardBits
  have h := Nat.mul_le_mul_left 16 (oneBits_le_trial p)
  omega
lemma guardedAmplifiedBits_le (p : Trial.Parameters G) (δ : ℚ) :
    guardedAmplifiedBits p δ≤17*amplifiedBits p δ := by
  have h := Nat.mul_le_mul_left (2*halfRepetitions δ+1) (guardedBits_le p)
  simpa only [guardedAmplifiedBits, amplifiedBits, Nat.mul_left_comm, Nat.mul_assoc] using h
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitComplexity
open FiniteTrial Trial

theorem polynomial_guarded_bits : ∃ C d : ℕ, ∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (hn : 2 ≤ G.n) (hev : Even G.n) (e δ : ℚ) (he : 0<e) (he1 : e<1), G.n ≤ 2*G.edges.card →
    guardedAmplifiedBits (parameters G hn hev e he he1) δ ≤ timeBound C d G e δ := by
  obtain ⟨C,d,h⟩:=polynomial_fair_bits
  refine ⟨17*C,d,fun G _ hn hev e δ he he1 hs=>?_⟩
  apply (guardedAmplifiedBits_le _ δ).trans
  have hh := Nat.mul_le_mul_left 17 (h G hn hev e δ he he1 hs)
  simpa only [timeBound,Nat.mul_assoc] using hh
end MatchingFPRAS.BitComplexity

namespace MatchingFPRAS.FiniteTrial
open BitComplexity Variation Finset
open scoped Classical

lemma padded_guarded_success {G : GraphInput} [Nontrivial (Fin G.n)]
    (p : Trial.Parameters G) (δ : ℚ) (B : ℕ) (ht : guardedAmplifiedBits p δ≤B)
    (hz : 0<Z G) (hd : 0<δ) :
    ((univ.filter (fun b=>Accurate p (padSampler ht (guardedAmplifiedBitOutput p δ) b))).card:ℚ)/
        (2:ℚ)^B≥1-δ := by
  rw [padSampler_success]
  exact guardedAmplifiedBitOutput_success p hz δ hd

theorem guarded_scheduled_fair_tapes : ∃ C d : ℕ, 0<C ∧
    ∀ (G : GraphInput) [Nontrivial (Fin G.n)] (_ : 2≤G.n) (_ : Even G.n)
      (e δ : ℚ) (_ : 0<e) (_ : e<1), G.n≤2*G.edges.card →
    ∃ f : (Fin (timeBound C d G e δ) → Bool) → ℚ,
      (∀ b,0≤f b) ∧ (Z G=0 → ∀ b,f b=0) ∧ (0<δ →
        ((univ.filter (fun b=>(1-e)*(Z G:ℚ)≤f b ∧ f b≤(1+e)*(Z G:ℚ))).card:ℚ) /
          (2:ℚ)^(timeBound C d G e δ)≥1-δ) := by
  obtain ⟨C,d,h⟩:=polynomial_guarded_bits
  refine ⟨C+1,d,by omega,fun G _ hn hev e δ he he1 hs=>?_⟩
  let p:=parameters G hn hev e he he1
  have ht : guardedAmplifiedBits p δ ≤ timeBound (C+1) d G e δ := by
    exact (h G hn hev e δ he he1 hs).trans (Nat.mul_le_mul_right _ (by omega))
  let f:=padSampler ht (guardedAmplifiedBitOutput p δ)
  have hz : Z G=0 → ∀ b,f b=0 := fun hZ b => guardedAmplifiedBitOutput_zero p hZ δ _
  refine ⟨f,fun b=>guardedAmplifiedBitOutput_nonneg p δ _,hz,fun hd=>?_⟩
  by_cases hZ : Z G=0
  · have hf : (univ.filter (fun b=>(1-e)*(Z G:ℚ)≤f b ∧ f b≤(1+e)*(Z G:ℚ)))=univ := by
      ext b
      simp [hZ,hz hZ b]
    rw [hf,card_univ]
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    rw [div_self (by positivity : (2:ℚ)^timeBound (C+1) d G e δ≠0)]
    linarith
  · convert padded_guarded_success p δ _ ht (Nat.pos_of_ne_zero hZ) hd using 3
    congr 1
    ext b
    simp only [mem_filter,mem_univ,true_and]
    rfl
end MatchingFPRAS.FiniteTrial

end OAI
