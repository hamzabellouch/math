import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.PublicDecoder

namespace OAI

namespace SharpRamseyFive.SubsetEncoding
open scoped Classical BigOperators

lemma log_factorial_lower (n : ℕ) :
    (n:ℝ)*Real.log n-n≤Real.log (n.factorial:ℝ) := by
  by_cases hn : n=0
  · subst n;norm_num
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Stirling.le_log_factorial_stirling hn
  have hp : (1:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hl := Real.log_nonneg hp
  have hl' := Real.log_nonneg hn1
  linarith

lemma log_choose_le (m n : ℕ) (hnm : n ≤ m) :
    Real.log (m.choose n:ℝ)≤(n:ℝ)*(Real.log ((m:ℝ)/n)+1) := by
  by_cases hn : n=0
  · subst n;simp
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmpos : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hn).trans_le hnm
  have hcp : (0:ℝ) < m.choose n := by exact_mod_cast Nat.choose_pos hnm
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.log_le_log hcp (Nat.choose_le_pow_div n m : (m.choose n:ℝ)≤(m:ℝ)^n/n.factorial)
  rw [Real.log_div (pow_ne_zero _ hmpos.ne') hfact.ne',Real.log_pow] at h
  rw [Real.log_div hmpos.ne' hnpos.ne']
  have hf := log_factorial_lower n
  nlinarith

variable {α : Type*} [Fintype α]

abbrev Alphabet (U : Finset α) (n : ℕ) := {A : Finset α // A⊆U ∧ A.card=n}

lemma alphabet_card (U : Finset α) (n : ℕ) :
    Fintype.card (Alphabet U n)=U.card.choose n := by
  classical
  unfold Alphabet
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun A : Finset α=>A⊆U ∧ A.card=n)=U.powersetCard n := by
    ext A;simp
  rw [he,Finset.card_powersetCard]

noncomputable def encode (S U : Finset α) (hSU : S⊆U) : Fin (Fintype.card (Alphabet U S.card)) :=
  Fintype.equivFin (Alphabet U S.card) ⟨S,hSU,rfl⟩

noncomputable def decode (U : Finset α) (n : ℕ) (i : Fin (Fintype.card (Alphabet U n))) : Finset α :=
  ((Fintype.equivFin (Alphabet U n)).symm i).1

lemma decode_encode (S U : Finset α) (hSU : S⊆U) : decode U S.card (encode S U hSU)=S := by
  exact congrArg Subtype.val ((Fintype.equivFin (Alphabet U S.card)).symm_apply_apply ⟨S,hSU,rfl⟩)

theorem small_set_description (S U : Finset α) (hSU : S⊆U)
    (q P : ℝ) (hn : (S.card:ℝ)≤100*q*P) :
    decode U S.card (encode S U hSU)=S ∧
    Real.log (Fintype.card (Alphabet U S.card):ℝ)≤
      100*q*P*(Real.log ((U.card:ℝ)/S.card)+1) := by
  refine ⟨decode_encode S U hSU,?_⟩
  rw [alphabet_card]
  have h := log_choose_le U.card S.card (Finset.card_le_card hSU)
  apply h.trans
  apply mul_le_mul_of_nonneg_right hn
  by_cases hs : S.card=0
  · simp [hs]
  · have hp : (0:ℝ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hp).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
    linarith [Real.log_nonneg hr]

end SharpRamseyFive.SubsetEncoding

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def sizeScoreCutoff (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) : ℕ :=
  ⌈(Nat.card K:ℝ)*Real.exp
    (Real.log ((U.card:ℝ)/n)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4))⌉₊

noncomputable def baseAlphabet (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) : Type _ :=
  if (n:ℝ)≤100*(Nat.card K:ℝ)*P then
    Fin (Fintype.card (Alphabet U n))
  else Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)

noncomputable instance (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) :
    Fintype (baseAlphabet U n P τ) := by
  unfold baseAlphabet
  split <;> infer_instance

noncomputable def baseDecoded (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (m : baseAlphabet U n P τ) : Finset (ℙ K V) := by
  classical
  exact if h : (n:ℝ)≤100*(Nat.card K:ℝ)*P then
    decode U n (cast (by simp only [baseAlphabet,h,ite_true]) m)
  else
    let m' : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) :=
      cast (by simp only [baseAlphabet,h,ite_false]) m
    publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) m'.2 (t m'.1)

omit [Finite K] [FiniteDimensional K V] in
lemma baseDecoded_small (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) (m : Fin (Fintype.card (Alphabet U n))) :
    baseDecoded U n P τ L₀ t (by simpa only [baseAlphabet,hn,ite_true] using m)=decode U n m := by
  simp [baseDecoded,hn]

omit [Finite K] [FiniteDimensional K V] in
lemma baseDecoded_large (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (hn : ¬(n:ℝ)≤100*(Nat.card K:ℝ)*P)
    (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) :
    baseDecoded U n P τ L₀ t (by simpa only [baseAlphabet,hn,ite_false] using m)=
      publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) m.2 (t m.1) := by
  simp [baseDecoded,hn]

lemma base_cost_scalar (q P gap τ : ℝ) (hq : 2≤q) (hP : 1≤P)
    (hgap : 0≤gap) (_hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (2*q) + gap*(2*q*P)+(8*P*τ+Real.log 4)+Real.log (2*q^2) ≤
      20*q*P*(gap+P) := by
  have hp : 0<P := by linarith
  have hq' : 0<q := by linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have hlq := Real.log_le_sub_one_of_pos hq'
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : Real.log (2*q^2)=Real.log 2+2*Real.log q := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq'.ne'),Real.log_pow]
    norm_num
  rw [he]
  have ht := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0:ℝ)≤8*P)
  have hqp : q≤q*P := by nlinarith
  have hpp : q*P≤q*P*P := by nlinarith
  have hgp : 0≤q*P*gap := by positivity
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
