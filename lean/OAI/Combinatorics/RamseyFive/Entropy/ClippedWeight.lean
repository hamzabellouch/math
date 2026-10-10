import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.LargeValueCount
import OAI.Combinatorics.RamseyFive.Iteration.Scale

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def clippedWeight {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) : Option (Option J)→ℙ K (Dual K V)→ℝ
  | none,H => if H∈exceptional S C then 1 else 0
  | some j,H => min 1 ((deviation S C j H)^2)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma clippedWeight_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option (Option J)) (H : ℙ K (Dual K V)) :
    0≤clippedWeight S C j H ∧ clippedWeight S C j H≤1 := by
  cases j with
  | none => simp only [clippedWeight]; split <;> norm_num
  | some j => exact ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

lemma clippedWeight_sum_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option (Option J),∑ H,clippedWeight S C j H)≤
      50000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  rw [Fintype.sum_option]
  have hi : (∑ H,clippedWeight S C none H)=((exceptional S C).card:ℝ) := by
    simp [clippedWeight]
  rw [hi]
  have hc : (∑ j : Option J,∑ H,clippedWeight S C (some j) H)≤
      ∑ j : Option J,∑ H,(deviation S C j H)^2 :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun H _ => min_le_right _ _
  have he := exceptional_card_bound hdim hd S C hS hC
  have hv := total_deviation_bound hdim hd S C hS hC
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K) hB]

lemma mean_ratio_le {d : ℕ} (hd : 1≤d) :
    ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  have he : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 :=
    by exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  nlinarith

noncomputable def irregular {d : ℕ} {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (ξ : ℝ) : Finset (ℙ K V) :=
  Finset.univ.filter fun x => ∃ j : Option (Option J),
    scale (K:=K) d S.card*Real.exp ξ < weightOnPencil (clippedWeight S C j) x

theorem irregular_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card)
    {ξ : ℝ} (hξ : 100000≤Real.exp ξ) :
    ((irregular (d:=d) S C ξ).card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*ξ) := by
  let B : ℝ := scale (K:=K) d S.card
  let w := clippedWeight S C
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hB : 0<B := by dsimp [B,scale]; positivity
  have hw : ∀ j H,0≤w j H := fun j H => (clippedWeight_bounds S C j H).1
  have htotal := clippedWeight_sum_bound hdim hd S C hS hC
  have hmean (j : Option (Option J)) :
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ H,w j H) ≤ B*Real.exp ξ/2 := by
    have hs : (∑ H,w j H)≤∑ i : Option (Option J),∑ H,w i H :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun H _ => hw i H) (Finset.mem_univ j)
    have hc : ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≥0 := by positivity
    calc
      _ ≤ (1/(Nat.card K:ℝ))*(∑ H,w j H) :=
        mul_le_mul_of_nonneg_right (mean_ratio_le (K:=K) hd) (Finset.sum_nonneg fun H _ => hw j H)
      _ ≤ (1/(Nat.card K:ℝ))*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left (hs.trans htotal) (by positivity)
      _ = 50000*B := by field_simp
      _ ≤ _ := by nlinarith
  have hr := family_irregular_count hdim hd w hw
    (fun j H => (clippedWeight_bounds S C j H).2) (B*Real.exp ξ) (by positivity) hmean
  have hcard : ((irregular (d:=d) S C ξ).card:ℝ)≤
      ((Finset.univ.filter fun x : ℙ K V => ∃ j : Option (Option J),
        B*Real.exp ξ≤weightOnPencil (w j) x).card:ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj.le⟩
  have hp : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  have he : (Nat.card K:ℝ)^d=B*S.card := by dsimp [B,scale]; field_simp
  have hb : ((irregular (d:=d) S C ξ).card:ℝ)*(B*Real.exp ξ)^2≤
      200000*(S.card:ℝ)*B^2 := by
    calc
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(∑ j,∑ H,w j H) :=
        (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)).trans hr
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by rw [show 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B)=
        200000*((Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ))*B by ring,hp,he]; ring
  have hb' : ((irregular (d:=d) S C ξ).card:ℝ)*(Real.exp ξ)^2≤200000*(S.card:ℝ) := by
    rw [mul_pow] at hb
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hB)).mp
    nlinarith only [hb]
  have hb'' := (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos ξ))).mpr hb'
  have heq : 200000*(S.card:ℝ)*Real.exp (-2*ξ)=
      200000*(S.card:ℝ)/(Real.exp ξ)^2 := by
    rw [←Real.exp_nat_mul,show -2*ξ=-(2*ξ) by ring,Real.exp_neg]
    norm_num
    ring
  rw [heq]
  exact hb''

end SharpRamseyFive.ScoreRegularity

end OAI
