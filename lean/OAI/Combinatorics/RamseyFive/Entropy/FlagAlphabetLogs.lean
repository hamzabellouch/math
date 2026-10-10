import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.StageState
import OAI.Combinatorics.RamseyFive.Marking.AllWindowBounds
import OAI.Combinatorics.RamseyFive.Entropy.Rectangle

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_card_le_two (hd : finrank K V=5) :
    (Fintype.card (ℙ K V):ℝ)≤2*(Nat.card K:ℝ)^4 := by
  have he : (Fintype.card (ℙ K V):ℝ)=∑i∈Finset.range 5,(Nat.card K:ℝ)^i := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hd]
    push_cast
    rfl
  rw [he]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have ht:=q_mul_geometric_bound (Nat.card K:ℝ) hq 5
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hh : (Nat.card K:ℝ)*(∑i∈Finset.range 5,(Nat.card K:ℝ)^i)≤
      (Nat.card K:ℝ)*(2*(Nat.card K:ℝ)^4) := by nlinarith [ht]
  exact (mul_le_mul_iff_right₀ hq0).mp hh

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_log_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 0≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (ℙ K V))≤4*σ+Real.log 2 := by
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hlog : Real.log (2*(Nat.card K:ℝ)^4)=4*σ+Real.log 2 := by
    rw [Real.log_mul (by norm_num) (pow_pos hq0 _).ne',Real.log_pow,←hq,Real.log_exp]
    ring
  have ht:=log_card_of_card_bound (Finset.univ : Finset (ℙ K V))
    (2*(Nat.card K:ℝ)^4) (4*σ+Real.log 2) (by simpa using point_card_le_two hd)
    (by have := Real.log_nonneg (show (1:ℝ)≤2 by norm_num);positivity) hlog.le
  simpa only [Finset.card_univ] using ht

omit [FiniteDimensional K V] in
lemma flagPair_log_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 0≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (FlagPair K V))≤8*σ+Real.log 4 := by
  have hp:=point_card_le_two hd
  have hb:=point_card_le_two (K:=K) (V:=Dual K V) (by simpa using hd)
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hcap : (Fintype.card (FlagPair K V):ℝ)≤4*(Nat.card K:ℝ)^8 := by
    have hh:=mul_le_mul hp hb (Nat.cast_nonneg _) (by positivity)
    simpa only [FlagPair,Fintype.card_prod,Nat.cast_mul] using hh.trans_eq (by ring)
  have hlog : Real.log (4*(Nat.card K:ℝ)^8)=8*σ+Real.log 4 := by
    rw [Real.log_mul (by norm_num) (pow_pos hq0 _).ne',Real.log_pow,←hq,Real.log_exp]
    ring
  have ht:=log_card_of_card_bound (Finset.univ : Finset (FlagPair K V))
    (4*(Nat.card K:ℝ)^8) (8*σ+Real.log 4) (by simpa using hcap)
    (by have := Real.log_nonneg (show (1:ℝ)≤4 by norm_num);positivity) hlog.le
  simpa only [Finset.card_univ] using ht

lemma incidentFlag_log_card (hd : finrank K V=5) (σ : ℝ) (hq : Real.exp σ=Nat.card K) :
    7*σ≤Real.log (Fintype.card (RectangleGeometry.Flag (K:=K) (V:=V))) := by
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hh : (Nat.card K:ℝ)^7≤Fintype.card (RectangleGeometry.Flag (K:=K) (V:=V)) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using RectangleGeometry.card_flags_lower hd)
  have ht:=Real.log_le_log (pow_pos hq0 7) hh
  simpa only [Real.log_pow,←hq,Real.log_exp,Nat.cast_ofNat] using ht
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section

lemma log_choose_le (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    Real.log (N.choose n)≤(n:ℝ)*(Real.log N-Real.log n+1) := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have h1:=Real.log_le_log hc (Nat.choose_le_pow_div (α:=ℝ) n N)
  rw [Real.log_div (pow_pos hN _).ne' hf.ne',Real.log_pow] at h1
  have h2:=Real.log_le_log (div_pos (pow_pos hp _) hf)
    (Real.pow_div_factorial_le_exp (n:ℝ) hp.le n)
  rw [Real.log_div (pow_pos hp _).ne' hf.ne',Real.log_pow,Real.log_exp] at h2
  nlinarith

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω] [Nonempty α]
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

omit [Fintype β] [Nonempty α] in
lemma SelectedStream.density_pos (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    0<S.density := by
  have hx : 0<∑ s,map S.law S.stream s := by rw [(map S.law S.stream).sum_one]; norm_num
  obtain ⟨s,_,hs⟩:=Finset.sum_pos_iff_of_nonneg (fun s _=>(map S.law S.stream).nonneg s) |>.mp hx
  have hp:=lt_of_lt_of_le hs (S.density_bound s)
  exact (div_pos_iff.mp hp).resolve_right
    (fun h=>(pow_nonneg (Nat.cast_nonneg _) _).not_gt h.2) |>.1

theorem SelectedStream.entropy_lower_explicit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (hn : 0<n) (hnN : n≤N) :
    (n:ℝ)*(Real.log (Fintype.card α)-Real.log N+Real.log n-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hα : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have hd : 0<2*S.density := mul_pos (by norm_num) S.density_pos
  have h:=S.entropy_lower hnN
  rw [Real.log_div (mul_pos hd hc).ne' (pow_pos hα _).ne',
    Real.log_mul hd.ne' hc.ne',Real.log_pow] at h
  have hb:=log_choose_le N n hn hnN
  apply le_trans _ h
  have hh:=add_le_add_right (neg_le_neg hb)
    ((n:ℝ)*Real.log (Fintype.card α)-Real.log (2*S.density))
  convert hh using 1 <;> ring

theorem SelectedStream.flag_entropy_lower (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ : ℝ) (hσ : 0<σ) (hn : 0<n) (hnN : n≤N)
    (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ) :
    4*σ*n+(n:ℝ)*(Real.log n-σ-Real.log σ-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hlogN:=Real.log_le_log hNpos hN
  rw [Real.log_mul (Real.exp_pos _).ne' hσ.ne',Real.log_exp] at hlogN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  have h:=S.entropy_lower_explicit hn hnN
  nlinarith

theorem SelectedStream.flag_entropy_lower_fraction
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ η c C : ℝ) (hσ : 0<σ) (hc : 0<c) (hC : S.density≤C)
    (hn : 0<n) (hnN : n≤N) (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ)
    (hlen : c*Real.exp σ*σ^(1+η)≤n) :
    4*σ*n+η*n*Real.log σ+(n:ℝ)*(Real.log c-1)-Real.log (2*C)≤
      entropy (map S.law S.tuple) := by
  have hp : 0<c*Real.exp σ*σ^(1+η) := mul_pos (mul_pos hc (Real.exp_pos _))
    (Real.rpow_pos_of_pos hσ _)
  have hlogn:=Real.log_le_log hp hlen
  rw [Real.log_mul (mul_pos hc (Real.exp_pos _)).ne'
      (Real.rpow_pos_of_pos hσ _).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp,
    Real.log_rpow hσ] at hlogn
  have hlogC:=Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) S.density_pos)
    (mul_le_mul_of_nonneg_left hC (by norm_num))
  have h:=S.flag_entropy_lower σ hσ hn hnN hα hN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
