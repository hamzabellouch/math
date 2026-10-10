import Mathlib
import OAI.Combinatorics.RamseyFive.Streams.SelectedLength

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_log_one_add_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (1+Fintype.card (ℙ K V))≤6*σ := by
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hp:=point_card_le_two hd
  have hh : (1:ℝ)+Fintype.card (ℙ K V)≤3*(Nat.card K:ℝ)^4 := by
    have hh : (1:ℝ)≤(Nat.card K:ℝ)^4 := one_le_pow₀ hq1
    linarith
  have ht:=Real.log_le_log (by positivity : (0:ℝ)<1+Fintype.card (ℙ K V)) hh
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,←hq,Real.log_exp] at ht
  have hl : Real.log 3≤2 := by have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3);linarith
  norm_num only [Nat.cast_ofNat] at ht
  linarith
omit [FiniteDimensional K V] in
lemma expensiveBound_coarse [Fintype (ℙ K (Dual K (Dual K V)))] (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    expensiveBound K V≤9600*Real.exp σ*σ := by
  have ha:=point_log_one_add_card hd σ hσ hq
  have hb:=point_log_one_add_card (K:=K) (V:=Dual K V) (by simpa using hd) σ hσ hq
  unfold expensiveBound
  rw [←hq]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb ha) (by positivity : (0:ℝ)≤800*Real.exp σ)]

theorem eventually_stream_cheap_entropy {η : ℝ} (hη : 0<η) (c C : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (Ω α β : Type) [Fintype Ω] [Fintype α] [Fintype β] [Nonempty α],
    ∀ (N n : ℕ) (admissible : (Fin N→α)→Prop) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible),
      1≤σ→7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      (n:ℝ)*(4*σ+Real.log 153)≤entropy (map S.law S.tuple) := by
  have ht : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  have he : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop (Real.log 153+2-Real.log c),
    he.eventually_ge_atTop (Real.log (2*C))] with σ ht he
  intro Ω α β _ _ _ _ N n admissible S hσ hα hN hlen hC
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hn : 0<n := by
    have hh : 0<(n:ℝ) := (by positivity : 0<c*Real.exp σ*σ^(1+η)).trans_le hlen
    exact_mod_cast hh
  have hlog : Real.log (2*C)≤n := by
    have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤c*Real.exp σ)
    nlinarith
  have hb:=S.flag_entropy_lower_fraction σ η c C hs hc hC hn S.length_le_source hα hN hlen
  have hh:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg n)
  nlinarith
end
end SharpRamseyFive.Marking

end OAI
