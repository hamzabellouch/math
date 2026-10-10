import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.HighNumerics
import OAI.Combinatorics.RamseyFive.Decoding.HighRoundNumbers
import OAI.Combinatorics.RamseyFive.Streams.HighSampleContradiction
import OAI.Combinatorics.RamseyFive.Entropy.DeletionNumerics

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open FiniteEntropy
noncomputable section
variable {Ω α β : Type} [Fintype Ω] [Fintype α] [Fintype β]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
omit [Fintype β] in
lemma SelectedStream.length_le_source (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) : n≤N := by
  obtain ⟨z,hz⟩:=S.law.exists_positive
  obtain ⟨e,he⟩:=(mem_occurrences_iff _ _).mp (S.selected z hz)
  have h:=Fintype.card_le_of_injective e e.injective
  simpa only [Fintype.card_fin] using h
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_high_prepared_impossible {η : ℝ} (hη : 0<η) (c C Cb : ℝ)
    (hc : 0<c) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n r' : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→4*σ≤J→
      2 ≤ r' → r' ≤ 4→(∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 4 r')→False := by
  have ha : 3000*beta η<η/2 := by unfold beta;linarith
  filter_upwards [eventually_high_sample_impossible hη c C hc,
    eventually_deletion_budget hη Cb 0 (2/c) (1/1000) hCb le_rfl (by positivity) (by norm_num),
    eventually_high_four_loss hη (1/1000) (by norm_num),eventually_high_geometry hη,
    eventually_stage_scale hη 3000 (c/4) ha (by positivity)] with σ hcontra hdel hfour hgeom hscale
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n r' _ admissible S ctx D J B M P
    hd hσ hq hα hN hlen hC hD hDhi hB hJ hrlo hrhi hcap
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 2≤Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α:=K))
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast hqp
  have hqpos : (0:ℝ)<Nat.card K := by linarith
  have hDpos : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let T:=⌊(Nat.card K:ℝ)*D*σ^(3000*beta η)⌋₊
  let rem:=n-T
  let h:=⌈(Nat.card K:ℝ)*σ^beta η⌉₊
  obtain ⟨hn,hT,hrem,hnrem,hroom,hTlo,hremlo,hhlo,hhhi⟩:=
    high_integer_ranges hη hσ hqr hc hD (by nlinarith [hscale D hDhi]) n (by simpa only [hq] using hlen)
  have hfour':=hfour D (Nat.card K) r' h hD hDhi (by omega) hq hrlo hhlo hhhi
  have hgeom':=hgeom D hDhi
  rw [hq] at hgeom'
  have hbudget:=hdel (Nat.card K) D n B T rem 0 hqpos hDpos (Nat.cast_nonneg _) hB hTlo hremlo (by simp)
  simp only [zero_div,add_zero] at hbudget
  have hε : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := by positivity
  have hbad : highBadMass (D*σ^(3*beta η)) (D*σ^beta η) 153≤(1:ℝ)/4 :=
    (highBadMass_le_highFourLoss (Nat.card K) r' h (by omega) _ _ _ hε.le).trans
      (hfour'.trans (by norm_num))
  obtain ⟨i,hi⟩:=high_prepared_round hd S ctx J B M P r' hrhi hcap T rem hT hrem hnrem hroom
    (D*σ^beta η) (D*σ^(3*beta η)) (σ^(-2000*beta η)/(Nat.card K:ℝ))
    (by simpa only [hσeq] using hJ) (by positivity) (by positivity) hε hbad hgeom'.1 h
  have hlN : n≤N := by have:=S.length_le_source;omega
  apply hcontra K V Ω κ α N n n i.val r' h admissible S ctx (fun _ _=>Finset.univ)
    (D*σ^(3*beta η)) hd hσ hq hα hN hlN (by omega) hlen hC
    (by simpa only [hq] using hhhi)
  apply hi.trans
  have hm:=mul_le_mul_of_nonneg_left hfour' (by positivity : (0:ℝ)≤2*n)
  have hd':=mul_le_mul_of_nonneg_left hbudget (by norm_num : (0:ℝ)≤5)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at *
  nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
end

end SharpRamseyFive.SelectedTuple

end OAI
