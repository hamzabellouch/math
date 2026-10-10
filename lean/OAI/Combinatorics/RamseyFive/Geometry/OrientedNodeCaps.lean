import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ReadyRefinement
import OAI.Combinatorics.RamseyFive.Trees.PivotPotential

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_cap_card (UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (UA.map bidualPoint.toEmbedding∩Y).card=(UA∩Y.map bidualPoint.symm.toEmbedding).card := by
  simpa only [Finset.inter_assoc,Finset.inter_left_idem] using bidual_inter_card UA UA Y

theorem orientedGuardedNode_caps
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    ((UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(B₀∩UB).card ∧
    ((UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(A₀∩UA).card := by
  have hC : (320/((9:ℝ)/10)+320)≤320/c+320 := by
    have hh : (320:ℝ)/((9:ℝ)/10)≤320/c := div_le_div_of_nonneg_left (by norm_num) hc hc9
    linarith only [hh]
  have hM (n : ℕ) : (320/((9:ℝ)/10)+320)*((Nat.card K:ℝ)^5)/n≤
      (320/c+320)*((Nat.card K:ℝ)^5)/n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Nat.cast_nonneg n)
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hB,hA⟩ := guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'
    exact ⟨hA.2.1.trans (hM _),hB.2.1⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hA,hB⟩ := guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    constructor
    · simpa only [orientedNodeDecoded,reverseNodePair,bidual_cap_card] using hA.2.1
    · have hh := hB.2.1
      simp only [←Finset.map_inter,Finset.card_map] at hh
      exact hh.trans (hM _)

theorem orientedGuardedNode_split_potential
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c τ P b : ℝ) (hc : 0<c) (hc9 : c≤9/10)
    (hp : ((Nat.card K:ℝ)^5)*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c (9/10) τ P (by norm_num) t=some m) :
    potential (UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2).card
        UB.card ((Nat.card K:ℝ)^5)+
      potential UA.card (UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1).card
        ((Nat.card K:ℝ)^5)≤
      potential UA.card UB.card ((Nat.card K:ℝ)^5)+(b+1)+2*Real.log (320/c+320) := by
  obtain ⟨hready,hca,hcb⟩ := orientedGuardedNode_original_capture f r σ hσ hq hd A₀ UA B₀ UB
    hA₀ hB₀ c (9/10) τ P (by norm_num) t m hm
  obtain ⟨hAcap,hBcap⟩ := orientedGuardedNode_caps f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P hc hc9 (by norm_num) t m hm
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hready.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hready.2.1
  have hcA := (nonempty_of_positive_trim _ _ hA₀ ((9/10)*(9/10)) (by norm_num) hca).mono Finset.inter_subset_right
  have hcB := (nonempty_of_positive_trim _ _ hB₀ ((9/10)*(9/10)) (by norm_num) hcb).mono Finset.inter_subset_right
  have hQ : (0:ℝ)<((Nat.card K:ℝ)^5) := by rw [←hq];positivity
  have hnA' : (0:ℝ)<(A₀∩UA).card := by exact_mod_cast hnA.card_pos
  have hnB' : (0:ℝ)<(B₀∩UB).card := by exact_mod_cast hnB.card_pos
  have hsplit := split_potential UA.card UB.card (A₀∩UA).card (B₀∩UB).card _ _ ((Nat.card K:ℝ)^5) (320/c+320)
    hnA' hnB' (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=A₀) (s₂:=UA)))
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=B₀) (s₂:=UB)))
    (by exact_mod_cast hcA.card_pos) (by exact_mod_cast hcB.card_pos) hQ
    (by
      have hh : 0≤(320:ℝ)/c := by positivity
      linarith only [hh]) hAcap hBcap
  have ht := ready_trimmed_product A₀ UA B₀ UB τ b hready hp
  have he : Real.exp (-(b+1))*Real.exp (b+1)=1 := by rw [←Real.exp_add];simp
  have hx : ((Nat.card K:ℝ)^5)≤((A₀∩UA).card:ℝ)*(B₀∩UB).card*Real.exp (b+1) := by
    calc
      _=(((Nat.card K:ℝ)^5)*Real.exp (-(b+1)))*Real.exp (b+1) := by rw [mul_assoc,he,mul_one]
      _≤_ := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hb : Real.log (((Nat.card K:ℝ)^5)/(((A₀∩UA).card:ℝ)*(B₀∩UB).card))≤b+1 := by
    apply (Real.log_le_iff_le_exp (div_pos hQ (mul_pos hnA' hnB'))).mpr
    apply (div_le_iff₀ (mul_pos hnA' hnB')).mpr
    simpa only [mul_comm (Real.exp (b+1))] using hx
  linarith only [hsplit,hb]
end SharpRamseyFive.ProjectiveIncidence

end OAI
