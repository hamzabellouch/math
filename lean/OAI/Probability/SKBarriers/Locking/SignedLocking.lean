import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaMarginal
import OAI.Probability.SKBarriers.Replicas.PairGibbsGap
import OAI.Probability.SKBarriers.Replicas.ReplicaEventSplit
import OAI.Probability.SKBarriers.Replicas.TripleContinuumGap

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def signedLockingSet (n : ℕ) (h b : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => h≤tripleQ s ∧
    |overlap (s 0) (s 1)|≤b ∧ |overlap (s 0) (s 2)|≤b ∧
    2*(n:ℝ)^(-(1:ℝ)/100)< |overlap (s 0) (s 1)-overlap (s 0) (s 2)|)

def orientedLockingSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (h b τ : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => tripleQ s∈Icc h 1 ∧ tripleR s∈Icc (0:ℝ) b ∧
    |tripleDelta s|≤b ∧ (n:ℝ)^(-(1:ℝ)/100)≤|tripleDelta s| ∧
    |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤τ)

theorem signedLocking_split {n : ℕ} (β h b τ : ℝ) (hh : 0≤h) (α : ℝ → ℝ)
    {s : ReplicaConfig n 3} (hs : s∈signedLockingSet n h b) :
    s∈orientedLockingSet n β α h b τ ∨ replicaFlip 0 s∈orientedLockingSet n β α h b τ ∨
      Fin.tail s∈pairMismatchSet n β α τ := by
  classical
  obtain ⟨hq,hx,hy,hd⟩ := (Finset.mem_filter.mp hs).2
  have hb := tripleRDelta_abs_le s hx hy
  have hq1 := (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2
  have hδ : (n:ℝ)^(-(1:ℝ)/100)≤|tripleDelta s| := by
    dsimp only [tripleDelta]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hd]
  by_cases hg : |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤τ
  · by_cases hr : 0≤tripleR s
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨hq,hq1⟩,⟨hr,(abs_le.mp hb.1).2⟩,hb.2,hδ,hg⟩⟩
    · right; left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [tripleQ_flip,tripleR_flip,tripleDelta_flip,abs_neg]
      exact ⟨⟨hq,hq1⟩,⟨by linarith only [hr],by linarith only [(abs_le.mp hb.1).1]⟩,hb.2,hδ,hg⟩
  · right; right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hh.trans hq,(not_le.mp hg).le⟩⟩

theorem signed_fixed_scale_locking {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) :
    ∃ b : ℝ,0<b ∧ ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤
        Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
  classical
  obtain ⟨μ,hμ,hmin,τ,r₀,δ₀,c,hτ,hr₀,hδ₀,hc,hgap⟩ := exists_tripleConstrainedPressure_gap hβ hh hh1
  let α := cdf (μ : Measure ℝ)
  have ha (z : ℝ) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have ha1 : α 1=1 := supported_probability_cdf_one μ hμ
  let b := min r₀ δ₀
  have hb : 0<b := lt_min hr₀ hδ₀
  have HP := eventual_pairMismatch_polynomial_bound (A:=τ) (a:=0) (t:=(9:ℝ)/10) (ε:=1/2)
    hβ hτ le_rfl (by norm_num) (by norm_num) (by norm_num) α ha ha1 hmin
  have HT := eventual_replicaGibbsMass_polynomial_gap (c:=c) (a:=(1:ℝ)/50) (t:=(9:ℝ)/10) (ε:=1/4)
    hβ 3 3 (by decide) hc (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨b,hb,?_⟩
  filter_upwards [HP,HT,eventually_gt_atTop (0:ℕ)] with n hnP hnT hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  let T := orientedLockingSet n β α h b τ
  have HT' : (∫ J,replicaGibbsMass β J T ∂disorderLaw n)≤(1/4)*Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
    apply hnT (Fin 3 → Fin (n+1)) (by simp) tripleReplicaCode (fun s t H => tripleReplicaCode_gram hn0 H)
    intro s hs
    obtain ⟨hq,hr,hδ,hδlower,hdev⟩ := (Finset.mem_filter.mp hs).2
    have hfeas := replicaGram_feasible s
    rw [replicaGram_triple_overlap hn0] at hfeas ⊢
    have HG := hgap n hn0 (tripleR s) (tripleDelta s) (tripleQ s)
      ⟨hr.1,hr.2.trans (min_le_left _ _)⟩ (hδ.trans (min_le_right _ _)) hq hdev hfeas
    have HD := pow_le_pow_left₀ (Real.rpow_nonneg hp.le _) hδlower 2
    rw [sq_abs] at HD
    have HE : ((n:ℝ)^(-(1:ℝ)/100))^2=(n:ℝ)^(-(1:ℝ)/50) := by
      rw [← Real.rpow_natCast ((n:ℝ)^(-(1:ℝ)/100)) 2,← Real.rpow_mul hp.le]
      norm_num
    rw [HE] at HD
    have HDC := mul_le_mul_of_nonneg_left HD hc.le
    norm_num only [Nat.cast_ofNat]
    linarith only [HG,HDC]
  have Hsplit := replicaGibbsMass_integral_or_or_flip (0:Fin 3) β (signedLockingSet n h b) T
    (Finset.univ.filter (fun s : ReplicaConfig n 3 => Fin.tail s∈pairMismatchSet n β α τ))
    (fun s hs => by
      rcases signedLocking_split β h b τ hh.le α hs with H|H|H
      · exact Or.inl H
      · exact Or.inr (Or.inl H)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩)))
  simp_rw [replicaGibbsMass_tail] at Hsplit
  simp only [neg_zero,Real.rpow_zero,mul_one] at hnP
  linarith only [Hsplit,HT',hnP]

end SK.Analytic

end
end

end OAI
