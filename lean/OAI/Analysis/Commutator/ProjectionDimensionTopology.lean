import Mathlib
import OAI.Analysis.Commutator.CountableProjectionJoin
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.DyadicDimensionComparison
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.ProjectionStrong

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionDimensionTopology

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

theorem strong_zero_of_geometric_dimension (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n))
    (hbound : ∀ n,dimension M hfac hd (P n)≤(1/2:ℝ)^n) (x : H) :
    Tendsto (fun n => P n x) atTop (𝓝 0) := by
  let T (n : ℕ) := sup M (fun k => P (n+k)) (fun k => hP (n+k)) (fun k => hPM (n+k))
  have hTM (n : ℕ) : T n∈M := sup_mem M _ _ _
  have hTP (n : ℕ) : IsStarProjection (T n) := sup_projection M _ _ _
  have hPT (n : ℕ) : P n≤T n := by
    simpa only [Nat.add_zero] using le_sup M (fun k => P (n+k))
      (fun k => hP (n+k)) (fun k => hPM (n+k)) 0
  have hmono : Antitone T := by
    apply antitone_nat_of_succ_le
    intro n
    apply sup_le M _ _ _ (hTP n)
    intro k
    have hh := le_sup M (fun k => P (n+k)) (fun k => hP (n+k)) (fun k => hPM (n+k)) (k+1)
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hh
  have hdim (n : ℕ) : dimension M hfac hd (T n)≤2*(1/2:ℝ)^n := by
    have hs : Summable (fun k : ℕ => (1/2:ℝ)^(n+k)) := by
      simpa only [pow_add] using (summable_geometric_of_lt_one
        (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)).mul_left ((1/2:ℝ)^n)
    have hh := dimension_sup_le M hfac hd hfin (fun k => P (n+k))
      (fun k => hP (n+k)) (fun k => hPM (n+k)) (fun k => (1/2:ℝ)^(n+k)) hs
      (fun k => hbound (n+k))
    have he : (∑' k : ℕ,(1/2:ℝ)^(n+k))=2*(1/2:ℝ)^n := by
      simp only [pow_add,tsum_mul_left]
      rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]
      ring
    exact he ▸ hh
  let Q (n : ℕ) := 1-T n
  have hQM (n : ℕ) : Q n∈M := M.sub_mem M.one_mem (hTM n)
  have hQP (n : ℕ) : IsStarProjection (Q n) := (hTP n).one_sub
  have hQmono : Monotone Q := fun n m h => sub_le_sub_left (hmono h) 1
  obtain ⟨W,hWM,hWP,hQW,hlim,_⟩ := ProjectionChains.exists_strong_sup M Q hQP hQM hQmono
  have hc : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdW : 1≤dimension M hfac hd W := by
    have ht : Tendsto (fun n : ℕ => 1-2*(1/2:ℝ)^n) atTop (𝓝 1) := by
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hc)
    apply le_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    have hh := dimension_mono M hfac hd (hQM n) (hQP n) (hQW n)
    change dimension M hfac hd (1-T n)≤_ at hh
    rw [dimension_complement M hfac hd hfin (hTM n) (hTP n)] at hh
    linarith [hdim n]
  have hW : W=1 := by
    have hdz : dimension M hfac hd (1-W)=0 := by
      rw [dimension_complement M hfac hd hfin hWM hWP]
      linarith [dimension_le_one M hfac hd W]
    have he := (dimension_eq_zero_iff M hfac hd hfin (M.sub_mem M.one_mem hWM)
      hWP.one_sub).mp hdz
    exact (sub_eq_zero.mp he).symm
  have hTlim : Tendsto (fun n => T n x) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := x)).sub (hlim x)
    rw [hW] at hh
    simpa only [Q,sub_apply,one_apply_eq_self,sub_sub_cancel,sub_self] using hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    ProjectionChains.projection_norm_mono (hP n) (hTP n) (hPT n) x) (by
      simpa only [norm_zero] using hTlim.norm)

theorem vector_uniform_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
      dimension M hfac hd p<δ → ‖p x‖<ε := by
  classical
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ p : H →L[ℂ] H,p∈M ∧ IsStarProjection p ∧
      dimension M hfac hd p<(1/2:ℝ)^n ∧ ε≤‖p x‖ := hn ((1/2:ℝ)^n) (by positivity)
  choose P hPM hP hdP hnorm using hex
  have ht := strong_zero_of_geometric_dimension M hfac hd hfin P hPM hP (fun n => (hdP n).le) x
  have he := (show Tendsto (fun n => ‖P n x‖) atTop (𝓝 0) by
    simpa only [norm_zero] using ht.norm).eventually_lt_const hε
  obtain ⟨n,hn⟩ := he.exists
  exact (not_lt_of_ge (hnorm n)) hn

end Kadison.ProjectionDimensionTopology

end

end
end

end OAI
