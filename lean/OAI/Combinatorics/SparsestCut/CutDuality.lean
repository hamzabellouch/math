import OAI.Combinatorics.SparsestCut.Semimetrics
import OAI.Combinatorics.SparsestCut.FiniteDuality

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section CutConeDuality
variable {n : ℕ}

lemma pairSum_sum {K : Type u1} [Fintype K] (f : K → Fin n → Fin n → ℝ) :
    pairSum (fun i j => ∑ k, f k i j) = ∑ k, pairSum (f k) := by
  classical
  unfold pairSum
  have hh (i j : Fin n) : (if i < j then ∑ k, f k i j else 0) =
      ∑ k, if i < j then f k i j else 0 := by
    split_ifs <;> simp_all
  simp_rw [hh]
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

noncomputable def symmetrizeCapacity (c : (Fin n × Fin n) → ℝ)
    (hc : ∀ e, 0 ≤ c e) : Capacity n where
  cap i j := if i = j then 0 else c (i,j) + c (j,i)
  nonneg i j := by split_ifs; exact le_rfl; exact add_nonneg (hc _) (hc _)
  symm i j := by by_cases h : i = j <;> simp [h, eq_comm, add_comm]
  diagonal i := by simp

lemma symmetrize_objective (c : (Fin n × Fin n) → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : Fin n → Fin n → ℝ) (hs : ∀ i j, d i j = d j i) (hd : ∀ i, d i i = 0) :
    pairSum (fun i j => (symmetrizeCapacity c hc).cap i j * d i j) =
      ∑ e, c e * d e.1 e.2 := by
  have hfun : (fun i j => (symmetrizeCapacity c hc).cap i j * d i j) =
      (fun i j => c (i,j) * d i j + c (j,i) * d j i) := by
    funext i j
    by_cases h : i = j
    · subst j; simp [hd]
    · simp [symmetrizeCapacity, h, hs j i, add_mul]
  rw [hfun, pairSum_add, pairSum_swap _ (fun i => by simp [hd])]
  exact (Fintype.sum_prod_type (fun e : Fin n × Fin n => c e * d e.1 e.2)).symm

theorem cut_cone_duality (hn : 2 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : NegativeType d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (havg : (n : ℝ)^2 * a ≤ ∑ i, ∑ j, d i j)
    (hcon : ∀ (K : Type) [Fintype K] (F : Fin n → K → ℝ),
      (∀ i j, (∑ k, |F i k - F j k|) ≤ d i j) →
      (∑ i, ∑ j, ∑ k, |F i k - F j k|) ≤ (n : ℝ)^2 * b) :
    ∃ C : Capacity n, 1 ≤ OPT C ∧ 0 < glValue C ∧ glValue C ≤ b / a := by
  classical
  have hsemi := hd.semimetric
  let A : (Fin n × Fin n) → Cut n → ℝ := fun e B => cutDist B.1 e.1 e.2
  let w : Cut n → ℝ := fun B => cutDemand B.1
  have hcol (B : Cut n) : 0 < ∑ e, A e B := by
    change 0 < ∑ e : Fin n × Fin n, cutDist B.1 e.1 e.2
    rw [Fintype.sum_prod_type, orderedSum_eq_two_pairSum _ (cutDist_symm _) (cutDist_self _), pairSum_cut]
    exact mul_pos (by norm_num) (cutDemand_pos B)
  have hbound (t : Cut n → ℝ) (ht : ∀ B, 0 ≤ t B)
      (htd : ∀ e, ∑ B, A e B * t B ≤ d e.1 e.2) :
      (∑ B, w B * t B) ≤ (n : ℝ)^2 * b / 2 := by
    let F : Fin n → Cut n → ℝ := fun i B => t B * cutIndicator B.1 i
    have hFd (i j : Fin n) : (∑ B, |F i B - F j B|) = ∑ B, t B * cutDist B.1 i j := by
      apply Finset.sum_congr rfl
      intro B hB
      simp [F, cutDist, ← mul_sub, abs_mul, abs_of_nonneg (ht B)]
    have hcontract (i j : Fin n) : (∑ B, |F i B - F j B|) ≤ d i j := by
      rw [hFd]
      simpa only [A, mul_comm] using htd (i,j)
    have htavg := hcon (Cut n) F hcontract
    simp_rw [hFd] at htavg
    have hsym (i j : Fin n) : (∑ B, t B * cutDist B.1 i j) =
        ∑ B, t B * cutDist B.1 j i := by simp_rw [cutDist_symm _ i j]
    rw [orderedSum_eq_two_pairSum _ hsym (fun i => by simp), pairSum_sum] at htavg
    simp_rw [pairSum_smul, pairSum_cut] at htavg
    have he : (∑ B, w B * t B) = ∑ B, t B * cutDemand B.1 := by
      unfold w; simp_rw [mul_comm]
    rw [he]
    linarith
  let W : ℝ := ∑ B : Cut n, w B
  have hw0 (B : Cut n) : 0 ≤ w B := (cutDemand_pos B).le
  obtain ⟨c,hc,hcover,hobj⟩ := FiniteDuality.packing_duality A w
    (fun e B => cutDist_binary B.1 e.1 e.2) hcol
    (fun e => d e.1 e.2) (fun e => hsemi.1 _ _)
    (show 0 ≤ (n : ℝ)^2 * b / 2 by positivity)
    (show 0 ≤ W from Finset.sum_nonneg (fun B hB => hw0 B))
    (fun B => Finset.single_le_sum (fun B hB => hw0 B) (Finset.mem_univ B)) hbound
  let C := symmetrizeCapacity c hc
  have hC (B : Cut n) : cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j := by
    rw [← cut_capacity_pair, symmetrize_objective c hc _ (cutDist_symm _) (cutDist_self _)]
    simpa only [A, w, mul_comm] using hcover B
  refine ⟨C, OPT_ge_one_of_cuts C hn hC, glValue_pos_of_cuts C hn hC, ?_⟩
  let D := pairSum d
  have havg' : (n : ℝ)^2 * a ≤ 2 * D := by
    simpa only [orderedSum_eq_two_pairSum d hsemi.2.1 hsemi.2.2.1] using havg
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := by nlinarith [mul_pos (sq_pos_of_pos hn0) ha]
  let d' := fun i j => D⁻¹ * d i j
  have hd' : Feasible d' := by
    refine ⟨hd.scale (inv_nonneg.mpr hD.le), ?_⟩
    change pairSum (fun i j => D⁻¹ * d i j) = 1
    rw [pairSum_smul, inv_mul_cancel₀ hD.ne']
  have hbdd : BddBelow {r | ∃ d : Fin n → Fin n → ℝ, Feasible d ∧
      r = pairSum (fun i j => C.cap i j * d i j)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨d,hd,rfl⟩
    exact objective_nonneg C hd.1.semimetric
  have hgl : glValue C ≤ pairSum (fun i j => C.cap i j * d' i j) :=
    csInf_le hbdd ⟨d',hd',rfl⟩
  apply hgl.trans
  have hscale : pairSum (fun i j => C.cap i j * d' i j) =
      (pairSum (fun i j => C.cap i j * d i j)) / D := by
    simp only [d', div_eq_mul_inv]
    rw [mul_comm _ D⁻¹, ← pairSum_smul D⁻¹]
    congr 1
    funext i j; ring
  rw [hscale, symmetrize_objective c hc d hsemi.2.1 hsemi.2.2.1,
    div_le_div_iff₀ hD ha]
  have hh1 := mul_le_mul_of_nonneg_right hobj ha.le
  have hh2 := mul_le_mul_of_nonneg_right havg' hb.le
  nlinarith

end CutConeDuality

end UniformSparsestCut

end

end OAI
