import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellSchedule

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_cell_exhaustion {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ w₀ : ℕ, 0 < w₀ ∧
      ∀ w ≥ w₀, ∀ m : ℕ, (2*A*k)*(m:ℝ) ≤ Bstar →
      ∀ v : ℕ, 2*cellWidth w m 0 ≤ v →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      environmentLaw ν (⋃ p : Composition m, failedOpportunityBlocks
        (scheduledCellFailure ν e f hef a C c g₀ g₁ A hc π v w m s) 0 p.blocks) ≤
          (2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m)) := by
  obtain ⟨A,hA,hk⟩ := actual_consumed_cell_failure ν hue e f hef htrans
  refine ⟨A,hA,fun k hk₂ => ?_⟩
  obtain ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,H₀,hs,hbudget⟩ := hk k hk₂
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,fun Bstar hB => ?_⟩
  obtain ⟨R,hR,hbound⟩ := hbudget Bstar hB
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  have : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hI : Integrable S μ := independent_commonWordIncrement_integrable ν hue _
    (signed_direction_unit e) htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f
  have hne : 0 < μ {x | S x ≠ 0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hlim : Tendsto (fun H : ℕ => (H:ℝ)/C) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hC
  obtain ⟨W,hW⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_atTop (fluctuationScale μ S R)))
  refine ⟨max 1 (max H₀ W),by omega,?_⟩
  intro w hw m hm v hv a π hπ
  let F := scheduledCellFailure ν e f hef a C c g₀ g₁ A hc π v w m s
  let ℱ := cellFiltration e a v w m
  have hFm : ∀ i n, 0 < n → MeasurableSet[ℱ (i+n)] (F i n) := by
    intro i n _
    exact scheduledCellFailure_measurable ν e f hef a C c g₀ g₁ A hc π hπ v w m s hv hs i n
  have hexp (n : ℕ) : ENNReal.ofReal (Real.exp (-2*k*n)) =
      (ENNReal.ofReal (Real.exp (-2*k)))^n := by
    rw [←ENNReal.ofReal_pow (Real.exp_nonneg _),←Real.exp_nat_mul]
    congr 2
    ring
  have hfresh : ∀ i n, 0 < n → ∀ E : Set (Environment d), MeasurableSet[ℱ i] E →
      environmentLaw ν (E∩F i n) ≤ (ENNReal.ofReal (Real.exp (-2*k)))^n*environmentLaw ν E := by
    intro i n hn E hE
    dsimp [F,scheduledCellFailure]
    split
    · rename_i h
      rcases h with ⟨hi,_,hnm⟩
      have hwidth : max H₀ W ≤ cellWidth w m i :=
        (show max H₀ W ≤ w by omega).trans (cellWidth_min w m i)
      have hrad := fluctuationRadius_spec μ S hS hI hne hR
        (hW (cellWidth w m i) ((le_max_right _ _).trans hwidth))
      have hscale : C*fluctuationScale μ S (cellRadius ν e f C w m i)=cellWidth w m i := by
        change C*fluctuationScale μ S (fluctuationRadius μ S ((cellWidth w m i:ℝ)/C))=_
        rw [hrad.2,mul_div_cancel₀ _ (ne_of_gt hC)]
      rw [←hexp]
      apply hbound (cellWidth w m i) ((le_max_left _ _).trans hwidth)
        (cellRadius ν e f C w m i) (cellRadius_pos ν e f C w m i) hrad.1.le rfl
        (cellEarlyHeight v w m i s) _ (cellLateHeight v w m i s) _ (m-i) _ n (by omega) hnm
        (a+cellOpportunity v w m i) (cellRestart e a π v w m i)
        (cellRestart_measurable e a π hπ v w m i) E hE
      · change (cellEarlyHeight v w m i s:ℝ) ≤ 3*C*fluctuationScale μ S _
        rw [mul_assoc, hscale]
        exact_mod_cast cellEarlyHeight_bound v w m i s hv hi
      · intro j
        change (cellLateHeight v w m i s j:ℝ) ≤ 3*C*fluctuationScale μ S _/(16:ℝ)^(s+j)
        rw [mul_assoc,hscale]
        apply (le_div_iff₀ (by positivity)).mpr
        exact_mod_cast cellLateHeight_bound v w m i s j hv
      · apply le_trans _ hm
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast Nat.sub_le m i
    · simp
  have hh := opportunity_exhaustion_probability (environmentLaw ν) ℱ F hFm
    (ENNReal.ofReal (Real.exp (-2*k))) hfresh m
  simpa only [←hexp] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def cellAttemptSuccess {Ω : Type*} (seed : Ω → ℝ≥0∞) (early : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (g₀ g₁ kA : ℝ) (s m : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
    ∀ j < m-s, Real.exp (-kA*((s:ℝ)+j+1)) ≤ ∏ i∈Finset.range (j+1), q i ω}

lemma cell_failure_or_success {Ω : Type*} (seed : Ω → ℝ≥0∞) (early : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (g₀ g₁ kA : ℝ) (s m : ℕ) (hs : 0 < s) (hm : 0 < m) (ω : Ω) :
    ω ∈ cellAttemptSuccess seed early q g₀ g₁ kA s m ∨
      ∃ n, 0 < n ∧ n ≤ m ∧ ω ∈ consumedCellFailure seed early q g₀ g₁ kA s m n := by
  by_cases hseed : ENNReal.ofReal g₀ ≤ seed ω
  · by_cases hear : g₁ ≤ early ω
    · by_cases hall : ∀ j < m-s, Real.exp (-kA*((s:ℝ)+j+1)) ≤ ∏ i∈Finset.range (j+1), q i ω
      · exact Or.inl ⟨hseed,hear,hall⟩
      · right
        have hex : ∃ j, j < m-s ∧ (∏ i∈Finset.range (j+1), q i ω) < Real.exp (-kA*((s:ℝ)+j+1)) := by
          push Not at hall
          exact hall
        let j := Nat.find hex
        have hj := Nat.find_spec hex
        have heq : s+j+1-s-1=j := by omega
        refine ⟨s+j+1,by omega,by omega,Or.inr ?_⟩
        refine ⟨by omega,by omega,hseed,hear,?_⟩
        rw [heq]
        refine ⟨?_,hj.2⟩
        intro u hu
        have hh := Nat.find_min hex hu
        push Not at hh
        exact hh (by omega)
    · exact Or.inr ⟨min s m,by omega,min_le_right _ _,Or.inl (Or.inr ⟨rfl,hseed,not_le.mp hear⟩)⟩
  · exact Or.inr ⟨1,by omega,hm,Or.inl (Or.inl ⟨rfl,not_le.mp hseed⟩)⟩

lemma failed_blocks_of_no_success {Ω : Type*} (F : ℕ → ℕ → Set Ω) (S : ℕ → Set Ω)
    (m : ℕ) (hchoice : ∀ i < m, ∀ ω, ω ∈ S i ∨ ∃ n, 0 < n ∧ n ≤ m-i ∧ ω ∈ F i n)
    (ω : Ω) (hfail : ∀ i < m, ω ∉ S i) :
    ∃ p : Composition m, ω ∈ failedOpportunityBlocks F 0 p.blocks := by
  have build : ∀ r i, i+r=m → ∃ ns : List ℕ, ns.sum=r ∧
      (∀ n∈ns, 0 < n) ∧ ω ∈ failedOpportunityBlocks F i ns := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hir
      by_cases hr : r=0
      · refine ⟨[],?_,by simp,?_⟩
        · simpa using hr.symm
        · trivial
      · have hi : i < m := by omega
        obtain ⟨n,hn,hnr,hFn⟩ := (hchoice i hi ω).resolve_left (hfail i hi)
        obtain ⟨ns,hns,hpos,hnsF⟩ := ih (r-n) (by omega) (i+n) (by omega)
        refine ⟨n::ns,?_,?_,⟨hFn,hnsF⟩⟩
        · simp only [List.sum_cons,hns]; omega
        · intro u hu
          simp only [List.mem_cons] at hu
          rcases hu with rfl|hu
          · exact hn
          · exact hpos u hu
  obtain ⟨ns,hs,hp,hF⟩ := build m 0 (by omega)
  exact ⟨⟨ns,(fun {n} hn => hp n hn),hs⟩,hF⟩

end DirectionalTransience

end

end OAI
