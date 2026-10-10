import OAI.Analysis.LipschitzHilbert.Trees.SourceNodeRatio
import OAI.Analysis.LipschitzHilbert.Trees.SourceCellMarking
import OAI.Analysis.LipschitzHilbert.Estimates.MarkedCost
import OAI.Analysis.LipschitzHilbert.Trees.UnaryRunResidual
import OAI.Analysis.LipschitzHilbert.Trees.UnaryPartitionSum
import OAI.Analysis.LipschitzHilbert.Trees.UnarySegmentEstimate

namespace OAI

/-! The finite path-product argument in §10. Marked indices retain the
residual-free predictor; all consecutive unary runs use one common cubic
variation estimate. The remaining unmarked large-drop index is unique.
The estimates are independent of the number of angular levels. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace UnaryRunPartition

theorem indices_disjoint {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) :
    Set.PairwiseDisjoint (R.runs : Set (ℕ × ℕ)) (fun r => Finset.Ico r.1 r.2) := by
  intro r hr s hs hrs
  apply Finset.disjoint_left.mpr
  intro j hjr hjs
  have hjr' := Finset.mem_Ico.mp hjr
  have hjs' := Finset.mem_Ico.mp hjs
  rcases R.ordered r hr s hs hrs with h | h <;> omega

theorem indices_union {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) :
    R.runs.biUnion (fun r => Finset.Ico r.1 r.2) =
      (Finset.Ico start finish).filter unary := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨r,hr,hjr⟩ := Finset.mem_biUnion.mp hj
    have hb := R.bounds r hr
    have hi := Finset.mem_Ico.mp hjr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hb.1.trans hi.1,hi.2.trans_le hb.2.2⟩,R.inside r hr j hi.1 hi.2⟩
  · intro hj
    obtain ⟨hi,hu⟩ := Finset.mem_filter.mp hj
    obtain ⟨r,hr,hlo,hhi⟩ := R.cover j (Finset.mem_Ico.mp hi).1
      (Finset.mem_Ico.mp hi).2 hu
    exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_Ico.mpr ⟨hlo,hhi⟩⟩

theorem sum_runs {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) :
    (∑ r ∈ R.runs, ∑ j ∈ Finset.Ico r.1 r.2, f j) =
      ∑ j ∈ (Finset.Ico start finish).filter unary, f j := by
  classical
  rw [← Finset.sum_biUnion R.indices_disjoint,R.indices_union]

theorem sum_segments {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E : Type*} [AddCommMonoid E] (f : ℕ → E) :
    (∑ i : UnaryRunSegment R P, ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, f j) =
      ∑ j ∈ (Finset.Ico start finish).filter unary, f j := by
  classical
  rw [Fintype.sum_sigma]
  have h (r : R.runs) :
      (∑ b : (P r).blocks, ∑ j ∈ Finset.Ico b.val.1 b.val.2, f j) =
        ∑ j ∈ Finset.Ico r.val.1 r.val.2, f j := by
    rw [← Finset.sum_subtype (P r).blocks (p := fun b => b ∈ (P r).blocks)
      (by simp) (fun b : ℕ × ℕ => ∑ j ∈ Finset.Ico b.1 b.2, f j)]
    exact (P r).sum_blocks f
  simp_rw [h]
  rw [← Finset.sum_subtype R.runs (p := fun r => r ∈ R.runs)
    (by simp) (fun r : ℕ × ℕ => ∑ j ∈ Finset.Ico r.1 r.2, f j)]
  exact R.sum_runs f

end UnaryRunPartition

/-- The discarded-top contributions sum against true relative drops,
also when the unary indices have many separate consecutive runs. -/
theorem source_unary_runs_weighted_drop {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    (hn : Antitone n) {μ Q : ℝ} (hμ : μ ≤ 1)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^μ ≤ Q) :
    (∑ i : UnaryRunSegment R P,
      n i.2.val.1^(μ-1)*(n i.2.val.1-n i.2.val.2)) ≤
        Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j := by
  have hstep (i : UnaryRunSegment R P) :
      n i.2.val.1^(μ-1)*(n i.2.val.1-n i.2.val.2) ≤
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Q*pathDrop n j := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    rw [← sum_Ico_mass_drop n hb.2.1.le,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjb := Finset.mem_Ico.mp hj
    have hjf : j ∈ Finset.Ico start finish := Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hjb.1),hjb.2.trans_le (hb.2.2.trans hr.2.2)⟩
    have hjpos := hnpos j hjf
    have hdrop := sub_nonneg.mpr (hn (Nat.le_succ j))
    calc
      _ ≤ n j^(μ-1)*(n j-n (j+1)) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hjpos (hn hjb.1) (by linarith)) hdrop
      _ = n j^μ*pathDrop n j := by rw [Real.rpow_sub_one hjpos.ne',pathDrop]; ring
      _ ≤ Q*pathDrop n j := mul_le_mul_of_nonneg_right (hQ j hjf)
        (pathDrop_nonnegative n j hjpos (hn (Nat.le_succ j)))
  calc
    _ ≤ ∑ i : UnaryRunSegment R P,
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Q*pathDrop n j := Finset.sum_le_sum
      (fun i _ => hstep i)
    _ = _ := by rw [R.sum_segments P,Finset.mul_sum]

/-- Reindex the actual unary energy telescope to an arbitrary segment.
The propagated comparison amplitude is required only on that segment. -/
theorem source_unary_segment_log_cost {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ → ℝ) (A Astar : ℕ → E) (beta : ℕ → ℝ)
    {e f : ℕ} {a p D : ℝ} (hef : e ≤ f)
    (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hD : 0 ≤ D)
    (hstart : 4 ≤ n e) (hn : Antitone n) (hdrop : n e-n f ≤ 2)
    (hcontraction : ∀ j ∈ Finset.Ico e f, ‖Astar j‖ ≤ ‖Astar (j+1)‖)
    (hend : Astar f = A f) (hbeta : ∀ j ∈ Finset.Ico e f, 0 < beta j)
    (hprediction : ∀ j ∈ Finset.Ico e f, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (herror : ∀ j ∈ Finset.Icc e f, ‖A j-Astar j‖ ≤ D) :
    (∑ j ∈ Finset.Ico e f, Real.log (beta j)) ≤ 4*p*n e^((a-1)/p-1)*D := by
  have h := unary_vertex_telescope_short_segment (f-e)
    (fun j => n (e+j)) (fun j => A (e+j)) (fun j => Astar (e+j))
    (fun j => beta (e+j)) hp ha hap hD (by simpa using hstart) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Finset.sum_Ico_eq_sum_range,Nat.add_zero] using h
  · intro j hj
    have hmono := hn (show e+j ≤ f by omega)
    simpa only [Nat.add_zero] using (show n e-2 ≤ n (e+j) by linarith)
  · intro j _
    exact hn (by omega)
  · intro j hj
    simpa only [Nat.add_assoc] using hcontraction (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · simpa only [Nat.add_sub_of_le hef] using hend
  · intro j hj
    exact hbeta (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · intro j hj
    simpa only [Nat.add_assoc] using hprediction (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · intro j hj
    exact herror (e+j) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

/-- All unary runs use one cubic-variation budget. The local error bound
is the actual propagated amplitude error from Abel summation, not a
hypothesis about the path product. -/
theorem source_unary_runs_log_cost {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    (A : ℕ → E) (Astar : ℕ → ℕ → ℕ → E) (beta : ℕ → ℝ)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level finish ≤ N) (hn : Antitone n)
    {a p c M V C ε Q : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hmass : ∀ j ∈ (Finset.Ico start finish).filter unary, M ≤ n j)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^((a-1)/p) ≤ Q)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬unary j → c ≤ n j-n (j+1))
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hbeta : ∀ j ∈ (Finset.Ico start finish).filter unary, 0 < beta j)
    (hprediction : ∀ j ∈ (Finset.Ico start finish).filter unary, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (hcontraction : ∀ i : UnaryRunSegment R P,
      ∀ j ∈ Finset.Ico i.2.val.1 i.2.val.2,
        ‖Astar i.2.val.1 i.2.val.2 j‖ ≤ ‖Astar i.2.val.1 i.2.val.2 (j+1)‖)
    (hend : ∀ i : UnaryRunSegment R P,
      Astar i.2.val.1 i.2.val.2 i.2.val.2 = A i.2.val.2)
    (herror : ∀ i : UnaryRunSegment R P, ∀ j ∈ Finset.Icc i.2.val.1 i.2.val.2,
      ‖A j-Astar i.2.val.1 i.2.val.2 j‖ ≤
        C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) :
    (∑ j ∈ (Finset.Ico start finish).filter unary, Real.log (beta j)) ≤
      4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
        4*p*ε*(Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j) := by
  have hmember (i : UnaryRunSegment R P) {j : ℕ}
      (hj : j ∈ Finset.Ico i.2.val.1 i.2.val.2) :
      j ∈ (Finset.Ico start finish).filter unary := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    have hi := Finset.mem_Ico.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hi.1),hi.2.trans_le (hb.2.2.trans hr.2.2)⟩,
      R.inside i.1.val i.1.property j (hb.1.trans hi.1) (hi.2.trans_le hb.2.2)⟩
  have hstart (i : UnaryRunSegment R P) : M ≤ n i.2.val.1 :=
    hmass _ (hmember i (Finset.mem_Ico.mpr ⟨le_rfl,(P i.1).bounds _ i.2.property |>.2.1⟩))
  have hres := unary_runs_residual_sum R P hn hc hc1 (by linarith : 1 ≤ M) hμ hV
    hstart hinterruption profile level hlevel N hendlevel hvariation
  have hdrop := source_unary_runs_weighted_drop R P hn (by linarith : (a-1)/p ≤ 1) hnpos hQ
  have hseg (i : UnaryRunSegment R P) :
      (∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Real.log (beta j)) ≤
      4*p*n i.2.val.1^((a-1)/p-1)*
        (C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) := by
    have hb := (P i.1).bounds i.2.val i.2.property
    apply source_unary_segment_log_cost n A (Astar i.2.val.1 i.2.val.2) beta
      hb.2.1.le hp ha hap ?_ (hM.trans (hstart i)) hn
      ((P i.1).drop_lt_two _ i.2.property).le (hcontraction i) (hend i)
      (fun j hj => hbeta j (hmember i hj)) (fun j hj => hprediction j (hmember i hj)) (herror i)
    exact add_nonneg (mul_nonneg hC (intervalOscillation_nonneg ..))
      (mul_nonneg hε (sub_nonneg.mpr (hn hb.2.1.le)))
  calc
    _ = ∑ i : UnaryRunSegment R P,
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Real.log (beta j) := (R.sum_segments P _).symm
    _ ≤ ∑ i : UnaryRunSegment R P, 4*p*n i.2.val.1^((a-1)/p-1)*
        (C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) := Finset.sum_le_sum (fun i _ => hseg i)
    _ = 4*p*C*(∑ i : UnaryRunSegment R P, n i.2.val.1^(-1+(a-1)/p)*
          intervalOscillation profile N (level i.2.val.1) (level i.2.val.2))+
        4*p*ε*(∑ i : UnaryRunSegment R P, n i.2.val.1^((a-1)/p-1)*
          (n i.2.val.1-n i.2.val.2)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show -1+(a-1)/p = (a-1)/p-1 by ring]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hres (by positivity))
      (mul_le_mul_of_nonneg_left hdrop (by positivity))

/-- The comparison amplitudes used above can be the literal products of
the path coefficients and the endpoint amplitude. This discharges their
contraction and endpoint conditions from the true unary recurrence. -/
theorem source_unary_propagated_log_cost {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] (A U W : ℕ → E) (coeff : ℕ → ℂ) (beta : ℕ → ℝ)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level finish ≤ N) (hn : Antitone n)
    {a p c M V C ε Q : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hmass : ∀ j ∈ (Finset.Ico start finish).filter unary, M ≤ n j)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^((a-1)/p) ≤ Q)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬unary j → c ≤ n j-n (j+1))
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hbeta : ∀ j ∈ (Finset.Ico start finish).filter unary, 0 < beta j)
    (hprediction : ∀ j ∈ (Finset.Ico start finish).filter unary, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (hcoeff : ∀ j ∈ (Finset.Ico start finish).filter unary, ‖coeff j‖ ≤ 1)
    (hstep : ∀ j ∈ (Finset.Ico start finish).filter unary,
      A j = coeff j • A (j+1)+U j+W j)
    (hW : ∀ j ∈ (Finset.Ico start finish).filter unary, ‖W j‖ ≤ ε*(n j-n (j+1)))
    (hU : ∀ i : UnaryRunSegment R P, ∀ j ∈ Finset.Icc i.2.val.1 i.2.val.2,
      ‖∑ k ∈ Finset.Ico j i.2.val.2, unaryPropagator coeff j k • U k‖ ≤
        C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)) :
    (∑ j ∈ (Finset.Ico start finish).filter unary, Real.log (beta j)) ≤
      4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
        4*p*ε*(Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j) := by
  have hmember (i : UnaryRunSegment R P) {j : ℕ}
      (hj : j ∈ Finset.Ico i.2.val.1 i.2.val.2) :
      j ∈ (Finset.Ico start finish).filter unary := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    have hi := Finset.mem_Ico.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hi.1),hi.2.trans_le (hb.2.2.trans hr.2.2)⟩,
      R.inside i.1.val i.1.property j (hb.1.trans hi.1) (hi.2.trans_le hb.2.2)⟩
  apply source_unary_runs_log_cost R P A
    (fun _ f j => unaryPropagator coeff j f • A f) beta profile level hlevel N
    hendlevel hn hp ha hap hc hc1 hM hμ hV hC hε hmass hnpos hQ
    hinterruption hvariation hbeta hprediction
  · intro i j hj
    exact propagated_endpoint_contraction coeff (A i.2.val.2)
      (Finset.mem_Ico.mp hj).2 (hcoeff j (hmember i hj))
  · intro i
    simp
  · intro i j hj
    have hjb := Finset.mem_Icc.mp hj
    have htail (k : ℕ) (hk : k ∈ Finset.Ico j i.2.val.2) :
        k ∈ (Finset.Ico start finish).filter unary :=
      hmember i (Finset.mem_Ico.mpr
        ⟨hjb.1.trans (Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2⟩)
    have he := unary_perturbation_bound coeff A U W n hjb.2
      (fun k hk => hcoeff k (htail k hk)) (fun k hk => hstep k (htail k hk))
      (hU i j hj) (fun k hk => hW k (htail k hk))
    exact he.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hn hjb.1) _) hε))

/-- The exceptional factor is controlled just by its amplitude and the
baseline mass in its denominator. -/
theorem source_exceptional_factor_le {E : Type*} [NormedAddCommGroup E]
    (A : E) {n denominator M C a p : ℝ}
    (hn : 0 < n) (hden : n ≤ denominator) (hM : n ≤ M+1)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hp : 0 ≤ p) (hA : ‖A‖ ≤ C*n) :
    vertexAmount n A a p/denominator ≤ 1+C^p*(M+1)^(a-1) := by
  have henergy : n^(a-p)*‖A‖^p ≤ C^p*n^a := by
    calc
      _ ≤ n^(a-p)*(C*n)^p := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hA hp) (Real.rpow_nonneg hn.le _)
      _ = C^p*n^a := by
        rw [Real.mul_rpow hC hn.le]
        calc
          n^(a-p)*(C^p*n^p) = C^p*(n^(a-p)*n^p) := by ring
          _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring
  have hbase : vertexAmount n A a p/denominator ≤ vertexAmount n A a p/n :=
    div_le_div_of_nonneg_left (vertexAmount_pos (a := a) (p := p) hn A).le hn hden
  apply hbase.trans
  calc
    _ ≤ (n+C^p*n^a)/n := div_le_div_of_nonneg_right (by
      unfold vertexAmount
      linarith) hn.le
    _ = 1+C^p*n^(a-1) := by
      rw [add_div,div_self hn.ne',mul_div_assoc,← Real.rpow_sub_one hn.ne']
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hn.le hM (show 0 ≤ a-1 by linarith)) (Real.rpow_nonneg hC _))

/-- Split a finite active product into marked, unary and exceptional
indices. The exceptional contribution costs once, even if its logarithm
is negative. -/
theorem source_path_product_of_log_costs (count : ℕ) (marked unary exceptional : ℕ → Prop)
    (beta beta0 : ℕ → ℝ) (markedCost unaryCost exceptionalCost : ℝ)
    (hbeta : ∀ j < count, 0 < beta j) (hbeta0 : ∀ j < count, marked j → 0 < beta0 j)
    (hpartition : ∀ j < count,
      (marked j ∨ unary j ∨ exceptional j) ∧
        ¬(marked j ∧ unary j) ∧ ¬(marked j ∧ exceptional j) ∧ ¬(unary j ∧ exceptional j))
    (hmarked : (∑ j ∈ (Finset.range count).filter marked,
      (Real.log (beta j)-Real.log (beta0 j))) ≤ markedCost)
    (hunary : (∑ j ∈ (Finset.range count).filter unary, Real.log (beta j)) ≤ unaryCost)
    (hexceptional : Set.Subsingleton {j | j < count ∧ exceptional j})
    (hcost : 0 ≤ exceptionalCost)
    (hexbound : ∀ j < count, exceptional j → Real.log (beta j) ≤ exceptionalCost) :
    (∏ j ∈ Finset.range count, beta j) ≤
      Real.exp (markedCost+unaryCost+exceptionalCost)*
        ∏ j ∈ Finset.range count, if marked j then beta0 j else 1 := by
  classical
  have hexsum : (∑ j ∈ (Finset.range count).filter exceptional, Real.log (beta j)) ≤
      exceptionalCost := by
    let S := (Finset.range count).filter exceptional
    have hsub : (S : Set ℕ).Subsingleton := by
      intro i hi j hj
      exact hexceptional ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1,
        (Finset.mem_filter.mp hi).2⟩ ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
    by_cases hempty : S = ∅
    · simpa only [S,hempty,Finset.sum_empty] using hcost
    · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hS : S = {j} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hj,fun i hi => hsub hi hj⟩
      change (∑ j ∈ S, Real.log (beta j)) ≤ exceptionalCost
      rw [hS,Finset.sum_singleton]
      exact hexbound j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (Finset.mem_filter.mp hj).2
  have hsplit :
      (∑ j ∈ Finset.range count, (Real.log (beta j)-
        Real.log (if marked j then beta0 j else 1))) =
      (∑ j ∈ (Finset.range count).filter marked, (Real.log (beta j)-Real.log (beta0 j)))+
      (∑ j ∈ (Finset.range count).filter unary, Real.log (beta j))+
      (∑ j ∈ (Finset.range count).filter exceptional, Real.log (beta j)) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hcover,hmU,hmE,huE⟩ := hpartition j (Finset.mem_range.mp hj)
    rcases hcover with hm | hu | he
    · have hnu : ¬unary j := fun h => hmU ⟨hm,h⟩
      have hne : ¬exceptional j := fun h => hmE ⟨hm,h⟩
      simp [hm,hnu,hne]
    · have hnm : ¬marked j := fun h => hmU ⟨h,hu⟩
      have hne : ¬exceptional j := fun h => huE ⟨hu,h⟩
      simp [hu,hnm,hne]
    · have hnm : ¬marked j := fun h => hmE ⟨h,he⟩
      have hnu : ¬unary j := fun h => huE ⟨h,he⟩
      simp [he,hnm,hnu]
  have hmodel (j : ℕ) (hj : j < count) : 0 < if marked j then beta0 j else 1 := by
    split_ifs with hm
    · exact hbeta0 j hj hm
    · norm_num
  have hlog : Real.log (∏ j ∈ Finset.range count, beta j)-
      Real.log (∏ j ∈ Finset.range count, if marked j then beta0 j else 1) ≤
        markedCost+unaryCost+exceptionalCost := by
    rw [Real.log_prod (fun j hj => (hbeta j (Finset.mem_range.mp hj)).ne'),
      Real.log_prod (fun j hj => (hmodel j (Finset.mem_range.mp hj)).ne'),← Finset.sum_sub_distrib,
      hsplit]
    linarith
  have hmodelp := Finset.prod_pos (s := Finset.range count)
    (fun j hj => hmodel j (Finset.mem_range.mp hj))
  have hactualp := Finset.prod_pos (s := Finset.range count)
    (fun j hj => hbeta j (Finset.mem_range.mp hj))
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub,Real.exp_log hactualp,Real.exp_log hmodelp] at he
  exact (div_le_iff₀ hmodelp).mp he

/-- The exact marked correction for the parent amplitude and its literal
residual-free value. The square sum is over the marked blocks only. -/
theorem source_marked_log_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    (A residual : ℕ → E) (denominator : ℕ → ℝ)
    {a p c M B : ℝ} (hp : 1 ≤ p) (hc : 0 < c) (hM : 1 ≤ M)
    (hμ : (a-1)/p ≤ 1/12) (hB : 0 ≤ B)
    (hdrop : ∀ j ∈ S, c ≤ n j-n (j+1))
    (hmass : ∀ j ∈ S, M ≤ n j) (hden : ∀ j ∈ S, 0 < denominator j)
    (hsquare : (∑ j ∈ S, ‖residual j‖^2) ≤ B^2) :
    (∑ j ∈ S, (Real.log (vertexAmount (n j) (A j) a p/denominator j)-
      Real.log (vertexAmount (n j) (A j-residual j) a p/denominator j))) ≤
      p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B := by
  apply marked_log_cost n hn S A (fun j => A j-residual j) denominator
    hp hc hM hμ hB hdrop hmass hden
  simpa only [sub_sub_cancel] using hsquare

/-- Actual vertex ratios admit the finite source path bound. The unary
cost is supplied by `source_unary_runs_log_cost`; the marked cost and
unique exceptional factor are proved here from their local data. -/
theorem source_path_product_from_vertex_costs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (count : ℕ) (n : ℕ → ℝ) (A residual : ℕ → E) (denominator : ℕ → ℝ)
    (marked : ℕ → Prop) {a p c M B U C : ℝ}
    (hn : Antitone n) (hp : 1 ≤ p) (ha : 1 ≤ a) (hc : 0 < c)
    (hM : 1 ≤ M) (hμ : (a-1)/p ≤ 1/12) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hactive : ∀ j < count, M < n j)
    (hden : ∀ j < count, n j ≤ denominator j)
    (hdrop : ∀ j < count, marked j → c ≤ n j-n (j+1))
    (hsquare : (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2)
    (hunary : (∑ j ∈ (Finset.range count).filter
      (fun j => ¬marked j ∧ n j-n (j+1) < 1),
      Real.log (vertexAmount (n j) (A j) a p/denominator j)) ≤ U)
    (hexstop : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M)
    (hexmass : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1)
    (hexamp : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖A j‖ ≤ C*n j) :
    (∏ j ∈ Finset.range count, vertexAmount (n j) (A j) a p/denominator j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B+U+
        Real.log (1+C^p*(M+1)^(a-1)))*
      ∏ j ∈ Finset.range count,
        if marked j then vertexAmount (n j) (A j-residual j) a p/denominator j else 1 := by
  classical
  let unary := fun j => ¬marked j ∧ n j-n (j+1) < 1
  let exceptional := fun j => ¬marked j ∧ 1 ≤ n j-n (j+1)
  have hnp (j : ℕ) (hj : j < count) : 0 < n j := by linarith [hactive j hj]
  have hdp (j : ℕ) (hj : j < count) : 0 < denominator j :=
    (hnp j hj).trans_le (hden j hj)
  have hmark := source_marked_log_cost n hn ((Finset.range count).filter marked)
    A residual denominator hp hc hM hμ hB
    (fun j hj => hdrop j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      (Finset.mem_filter.mp hj).2)
    (fun j hj => (hactive j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).le)
    (fun j hj => hdp j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)) hsquare
  apply source_path_product_of_log_costs count marked unary exceptional
    (fun j => vertexAmount (n j) (A j) a p/denominator j)
    (fun j => vertexAmount (n j) (A j-residual j) a p/denominator j)
    (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B) U
    (Real.log (1+C^p*(M+1)^(a-1)))
  · intro j hj
    exact div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj)
  · intro j hj _
    exact div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj)
  · intro j _
    dsimp only [unary,exceptional]
    by_cases hm : marked j
    · tauto
    · have hd : ¬(n j-n (j+1) < 1 ∧ 1 ≤ n j-n (j+1)) := by
        rintro ⟨h₁,h₂⟩
        exact (not_lt_of_ge h₂) h₁
      rcases lt_or_ge (n j-n (j+1)) 1 with h | h <;> tauto
  · exact hmark
  · simpa only [Finset.sum_filter,unary] using hunary
  · exact source_exceptional_index_unique n M hn
      (fun j => j < count ∧ exceptional j)
      (fun j hj => hactive j hj.1)
      (fun j hj => hexstop j hj.1 hj.2.1 hj.2.2)
  · apply Real.log_nonneg
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hC _)
      (Real.rpow_nonneg (by linarith : 0 ≤ M+1) _))
  · intro j hj hex
    apply Real.log_le_log (div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj))
    exact source_exceptional_factor_le (A j) (hnp j hj) (hden j hj)
      (hexmass j hj hex.1 hex.2) hC ha (by linarith) (hexamp j hj hex.1 hex.2)

/-- Assemble the full finite active path directly from residual square
sums, the common cubic variation, and the actual propagated recurrence.
The only interval hypothesis is the Abel bound on the propagated main
residuals. It is imposed on unary intervals of total drop below two,
exactly the intervals constructed in the proof. -/
theorem source_path_product_from_propagated_residuals
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [NormedAddCommGroup F]
    (count : ℕ) (n : ℕ → ℝ) (A U W residual : ℕ → E)
    (coeff : ℕ → ℂ) (denominator : ℕ → ℝ) (marked : ℕ → Prop)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level count ≤ N) (hn : Antitone n)
    {a p c M B V C ε Q Cex : ℝ}
    (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hc : 0 < c) (hc1 : c ≤ 1)
    (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCex : 0 ≤ Cex)
    (hactive : ∀ j < count, M < n j)
    (hden : ∀ j < count, n j ≤ denominator j)
    (hmarked : ∀ j < count, marked j → c ≤ n j-n (j+1))
    (hsquare : (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2)
    (hQ : ∀ j < count, n j^((a-1)/p) ≤ Q)
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hpathden : ∀ j < count, ¬marked j → n j-n (j+1) < 1 →
      n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p ≤ denominator j)
    (hcoeff : ∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖coeff j‖ ≤ 1)
    (hstep : ∀ j < count, ¬marked j → n j-n (j+1) < 1 →
      A j = coeff j • A (j+1)+U j+W j)
    (hW : ∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖W j‖ ≤ ε*(n j-n (j+1)))
    (hU : ∀ e f, e < f → f ≤ count → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f,
        ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
          C*intervalOscillation profile N (level e) (level f))
    (hexstop : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M)
    (hexmass : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1)
    (hexamp : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖A j‖ ≤ Cex*n j) :
    (∏ j ∈ Finset.range count, vertexAmount (n j) (A j) a p/denominator j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B+
        (4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
          4*p*ε*(Q*∑ j ∈ (Finset.range count).filter
            (fun j => ¬marked j ∧ n j-n (j+1) < 1), pathDrop n j))+
        Real.log (1+Cex^p*(M+1)^(a-1)))*
      ∏ j ∈ Finset.range count,
        if marked j then vertexAmount (n j) (A j-residual j) a p/denominator j else 1 := by
  classical
  let unary := fun j => ¬marked j ∧ n j-n (j+1) < 1
  obtain ⟨R⟩ := exists_unary_run_partition unary 0 count (Nat.zero_le count)
  have hparts (r : R.runs) : Nonempty (UnarySegmentPartition n r.val.1 r.val.2) := by
    apply exists_unary_segment_partition n r.val.1 r.val.2
      (R.bounds r.val r.property).2.1.le
    intro j hje hjf
    exact (R.inside r.val r.property j hje hjf).2
  let P := fun r : R.runs => Classical.choice (hparts r)
  have hnp (j : ℕ) (hj : j < count) : 0 < n j := by linarith [hactive j hj]
  have hdp (j : ℕ) (hj : j < count) : 0 < denominator j := (hnp j hj).trans_le (hden j hj)
  have hmem (j : ℕ) (hj : j ∈ @Finset.filter ℕ unary
      (fun j => Classical.propDecidable (unary j)) (Finset.Ico 0 count)) :
      j < count ∧ ¬marked j ∧ n j-n (j+1) < 1 := by
    simpa only [Finset.mem_filter,Finset.mem_Ico,Nat.zero_le,true_and,unary] using hj
  have hlog := source_unary_propagated_log_cost R P A U W coeff
    (fun j => vertexAmount (n j) (A j) a p/denominator j)
    profile level hlevel N hendlevel hn hp ha hap hc hc1 hM hμ hV hC hε
    (fun j hj => (hactive j (hmem j hj).1).le)
    (fun j hj => hnp j (Finset.mem_Ico.mp hj).2)
    (fun j hj => hQ j (Finset.mem_Ico.mp hj).2) ?_ hvariation ?_ ?_
    (fun j hj => hcoeff j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2)
    (fun j hj => hstep j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2)
    (fun j hj => hW j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2) ?_
  · apply source_path_product_from_vertex_costs count n A residual denominator marked
      hn hp ha hc (by linarith : 1 ≤ M) hμ hB hCex hactive hden hmarked hsquare
      ?_ hexstop hexmass hexamp
    simpa only [Nat.Ico_zero_eq_range,Finset.sum_filter,unary] using hlog
  · intro j _ hj hnot
    by_cases hm : marked j
    · exact hmarked j hj hm
    · have hg : 1 ≤ n j-n (j+1) := le_of_not_gt (fun h => hnot ⟨hm,h⟩)
      exact hc1.trans hg
  · intro j hj
    have hjc := (hmem j hj).1
    exact div_pos (vertexAmount_pos (hnp j hjc) _) (hdp j hjc)
  · intro j hj
    obtain ⟨hjc,hm,hs⟩ := hmem j hj
    have hnext : 0 < n (j+1) := by linarith [hactive j hjc]
    have hbase : 0 < n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p :=
      add_pos_of_nonneg_of_pos (sub_nonneg.mpr (hn (Nat.le_succ j))) (vertexAmount_pos hnext _)
    exact div_le_div_of_nonneg_left (vertexAmount_pos (hnp j hjc) _).le hbase
      (hpathden j hjc hm hs)
  · intro i j hj
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    apply hU i.2.val.1 i.2.val.2 hb.2.1 (hb.2.2.trans hr.2.2)
      ((P i.1).drop_lt_two _ i.2.property) ?_ j hj
    intro k hk
    have hki := Finset.mem_Ico.mp hk
    exact R.inside i.1.val i.1.property k (hb.1.trans hki.1) (hki.2.trans_le hb.2.2)

end LipschitzHilbert

end

end OAI
