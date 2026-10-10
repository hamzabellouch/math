import OAI.NumberTheory.TotientAsymptotic.UniquePrefix
import OAI.NumberTheory.TotientAsymptotic.TupleCandidate
import OAI.NumberTheory.TotientAsymptotic.FilteredComparison

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

/-- The exact least-preimage identity on the bijective part of the actual
representation map. Every preimage, including the least one, has this prefix. -/
theorem unique_tuple_least_preimage : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ τ ∈ tupleFinset x H x \ discardedTuples x H,
      ell (tupleValue τ)=tupleLeastCandidate τ := by
  filter_upwards [unique_prefix_finite_comparison,basic_tuple_candidate_realizes,
    eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hbij hc hH hP
  have hPH := P_lt_self hH
  filter_upwards [hbij,hc,common_prefix_inverse_fiber hPH hP,
    theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hbij hc hcommon hs hm
  intro τ hτ
  have hb := (mem_tupleFinset hPH.le).mp (Finset.mem_sdiff.mp hτ).1
  have hv := hbij.2.2.1 hτ
  have hvφ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have hd := (prefix_tail_support hPH hm hs hb.2.2.1).1
  exact ell_of_common_prefix hvφ hd (tuplePrimeProduct_pos hPH.le hb) (hc x τ hb)
    (hcommon τ hτ hbij.2.2.2.1 hv)

def candidateInWindow {r : ℕ} (k : ℕ) (x : ℝ) (τ : TotientTuple r) : Prop :=
  (k : ℝ)*x < tupleLeastCandidate τ ∧ (tupleLeastCandidate τ : ℝ) ≤ (k+1 : ℝ)*x

def candidateTuples (x : ℝ) (H k : ℕ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H x).filter (candidateInWindow k x)

lemma candidate_count_comparison : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ k : ℕ,
    |((candidateTuples x H k).card : ℝ)-N k x| ≤
      (discardedTuples x H).card+(nonuniqueValues x H).card := by
  filter_upwards [unique_tuple_least_preimage,unique_prefix_finite_comparison]
    with H hleast hbij
  filter_upwards [hleast,hbij] with x hleast hbij
  intro k
  have hh := FiniteMap.filtered_card_comparison (tupleFinset x H x) (discardedTuples x H)
    (totientValues x) (nonuniqueValues x H) tupleValue (candidateInWindow k x)
    (fun v : ℕ => (k : ℝ)*x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ)*x)
    hbij.2.2 (fun τ hτ => by rw [hleast τ hτ]; rfl)
  have hN : (((totientValues x).filter (fun v : ℕ =>
      (k : ℝ)*x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ)*x)).card : ℝ)=N k x := by
    simp only [N,totientValues,Finset.filter_filter]
  rw [← hN]
  convert hh using 1
  congr 3
  apply congrArg Finset.card
  ext τ
  simp only [Finset.mem_filter]

end TotientAsymptotic

end

end OAI
