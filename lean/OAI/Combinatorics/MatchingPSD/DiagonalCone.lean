import Mathlib
import OAI.Combinatorics.MatchingPSD.PSDCompression
import OAI.Combinatorics.MatchingPSD.PSDTopology
import OAI.Combinatorics.MatchingPSD.MatrixBounds

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma evaluationCone_isClosed_of_diagonal (B : I → Matrix R R ℝ)
    (hB : ∀ i, (B i).PosSemidef) (d : R → ℝ)
    (hs : ∑ i, B i = diagonal d) : IsClosed (evaluationCone B) := by
  classical
  apply IsSeqClosed.isClosed
  intro u y hu hy
  choose A hA heA using hu
  have hc (k : ℕ) := diagonal_compression B hB d hs (A k) (hA k)
  choose C hC heC hzC using hc
  have heval (k : ℕ) : evaluation B (C k) = u k := (heC k).trans (heA k)
  have hsum : Filter.Tendsto (fun k => ∑ i, u k i) Filter.atTop (nhds (∑ i, y i)) :=
    tendsto_finsetSum _ (fun i _ => (tendsto_pi_nhds.mp hy) i)
  obtain ⟨b, hb⟩ := hsum.bddAbove_range
  have hbound (k : ℕ) : ∑ i, u k i ≤ b := hb (Set.mem_range_self k)
  let a : ℝ := ∑ j, (d j)⁻¹
  have ha : 0 ≤ a := Finset.sum_nonneg (fun j _ =>
    inv_nonneg.mpr (sum_diagonal_nonneg B hB d hs j))
  have htr (k : ℕ) : (C k).trace ≤ a * b := by
    refine (diagonal_trace_bound B hB d hs (C k) (hC k) (hzC k)).trans ?_
    rw [heval]
    exact mul_le_mul_of_nonneg_left (hbound k) ha
  let lo : R → R → ℝ := fun _ _ => -(a * b)
  let hi : R → R → ℝ := fun _ _ => a * b
  have hm (k : ℕ) : C k ∈ Set.Icc lo hi := by
    constructor <;> intro i j
    · exact (abs_le.mp ((PerfectMatchingPSD.posSemidef_entry_abs_le_trace (hC k) i j).trans
        (htr k))).1
    · exact (abs_le.mp ((PerfectMatchingPSD.posSemidef_entry_abs_le_trace (hC k) i j).trans
        (htr k))).2
  obtain ⟨L, hL, φ, hφ, ht⟩ := IsCompact.tendsto_subseq (X := R → R → ℝ) (isCompact_Icc : IsCompact (Set.Icc lo hi)) hm
  have hpsd : Matrix.PosSemidef L := psd_isClosed.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun k => hC (φ k)))
  refine ⟨L, hpsd, ?_⟩
  have hlim := (evaluation_continuous B).continuousAt.tendsto.comp ht
  have hlim' := hy.comp hφ.tendsto_atTop
  have hEq : evaluation B ∘ (C ∘ φ) = u ∘ φ := by ext k i; exact congrFun (heval (φ k)) i
  have hlim := hlim.congr (fun k => congrFun hEq k)
  exact tendsto_nhds_unique hlim hlim'

end AffinePSD

end OAI
