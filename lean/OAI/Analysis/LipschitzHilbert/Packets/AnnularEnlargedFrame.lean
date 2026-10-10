import OAI.Analysis.LipschitzHilbert.Fourier.AnnularEnlargement
import OAI.Analysis.LipschitzHilbert.Packets.AnnularLowerFrame
import OAI.Analysis.LipschitzHilbert.Packets.VerticalFrameSynthesis

namespace OAI

/-! Uniform finite overlap of the enlarged annuli used to reconstruct
outputs whose individual annular projections are in L2. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyEnlarged_real (x : ℝ) : conj (reassemblyEnlarged x)=reassemblyEnlarged x := by
  simp only [reassemblyEnlarged_apply,reassemblyOuter_apply,map_add,Complex.conj_ofReal]

theorem reassemblyEnlarged_norm (x : ℝ) : ‖reassemblyEnlarged x‖≤2 := by
  rw [reassemblyEnlarged_apply]
  have h := (norm_add_le _ _).trans (add_le_add (reassemblyOuter_norm x) (reassemblyOuter_norm (-x)))
  norm_num at h ⊢
  exact h

theorem natural_enlarged_nonzero_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => reassemblyEnlarged ((3/2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => reassemblyEnlarged ((3/2:ℝ)^n*x)≠0)
  change A.card≤3
  have hsep (j k : ℕ) (hj : j∈A) (hk : k∈A) (hjk : j+2≤k) : False := by
    have hjb := reassemblyEnlarged_support _ (Finset.mem_filter.mp hj).2
    have hkb := reassemblyEnlarged_support _ (Finset.mem_filter.mp hk).2
    have hp : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
      calc
        _ = (3/2:ℝ)^(j+2) := by rw [pow_add]; norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hjk
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg x)
    have habs (n : ℕ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
      rw [abs_mul,abs_of_pos (by positivity)]
    rw [habs] at hjb hkb
    nlinarith only [hh,hjb.1,hkb.2]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k j hk hj (by omega)
      · by_contra hn
        exact hsep j k hj hk (by omega)
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem enlarged_annular_square (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range (2*N+1), ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)≤12 := by
  classical
  let I := Finset.range (2*N+1)
  let A := I.filter (fun n => reassemblyEnlarged (reassemblyScale N n*x)≠0)
  have he : (∑ n∈I, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)=
      ∑ n∈A, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : reassemblyEnlarged (reassemblyScale N n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hscale (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
    unfold reassemblyScale
    ring
  have hc : A.card≤3 := by
    simpa only [A,hscale] using natural_enlarged_nonzero_count I ((2/3:ℝ)^N*x)
  change (∑ n∈I, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)≤12
  rw [he]
  calc
    _ ≤ ∑ n∈A, (4:ℝ) := Finset.sum_le_sum fun n _ => by
      have h := reassemblyEnlarged_norm (reassemblyScale N n*x)
      nlinarith [norm_nonneg (reassemblyEnlarged (reassemblyScale N n*x))]
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by exact_mod_cast Nat.mul_le_mul_right 4 hc

end LipschitzHilbert.PacketRepresentation

end

end OAI
