import OAI.Analysis.LipschitzHilbert.Fourier.RescaledPartitionedSymbol

namespace OAI

/-! A concrete compact smooth partition on an arithmetic slope lattice.
The finite sum is exactly one on its prescribed interval. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def slopePartitionReal (x : ℝ) : ℝ := Real.smoothTransition (x+1)-Real.smoothTransition x

theorem slopePartitionReal_nonneg (x : ℝ) : 0≤slopePartitionReal x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem slopePartitionReal_le_one (x : ℝ) : slopePartitionReal x≤1 := by
  unfold slopePartitionReal
  linarith [Real.smoothTransition.nonneg x,Real.smoothTransition.le_one (x+1)]

theorem slopePartitionReal_eq_zero (x : ℝ) (hx : x≤-1 ∨ 1≤x) : slopePartitionReal x=0 := by
  rcases hx with hx | hx
  · rw [slopePartitionReal,Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]
  · rw [slopePartitionReal,Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le hx,sub_self]

def slopePartition : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (slopePartitionReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
    intro x hx
    have hxx : x≤-1 ∨ 1≤x := by
      by_cases h : -1≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx1 => hx ⟨h,hx1⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,slopePartitionReal_eq_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) slopePartitionReal
    unfold slopePartitionReal
    fun_prop)

theorem slopePartition_apply (x : ℝ) : slopePartition x=(slopePartitionReal x : ℂ) := rfl

theorem slopePartition_support (x : ℝ) (hx : slopePartition x≠0) : |x|≤1 := by
  by_contra h
  have habs : 1 < |x| := lt_of_not_ge h
  have hxx : x≤-1 ∨ 1≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at habs
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at habs
      exact Or.inr habs.le
  have heq := slopePartitionReal_eq_zero x hxx
  exact hx (by rw [slopePartition_apply,heq,Complex.ofReal_zero])

theorem slopePartitionReal_sum (x : ℝ) (N : ℕ) :
    ∑ n∈Finset.range N, slopePartitionReal (x-(n:ℝ))=
      Real.smoothTransition (x+1)-Real.smoothTransition (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,slopePartitionReal]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

theorem slopePartition_sum_one (K : ℕ) (x : ℝ) (hx : |x|≤K) :
    ∑ n∈Finset.range (2*K+1), slopePartition (x+K-(n:ℝ))=1 := by
  simp only [slopePartition_apply,←Complex.ofReal_sum]
  rw [slopePartitionReal_sum]
  have hbounds := abs_le.mp hx
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
