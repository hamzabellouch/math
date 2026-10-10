import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth

namespace OAI

/-! The unphased, scaled incoming cutoff is an actual invariant
scalar. Its arithmetic sum is locally finite at all scales at least one. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaScalarCuspTerm (N : ℝ) (r : CubicThetaBottomRow) (p : ℂ × ℝ) : ℂ :=
  cubicThetaCuspCutoff (r.height p/N)

def cubicThetaScalarCusp (N : ℝ) (p : ℂ × ℝ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaScalarCuspTerm N r p

lemma cubicThetaScalarCuspTerm_zero (N : ℝ) (hN : 0<N) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : r.height p≤N) : cubicThetaScalarCuspTerm N r p=0 :=
  cubicThetaCuspCutoff_zero ((div_le_one hN).mpr hp)

lemma cubicThetaScalarCuspTerm_high {N : ℝ} (hN : 1≤N) {r : CubicThetaBottomRow}
    {p : ℂ × ℝ} (h : cubicThetaScalarCuspTerm N r p≠0) : 1<r.height p := by
  have hp : N<r.height p := by
    by_contra hn
    exact h (cubicThetaScalarCuspTerm_zero N (by linarith) r (le_of_not_gt hn))
  exact lt_of_le_of_lt hN hp

lemma cubicThetaScalarCusp_finite {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ} (hp : 0<p.2) :
    (Function.support (fun r => cubicThetaScalarCuspTerm N r p)).Finite := by
  apply Set.Subsingleton.finite
  intro r hr t ht
  exact cubicThetaIncomingRows_unique hp (cubicThetaScalarCuspTerm_high hN hr)
    (cubicThetaScalarCuspTerm_high hN ht)

lemma cubicThetaScalarCusp_compact_sum {N : ℝ} (hN : 1≤N)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K,
      cubicThetaScalarCusp N p=∑ r∈S, cubicThetaScalarCuspTerm N r p := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hp
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact cubicThetaScalarCuspTerm_zero N (by linarith) r ((hS p hp r hr).le.trans hN)

lemma cubicThetaScalarCusp_smooth {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (cubicThetaScalarCusp N) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaScalarCusp_compact_sum hN hK hpos
  have he : cubicThetaScalarCusp N=ᶠ[𝓝 p] (fun q => ∑ r∈S, cubicThetaScalarCuspTerm N r q) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaScalarCuspTerm N r q) p :=
    ContDiffAt.sum (fun r _ => cubicThetaCuspCutoff_smooth.contDiffAt.comp p
      ((r.height_contDiffAt hp).div_const N))
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

lemma cubicThetaScalarCusp_invariant (N : ℝ) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaPrincipalComplex g) p)=
      cubicThetaScalarCusp N p := by
  unfold cubicThetaScalarCusp cubicThetaScalarCuspTerm
  simp_rw [← CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaCuspCutoff (r.height p/N))

lemma cubicThetaScalarCusp_high {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ}
    (hp : 2*N≤p.2) : cubicThetaScalarCusp N p=1 := by
  have hp1 : 1<p.2 := by linarith
  have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N cubicThetaZeroRow p := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hc := r.high_height_c_zero hp1 (cubicThetaScalarCuspTerm_high hN hn)
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  apply cubicThetaCuspCutoff_one
  have hz : cubicThetaZeroRow.height p=p.2 := by simp [CubicThetaBottomRow.height,cubicThetaZeroRow,norm]
  rw [hz]
  exact (le_div_iff₀ (by linarith : 0<N)).mpr hp

end CubicFirstMoment

end

end OAI
