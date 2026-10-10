import OAI.Analysis.LipschitzHilbert.Packets.SourceBoundaryPacketError
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualVariation

namespace OAI

/-! Exact finite-packet regrouping for the expected boundary error.
The only prefix bound is on the original packet values. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem packet_stopping_prefix_bound {N : ℕ} (packets : Finset σ)
    (lengthIndex : σ → Fin N) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (value : σ → E) (B : ℝ)
    (hinterval : ∀ l u : ℕ, l ≤ u → u ≤ N →
      ‖∑ s ∈ packets.filter (fun s => l ≤ (lengthIndex s).val ∧ (lengthIndex s).val < u), value s‖ ≤ B)
    (k : ℕ) :
    ‖∑ s ∈ packets.filter (fun s => stop (lengthIndex s) ≤ k), value s‖ ≤ B := by
  obtain ⟨l,u,hlu,hu,hband⟩ := antitone_stopping_band_interval stop hstop 0 (k+1)
  have hset : packets.filter (fun s => stop (lengthIndex s) ≤ k) =
      packets.filter (fun s => l ≤ (lengthIndex s).val ∧ (lengthIndex s).val < u) := by
    ext s
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    simpa only [Nat.zero_le,true_and,Nat.lt_add_one_iff] using hband (lengthIndex s)
  rw [hset]
  exact hinterval l u hlu hu

theorem sum_weighted_stopping_fibers (packets : Finset σ) (stop : σ → ℕ)
    (value : σ → E) (w : ℕ → ℂ) (M : ℕ) (hmax : ∀ s ∈ packets, stop s ≤ M) :
    (∑ j ∈ Finset.range (M+1), w j • ∑ s ∈ packets.filter (fun s => stop s = j), value s) =
      ∑ s ∈ packets, w (stop s) • value s := by
  calc
    _ = ∑ j ∈ Finset.range (M+1), ∑ s ∈ packets.filter (fun s => stop s = j),
        w (stop s) • value s := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax s hs))) _

namespace AngularGrid
variable {τ X : Type*} [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_finite_packet_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (M : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) M) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (stop : σ → ℕ) (value : σ → E)
    (hmax : ∀ s ∈ packets, stop s ≤ M) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ M, ‖∑ s ∈ packets.filter (fun s => stop s ≤ k), value s‖ ≤ B) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖∑ s ∈ packets,
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) (stop s) top a x : ℝ):ℂ) • value s‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*B*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon err
  let f := fun j => ∑ s ∈ packets.filter (fun s => stop s = j), value s
  have hprefix (k : ℕ) (hk : k ≤ M) : ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B := by
    dsimp only [f]
    rw [← Nat.Ico_zero_eq_range, sum_packet_stopping_fibers]
    simpa only [Nat.zero_le,true_and,Nat.lt_add_one_iff] using hB k hk
  have hb := g.source_boundary_expected_packet_error L hbranch hsmall tops slope precision cutoff weight
    hp hw hK M top htop he a ha x f B hB0 hprefix
  have heq : (fun origin => ‖∑ j ∈ Finset.range (M+1),
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) j top a x : ℝ):ℂ) • f j‖) = err := by
    funext origin
    congr 1
    exact sum_weighted_stopping_fibers packets stop value _ M hmax
  simpa only [heq] using hb

end AngularGrid
end LipschitzHilbert

end

end OAI
