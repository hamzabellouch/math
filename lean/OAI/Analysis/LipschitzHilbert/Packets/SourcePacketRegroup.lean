import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! Exact regrouping of original packet amplitudes by assigned top and
length. This connects the individual-packet residual estimates to the
same top-band amplitudes appearing in the physical path integrals. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem weighted_sum_fibers {σ ι E : Type*} [AddCommMonoid E] [Module ℂ E]
    (packets : Finset σ) (groups : Finset ι) (key : σ → ι)
    (hkey : ∀ q ∈ packets, key q ∈ groups) (weight : ι → ℂ) (value : σ → E) :
    (∑ i ∈ groups, weight i • ∑ q ∈ packets.filter (fun q => key q = i), value q) =
      ∑ q ∈ packets, weight (key q) • value q := by
  calc
    _ = ∑ i ∈ groups, ∑ q ∈ packets.filter (fun q => key q = i), weight (key q) • value q := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hkey _

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The scalar factor at one node is constant on every top/length fiber. -/
def sourceGroupedCoefficient {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (stop : ι → Fin N → ℕ) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (p : ι×Fin N) : ℂ :=
  if g.index level (slope p.1) = cell ∧ level ≤ stop p.1 p.2 then
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      level (stop p.1 p.2) (slope p.1)*
      ((g.mass tops slope precision cutoff weight (stop p.1 p.2)
        (g.index (stop p.1 p.2) (slope p.1)) x^(-a):ℝ):ℂ)
  else 0

theorem sourcePacketAmplitude_grouped_sum {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    ∑ q ∈ packets, g.sourceGroupedCoefficient tops slope precision cutoff weight K gap
      stop phase a x level cell (assigned q,lengthIndex q) • value q := by
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  unfold sourceGroupedCoefficient sourcePacketBase
  split_ifs <;> simp only [smul_smul,zero_smul]

/-- The original packet amplitude equals its literal top/length regrouping.
No estimate, choice of signs, or bound on the number of fibers is used. -/
theorem sourcePacketAmplitude_regroup {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ∑ q ∈ packets.filter (fun q => (assigned q,lengthIndex q) = p), value q)
      phase a x level cell := by
  rw [g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap packets
    assigned lengthIndex stop value phase a x level cell,
    g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst Prod.snd stop]
  symm
  convert weighted_sum_fibers packets (tops ×ˢ (Finset.univ : Finset (Fin N)))
    (fun q => (assigned q,lengthIndex q))
    (fun q hq => Finset.mem_product.mpr ⟨hassigned q hq,Finset.mem_univ _⟩)
    (g.sourceGroupedCoefficient tops slope precision cutoff weight K gap stop phase a x level cell)
    value using 1; congr 1; ext q; simp
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

end AngularGrid
end LipschitzHilbert

end

end OAI
