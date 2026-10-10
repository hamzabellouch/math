import OAI.Geometry.CylinderCovering.Radial.FinitePairDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialPairedSweep
open Set Filter
open scoped Topology

@[simp] lemma join_upper {N : ℕ} (U L : Fin N → TriangularCovering.TriCylinder)
    (i : Fin N) : join U L (upperIndex i) = U i := by
  simp only [join, upperIndex, Function.comp_apply, Fin.cast_cast,
    Fin.cast_eq_self, Fin.append_left]

@[simp] lemma join_lower {N : ℕ} (U L : Fin N → TriangularCovering.TriCylinder)
    (i : Fin N) : join U L (lowerIndex i) = L i := by
  simp only [join, lowerIndex, Function.comp_apply, Fin.cast_cast,
    Fin.cast_eq_self, Fin.append_right]

lemma join_totalArea {N : ℕ} (U L : Fin N → TriangularCovering.TriCylinder) :
    TriangularCovering.totalArea (join U L) =
      TriangularCovering.totalArea U + TriangularCovering.totalArea L := by
  change (∑ i : Fin (2 * N),
    (fun k : Fin (N + N) => TriangularCovering.area (Fin.append U L k).base)
      ((finCongr (two_mul N)) i)) = _
  rw [Equiv.sum_comp (finCongr (two_mul N))
    (fun k => TriangularCovering.area (Fin.append U L k).base)]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, TriangularCovering.totalArea]

lemma join_covers_union {N : ℕ} (U L : Fin N → TriangularCovering.TriCylinder)
    {A B : Set Space}
    (hU : ∀ z ∈ A, ∃ i : Fin N, z ∈ (U i).carrier)
    (hL : ∀ z ∈ B, ∃ i : Fin N, z ∈ (L i).carrier) :
    ∀ z ∈ A ∪ B, ∃ i : Fin (2 * N), z ∈ (join U L i).carrier := by
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨i, hi⟩ := hU z hz
    exact ⟨upperIndex i, by simpa only [join_upper] using hi⟩
  · obtain ⟨i, hi⟩ := hL z hz
    exact ⟨lowerIndex i, by simpa only [join_lower] using hi⟩

lemma join_totalArea_tendsto
    (U L : (N : ℕ) → Fin N → TriangularCovering.TriCylinder) {a : ℝ}
    (h : Tendsto (fun N => TriangularCovering.totalArea (U N) +
      TriangularCovering.totalArea (L N)) atTop (𝓝 a)) :
    Tendsto (fun N => TriangularCovering.totalArea (join (U N) (L N))) atTop (𝓝 a) := by
  simpa only [join_totalArea] using h

lemma upperSweep_mono (h ε : ℝ) {R S : ℝ → ℝ}
    (hRS : ∀ q ∈ Icc (-1 : ℝ) 1, R q ≤ S q) :
    upperSweep h ε R ⊆ upperSweep h ε S := by
  rintro z ⟨q, hq, ρ, hρ, x, hx, hz⟩
  exact ⟨q, hq, ρ, ⟨hρ.1, hρ.2.trans (hRS q hq)⟩, x, hx, hz⟩

lemma lowerSweep_mono (h ε : ℝ) {R S : ℝ → ℝ}
    (hRS : ∀ q ∈ Icc (-1 : ℝ) 1, R q ≤ S q) :
    lowerSweep h ε R ⊆ lowerSweep h ε S := by
  rintro z ⟨q, hq, ρ, hρ, y, hy, hz⟩
  exact ⟨q, hq, ρ, ⟨hρ.1, hρ.2.trans (hRS q hq)⟩, y, hy, hz⟩

lemma eventually_strict_finite_cost
    (C : (N : ℕ) → Fin (2 * N) → TriangularCovering.TriCylinder)
    {a target : ℝ}
    (hlim : Tendsto (fun N => TriangularCovering.totalArea (C N)) atTop (𝓝 a))
    (hlt : a < target) :
    ∀ᶠ N in atTop, 0 < N ∧ TriangularCovering.totalArea (C N) < target := by
  exact (eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds hlt))

end CylinderCovering.RadialPairedSweep

end

end OAI
