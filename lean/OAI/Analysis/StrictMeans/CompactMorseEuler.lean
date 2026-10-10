import OAI.Analysis.StrictMeans.SmoothSublevelEuler

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_halfPlane_morse_sum {u : ℂ → ℝ} {c : ℝ}
    (hK : IsCompact {z : ℂ | 0<z.im ∧ u z≤c})
    (hne : (interior {z : ℂ | 0<z.im ∧ u z≤c}).Nonempty)
    (C : Finset ℂ)
    (hc : ∀ z, 0<z.im ∧ u z≤c → (fderiv ℝ u z=0 ↔ z∈C))
    (hC : ∀ p∈C, p∈interior {z : ℂ | 0<z.im ∧ u z≤c})
    (hu : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ 2 u z)
    (htr : ∀ z : ℂ, 0<z.im → 0<second u z 1 1+second u z Complex.I Complex.I)
    (hdet : ∀ p∈C, hessianDet u p≠0) :
    1≤∑ p∈C, morseSign u p := by
  classical
  obtain ⟨o,hlower⟩ := smooth_halfPlane_sublevel_index_lower hK hne hu htr
  have heq := compact_morse_index_sum hK C hc hC
    (fun z hz=>hu z hz.1) (fun z hz=>htr z (interior_subset (hC z hz)).1) hdet
  obtain ⟨s,hs,hl,he⟩ := (hlower.and heq).exists_gt
  let S := (meshPoint_bounded_preimage (o:=o) hs.ne' hK.isBounded).toFinset
  have hS : ∀ v, v∈S ↔ 0<(meshPoint o s v).im ∧ u (meshPoint o s v)≤c := by
    intro v
    exact Set.Finite.mem_toFinset _
  rw [← he hs o S hS]
  exact hl hs S hS

end
end StrictInverseFirstPower.Grid

end

end OAI
