import OAI.Probability.DilutedSpin.Model

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Set Filter
open scoped Topology

theorem isOpen_exponents (r : ℕ) : IsOpen {m : Fin r → ℝ | Exponents m} := by
  have he : {m : Fin r → ℝ | Exponents m} =
      (⋂ i : Fin r, ⋂ j : Fin r, {m | i < j → m i < m j}) ∩
        (⋂ i : Fin r, {m | 0 < m i ∧ m i < 1}) := by
    ext m
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Exponents, StrictMono]
  rw [he]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases h : i < j
    · simpa only [h, true_implies] using isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp only [h, false_implies, ofPred_true]
      exact isOpen_univ
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem rationalExponent_dense (r : ℕ) :
    DenseRange (fun q : Fin r → ℚ => fun i => (q i : ℝ)) :=
  DenseRange.piMap (fun _ => Rat.denseRange_cast)

theorem exists_rational_exponents {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m)
    {s : Set (Fin r → ℝ)} (hs : s ∈ nhds m) :
    ∃ q : Fin r → ℚ, Exponents (fun i => (q i : ℝ)) ∧ (fun i => (q i : ℝ)) ∈ s := by
  have hn : {m : Fin r → ℝ | Exponents m} ∩ s ∈ nhds m :=
    inter_mem ((isOpen_exponents r).mem_nhds hm) hs
  obtain ⟨x, hx, hxs⟩ := mem_closure_iff_nhds.mp ((rationalExponent_dense r) m) _ hn
  obtain ⟨q, rfl⟩ := hxs
  exact ⟨q, hx.1, hx.2⟩

end FixedClauseThreshold.Computability

end OAI
