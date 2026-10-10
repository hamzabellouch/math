import OAI.Analysis.KadisonKastler.FiniteModuleObstruction

namespace OAI

/-! Finite coefficient approximation suffices to find an exact module map
inside a compact family. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem compact_contains_right_module_of_finite_approximation
    {M : VonNeumannAlgebra H} {c : ℝ}
    (K : Set (BoundedWeakAlgebraMap M c)) (hK : IsCompact K) (hne : K.Nonempty)
    (happrox : ∀ (s : Finset (Algebra M × Algebra M × H × H)) (ε : ℝ), 0 < ε →
      ∃ F ∈ K, ∀ t ∈ s, ‖weakModuleDefect F t.1 t.2.1 t.2.2.1 t.2.2.2‖ ≤ ε) :
    ∃ F ∈ K, ∀ a b, F.map (a * b) = F.map a * b := by
  classical
  by_contra hn
  obtain ⟨s, δ, hδ, hbound⟩ := compact_finite_module_obstruction K hK hne
    (fun F hF hm => hn ⟨F, hF, hm⟩)
  let ε : ℝ := δ / ((s.card : ℝ) + 1)
  have hd : 0 < (s.card : ℝ) + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hd
  obtain ⟨F, hF, hf⟩ := happrox s ε hε
  have hs : (∑ t ∈ s, ‖weakModuleDefect F t.1 t.2.1 t.2.2.1 t.2.2.2‖) ≤
      (s.card : ℝ) * ε := by
    calc
      _ ≤ ∑ _t ∈ s, ε := Finset.sum_le_sum hf
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have he : ε * ((s.card : ℝ) + 1) = δ :=
    div_mul_cancel₀ δ (ne_of_gt hd)
  have hb := (hbound F hF).trans hs
  nlinarith

end

end KadisonKastler

end OAI
