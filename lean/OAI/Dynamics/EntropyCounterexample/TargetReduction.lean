import OAI.Dynamics.EntropyCounterexample.SpectralRadius

namespace OAI

noncomputable section

namespace Problem340

theorem exists_C1_entropy_counterexample_of_witness
    (q : ℕ) (hq : 0 < q)
    (f : CounterexampleManifold q → CounterexampleManifold q)
    (hf : IsC1SelfMap q f)
    (hentropy : Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) =
      (0 : EReal))
    (heigen : ∃ v : RealSingularHomology 2 (CounterexampleManifold q),
      v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v)
    (hbounded : BddAbove (homologyEigenvalueRadii f hf.1))
    (hnotbijective : ¬ Function.Bijective f) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q,
      ∃ hf : IsC1SelfMap q f,
        Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧
        (∃ v : RealSingularHomology 2 (CounterexampleManifold q),
          v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧
        0 < Real.log (2 : ℝ) ∧
        Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧
        ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  refine ⟨q, hq, f, hf, hentropy, heigen, Real.log_pos (by norm_num), ?_,
    hnotbijective, by omega⟩
  obtain ⟨v, hv, hfv⟩ := heigen
  exact log_two_le_log_totalRealHomologySpectralRadius hf.1 hbounded hv hfv

end Problem340

end

end OAI
