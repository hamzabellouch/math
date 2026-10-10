import OAI.Probability.DilutedSpin.DictionaryAnalytic

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology
variable {Ω X Y Z : ℕ → Type} [∀ N, Fintype (Ω N)]
    [∀ N, MeasurableSpace (X N)] [∀ N, MeasurableSpace (Y N)]
    [∀ N, Countable (Z N)] [∀ N, MeasurableSpace (Z N)] [∀ N, MeasurableSingletonClass (Z N)]
    {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    {A : K → Type} [∀ q, Fintype (A q)] {L : ℕ} {M : ℕ → ℕ}
    (ξ : (N : ℕ) → Fin (M N) → Measure (Y N)) [∀ N j, IsProbabilityMeasure (ξ N j)]
    (μ : (N : ℕ) → Measure (X N)) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
    (τ : (N : ℕ) → Measure (Z N)) [∀ N, IsProbabilityMeasure (τ N)]
    (r s : ℕ → ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : (N : ℕ) → KernelTower (Ω N) L) (Q : (q : K) → Fin L → FiniteLaw (A q))
    (m : Fin (L+1) → ℝ)
    (base : (N : ℕ) → RootPath (Y N) (M N) → (k : ℕ) → RootPath (X N) k → FinitePath (Ω N) L → ℝ)
    (D E : (N : ℕ) → (q : K) → Z N → FinitePath (Ω N) L → FinitePath (A q) L → ℝ)
    (u : ℕ → K×ℕ → ℝ) (f : (N : ℕ) → (S.Leaf → FinitePath (Ω N) L) → ℝ)

 
theorem dictionary_coefficients_tendsto
    (hb : ∀ N k y, Measurable (fun z : RootPath (Y N) (M N) × RootPath (X N) k => base N z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ N x, |f N x| ≤ B)
    (hD : ∀ N q v x y, |D N q v x y| ≤ 1) (hE : ∀ N q v x y, |E N q v x y| ≤ 1)
    (hc : ∀ q j, 0 < ν.real {(q,j)}) (hs : ∀ N, 0 < s N)
    (he : ∀ q j, Tendsto (fun N => parameterError (ξ N) (μ N) (ν.prod (τ N)) (r N) (s N)
      (T N) (fun i => Q i.1.1) (fun l => m l.succ) (base N) Prod.fst
      (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
      (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (q,j) (u N) /
        (ν.real {(q,j)}*(s N:ℝ))) atTop (𝓝 0)) (q : K) (k : ℕ) :
    Tendsto (fun N => covarianceCoefficient (ξ N) (μ N) (ν.prod (τ N))
      ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
      (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) k)
      atTop (𝓝 0) := by
  let H (N : ℕ) (t : ℝ) := externalCovariance (ξ N) (μ N) (ν.prod (τ N))
    ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
    (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) t 0
  let coeff (N k : ℕ) := covarianceCoefficient (ξ N) (μ N) (ν.prod (τ N))
    ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
    (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (f N) k
  let bound (k : ℕ) := 2*B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase anchor).card) (k+1)/(k.factorial:ℝ)
  let err (j N : ℕ) := B*(parameterError (ξ N) (μ N) (ν.prod (τ N)) (r N) (s N)
    (T N) (fun i => Q i.1.1) (fun l => m l.succ) (base N) Prod.fst
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2) (q,j) (u N) /
      (ν.real {(q,j)}*(s N:ℝ)))
  have hbound (k : ℕ) : 0 ≤ bound k := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) hB) (PrescribedTree.derivativeBound_nonneg _ _)
    · exact Nat.cast_nonneg _
  have hR (N k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      |H N t - ∑ j ∈ Finset.range (k+1), coeff N j*t^j| ≤ bound k*t^(k+1) := by
    exact externalCovariance_taylor_bound (ξ N) (μ N) (ν.prod (τ N))
      ((τ N).map (fun v => ((q,0),v))) (r N) (s N) S anchor (T N) (fun i => Q i.1.1) m (base N)
      (dictionaryFactor (D N) (E N) (u N)) (fun i => D N i.1.1 i.2) (fun i => E N i.1.1 i.2)
      (f N) (hb N) hm hmono hpos hroot hend hB (hf N) (fun i => hD N i.1.1 i.2)
      (fun i => hE N i.1.1 i.2) ht k
  apply coefficients_tendsto_zero_of_uniform_remainders H coeff bound (4*(4+8*(S.leaves:ℝ))*B)
    hbound (by positivity) hR err
    (fun j => by simpa only [mul_zero] using (he q j).const_mul B) _ k
  intro j N
  exact dictionary_covariance_probe_bound (ξ N) (μ N) ν (τ N) (r N) (s N) S anchor (T N) Q m
    (base N) (D N) (E N) (u N) (f N) q j (hb N) hm hmono hpos hroot hend hB (hf N)
    (hD N) (hE N) (hc q j) (hs N)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
