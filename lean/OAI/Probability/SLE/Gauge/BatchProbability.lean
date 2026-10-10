import OAI.Probability.SLE.Gauge.BatchEntryOrder
import OAI.Probability.SLE.Gauge.BatchAdaptedFailure

namespace OAI

/-! Reindexing the prescribed repeated tests preserves their probability
budget. The finite adapted failure estimate therefore applies to the actual
batch, with its repetitions, rather than just to distinct thresholds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma adapted_fin_successes_failure_exp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) {N : ℕ} (success : Fin N → Set Ω)
    (hmeas : ∀ i, MeasurableSet[F (i.val+1)] (success i))
    (p : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hstep : ∀ i (A : Set Ω), MeasurableSet[F i.val] A →
      ENNReal.ofReal (p i)*P A ≤ P (A∩success i)) :
    P (⋂ i, (success i)ᶜ) ≤ ENNReal.ofReal (Real.exp (-(∑ i, p i))) := by
  classical
  let s : ℕ → Set Ω := fun i => if h : i<N then success ⟨i,h⟩ else ∅
  let q : ℕ → ℝ := fun i => if h : i<N then p ⟨i,h⟩ else 0
  have hm (i) : MeasurableSet[F (i+1)] (s i) := by
    dsimp only [s]
    split_ifs with h
    · exact hmeas ⟨i,h⟩
    · exact @MeasurableSet.empty Ω (F (i+1))
  have h0 (i) : 0 ≤ q i := by
    dsimp only [q]
    split_ifs with h
    · exact hp0 ⟨i,h⟩
    · exact le_rfl
  have h1 (i) : q i ≤ 1 := by
    dsimp only [q]
    split_ifs with h
    · exact hp1 ⟨i,h⟩
    · norm_num
  have hs (i) (A : Set Ω) (hA : MeasurableSet[F i] A) :
      ENNReal.ofReal (q i)*P A ≤ P (A∩s i) := by
    by_cases hi : i<N
    · simpa only [q,s,dite_eq_left hi] using hstep ⟨i,hi⟩ A hA
    · simp [q,s,hi]
  have h := adapted_successes_failure_exp_bound P F s hm q h0 h1 hs N
  have he : (⋂ i∈Finset.range N, (s i)ᶜ) = ⋂ i, (success i)ᶜ := by
    ext ω
    simp only [mem_iInter,Finset.mem_range,mem_compl_iff]
    constructor
    · intro h i
      simpa only [s,dite_eq_left i.isLt] using h i.val i.isLt
    · intro h i hi
      simpa only [s,dite_eq_left hi] using h ⟨i,hi⟩
  have hsum : (∑ i∈Finset.range N, q i) = ∑ i : Fin N, p i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [q,dite_eq_left i.isLt]
  rwa [he,hsum] at h

namespace Target

lemma repeated_batch_sum_eq (κ : ℝ) (W : WienerLaw) (n J : ℕ)
    (e : Fin J → ℤ × ℕ) (hi : Function.Injective e)
    (he : ∀ kj, kj ∈ Set.range e ↔ kj.2 < multiplicity κ W n kj.1)
    (q : ℤ → ℝ) :
    (∑ i, q (e i).1) = ∑' k : ℤ, (multiplicity κ W n k : ℝ)*q k := by
  classical
  let f : Fin J → Σ k : ℤ, Fin (multiplicity κ W n k) := fun i =>
    ⟨(e i).1,(e i).2,(he (e i)).mp ⟨i,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hi
      have h := congrArg (fun p : Σ k : ℤ, Fin (multiplicity κ W n k) => (p.1,p.2.val)) hij
      simpa only [f] using h
    · rintro ⟨k,j⟩
      obtain ⟨i,hi⟩ := (he (k,j.val)).mpr j.isLt
      refine ⟨i,?_⟩
      dsimp only [f]
      refine Sigma.ext (congrArg Prod.fst hi) ?_
      exact (Fin.heq_ext_iff (congrArg (multiplicity κ W n) (congrArg Prod.fst hi))).2
        (congrArg Prod.snd hi)
  let E := Equiv.ofBijective f hf
  let : Fintype (Σ k : ℤ, Fin (multiplicity κ W n k)) := Fintype.ofEquiv (Fin J) E
  calc
    (∑ i, q (e i).1) = ∑' i, q (e i).1 := (tsum_fintype _).symm
    _ = ∑' p : Σ k : ℤ, Fin (multiplicity κ W n k), q p.1 :=
      E.tsum_eq (fun p : Σ k : ℤ, Fin (multiplicity κ W n k) => q p.1)
    _ = ∑' k : ℤ, ∑' _j : Fin (multiplicity κ W n k), q k :=
      (Summable.of_finite).tsum_sigma' (fun _ => Summable.of_finite)
    _ = _ := by simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end Target

/-- Half of each centered success probability is enough for the paper's
exponent, even when the tests are dependent and the thresholds repeat. -/
theorem repeated_batch_failure_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (κ : ℝ) (W : Target.WienerLaw) (n J : ℕ)
    (e : Fin J → ℤ × ℕ) (hi : Function.Injective e)
    (he : ∀ kj, kj ∈ Set.range e ↔ kj.2 < Target.multiplicity κ W n kj.1)
    (q : ℤ → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hbudget : (2:ℝ)^n/8 ≤ ∑' k, (Target.multiplicity κ W n k:ℝ)*q k)
    (success : Fin J → Set Ω)
    (hmeas : ∀ i, MeasurableSet[F (i.val+1)] (success i))
    (hstep : ∀ i (A : Set Ω), MeasurableSet[F i.val] A →
      ENNReal.ofReal (q (e i).1/2)*P A ≤ P (A∩success i)) :
    P (⋂ i, (success i)ᶜ) ≤ ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  have hb : (2:ℝ)^n/8 ≤ ∑ i, q (e i).1 := by
    rwa [Target.repeated_batch_sum_eq κ W n J e hi he q]
  have hp0 (i) : 0 ≤ q (e i).1/2 := div_nonneg (hq0 _) (by norm_num)
  have hp1 (i) : q (e i).1/2 ≤ 1 := by linarith [hq1 (e i).1]
  refine (adapted_fin_successes_failure_exp_bound P F success hmeas
    (fun i => q (e i).1/2) hp0 hp1 hstep).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [← Finset.sum_div]
  linarith

end SLEExactGauge

end

end OAI
