import OAI.MeasureTheory.Falconer.Angular.StationaryChartAmplitude

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem extendedStationaryInverse_zero : extendedStationaryInverse 0 = 0 := by
  rw [extendedStationaryInverse_eq (by norm_num)]
  simp [stationarySineInverse]

 theorem stationaryWeight_zero : stationaryWeight 0 = 1 := by
  have h : stationaryCutoff (0:ℝ) = 1 := stationaryCutoff.one_of_mem_closedBall
    (by simp [stationaryCutoff])
  simp [stationaryWeight,stationarySineJacobian,h]

 theorem stationaryAmplitude_zero (f : ℝ → ℂ) : stationaryAmplitude f 0 = f 0 := by
  simp [stationaryAmplitude,stationaryWeight_zero,extendedStationaryInverse_zero]

noncomputable def stationaryJet (n : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℂ) *
    iteratedDeriv k (fun u => (stationaryWeight u : ℂ)) 0 *
      ∑ c : OrderedFinpartition (n-k),
        ((∏ j, iteratedDeriv (c.partSize j) extendedStationaryInverse 0 : ℝ):ℂ) *
          iteratedDeriv c.length f 0

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

 theorem stationaryAmplitude_jet (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (stationaryAmplitude f) 0 = stationaryJet n f := by
  have hw : ContDiff ℝ ∞ (fun u => (stationaryWeight u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff
  have hfn : ContDiffAt ℝ n (f ∘ extendedStationaryInverse) 0 :=
    ((hf.comp extendedStationaryInverse_contDiff).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hwn : ContDiffAt ℝ n (fun u => (stationaryWeight u : ℂ)) 0 :=
    (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change iteratedDeriv n (fun u => (stationaryWeight u : ℂ) *
    (f ∘ extendedStationaryInverse) u) 0 = _
  rw [iteratedDeriv_fun_mul hwn hfn]
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt
    extendedStationaryInverse_contDiff.contDiffAt
      (WithTop.coe_le_coe.mpr (show ((n-k:ℕ):ℕ∞) ≤ ⊤ from le_top))]
  simp only [extendedStationaryInverse_zero,Complex.real_smul]

 theorem stationaryJet_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    stationaryJet 0 f = f 0 := by
  rw [← stationaryAmplitude_jet 0 hf,iteratedDeriv_zero,stationaryAmplitude_zero]

noncomputable def directStationaryOperator (j : ℕ) (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ((Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) *
    (((j.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^j *
      stationaryJet (2*j) (fun u => f (u+θ))

 theorem directStationaryOperator_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (θ : ℝ) :
    directStationaryOperator 0 f θ =
      ((Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) * f θ := by
  unfold directStationaryOperator
  have ht : ContDiff ℝ ∞ (fun u => f (u+θ)) := hf.comp (contDiff_id.add contDiff_const)
  simp only [mul_zero]
  rw [stationaryJet_zero ht]
  simp

end PlanarFalconer

end OAI
