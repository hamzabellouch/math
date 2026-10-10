import OAI.Probability.InvariantIsing.Fields.PriorFrozenCGF
import OAI.Probability.InvariantIsing.Spectral.SpectralGG
import OAI.Probability.InvariantIsing.Pressure.PressureCoordinateMinimum

namespace OAI

/-! The selected Gaussian energy at the actual constrained-prior minimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma priorFrozenCGF_mean_bounds {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ) :
    0≤(∫ p, priorFrozenCGF ν eig c I degree amplitude r h j t p
      ∂(priorFrozenLaw μ j).prod gaussianCoordinates) ∧
    (∫ p, priorFrozenCGF ν eig c I degree amplitude r h j t p
      ∂(priorFrozenLaw μ j).prod gaussianCoordinates)≤t^2/2 := by
  let U : PriorFrozenData N j → SpecialOrthogonal N := fun ω => ω.1
  have hb := randomCoefficient_cgf_mean_bounds
    (P := priorFrozenLaw μ j) (measurable_priorFrozenReference ν eig c I degree amplitude r h j)
    (spectralPerturbationCoefficients U I (degree j) n (r j))
    (measurable_spectralPerturbationFields U measurable_fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation (U ω)) I (degree j) n (r j) x) t
  simpa only [priorFrozenCGF,spectralPerturbationCoefficients,U,mul_one] using hb

theorem priorGaussian_energy_at_minimum {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (amplitude : Fin N → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin N) (w s K B : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/8)
    (hs : 0<s) (hs' : s≤1/4) (hK : 0<K)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (priorNamespacedLog ν₀ eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        (fun i => tensorPathProfile I degree n r h i)) 2 (μ.prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (priorNamespacedLog ν₀ eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        (fun i => tensorPathProfile I degree n r h i)) (μ.prod gaussianCoordinates)≤B)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, priorNamespacedLog ν₀ eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2,
        -M w+perturbationWeight j*(w-3/2)^2≤-M q+perturbationWeight j*(q-3/2)^2) :
    let a := perturbationAmplitude N j
    let c₀ := N*perturbationWeight j/a^2
    let P := (priorFrozenLaw μ j).prod gaussianCoordinates
    let A := fun ω : PriorFrozenData N j =>
      jointSpectralMonomialCoefficients (specialRotation ω.1) I (degree j) n (r j)
    let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
    let E := fun p : PriorFrozenData N j × (ℕ → ℝ) => ∫ x,
      |cylinderField (A p.1 x) p.2-2*c₀*(a*w-a*(3/2))|
      ∂(ν p.1).tilted (fun x => a*w*cylinderField (A p.1 x) p.2)
    Integrable E P ∧ (∫ p, E p ∂P)≤
      (2*c₀+K^2)/(2*K)+c₀*(a*s)+4*(2*Real.sqrt B)/(a*s) := by
  intro a c₀ P A ν E
  let M := fun q => (N : ℝ)⁻¹ * ∫ p, priorNamespacedLog ν₀ eig c I degree
    (Function.update amplitude j (a*q)) (fun i => tensorPathProfile I degree n r h i) p
    ∂μ.prod gaussianCoordinates
  let L := fun t => ∫ p, priorFrozenCGF ν₀ eig c I degree amplitude r h j t p ∂P
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := perturbationAmplitude_pos hN j
  have hstat (q : ℝ) (hq : |q|≤2) := priorFrozenCGF_statistics μ ν₀ eig c I degree amplitude
    r h hh h0 j (a*q) B
    (fun b hb => by
      rcases hb with rfl | rfl
      · exact hF q hq
      · simpa only [mul_zero] using hF 0 (by norm_num))
    (fun b hb => by
      rcases hb with rfl | rfl
      · exact hv q hq
      · simpa only [mul_zero] using hv 0 (by norm_num))
  have hmean (q : ℝ) (hq : |q|≤2) : L (a*q)=N*(M q-M 0) := by
    dsimp only [L,P,M]
    rw [(hstat q hq).2.1]
    simp only [mul_zero]
    field_simp [hn.ne']
  have hcost (q : ℝ) (hq : |q|≤2) :
      0≤M q-M 0 ∧ M q-M 0≤(a*q)^2/(2*N) := by
    have hb := priorFrozenCGF_mean_bounds μ ν₀ eig c I degree amplitude r h j (a*q)
    change 0≤L (a*q) ∧ L (a*q)≤(a*q)^2/2 at hb
    rw [hmean q hq] at hb
    refine ⟨(mul_nonneg_iff_of_pos_left hn).mp hb.1,?_⟩
    apply (le_div_iff₀ (show 0<2*(N : ℝ) by positivity)).mpr
    nlinarith [hb.2]
  have hwa : |w|≤2 := abs_le.mpr ⟨by linarith [hw.1],hw.2⟩
  have hpen := gaussianCoordinate_minimum_penalty hN j M w hwa
    ⟨(hcost (3/2) (by norm_num)).1,(hcost w hwa).2⟩
    (hmin (3/2) (by constructor <;> norm_num))
  obtain ⟨hlo,hhi⟩ := gaussianCoordinate_minimum_interior j hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) ha hw hlo hhi
    (fun q hq => hmean q (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩)) hmin
  have hconc (t : ℝ) (ht : t∈({a*w-a*s,a*w,a*w+a*s} : Set ℝ)) :
      (∫ p, |priorFrozenCGF ν₀ eig c I degree amplitude r h j t p-L t| ∂P)≤2*Real.sqrt B := by
    have hti : t∈Set.Icc (a*w-a*s) (a*w+a*s) := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos ha hs]
    have htq : t/a∈Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ ha).mpr
        nlinarith [hti.1]
      · apply (div_le_iff₀ ha).mpr
        nlinarith [hti.2]
    have hta : |t/a|≤2 := abs_le.mpr ⟨by linarith [htq.1],htq.2⟩
    simpa only [mul_div_cancel₀ _ ha.ne'] using (hstat (t/a) hta).2.2
  exact randomCoefficient_energy_at_minimum (P := priorFrozenLaw μ j)
    (measurable_priorFrozenReference ν₀ eig c I degree amplitude r h j) A
    (measurable_spectralPerturbationFields (fun ω : PriorFrozenData N j => ω.1)
      measurable_fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation ω.1) I (degree j) n (r j) x) (mul_pos ha hs) hK hlocal hconc

end InvariantIsing

end

end OAI
