import OAI.Probability.InvariantIsing.Fields.SpinPriorFrozenReference
import OAI.Probability.InvariantIsing.Pressure.PressureDifferenceConcentration

namespace OAI

/-! Frozen Gaussian cumulants in the actual constrained cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFrozenCGF {N m k : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2)
    (spinPriorFrozenReference π eig c I degree amp n r h j p.1) t

theorem spinPriorFrozenCGF_eq_log_difference {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) (t : ℝ) :
    spinPriorFrozenCGF π eig c I degree amp n r h j t =ᵐ[(tensorFrozenLaw μ n b j).prod gaussianCoordinates]
      fun p => spinPriorNamespacedLog π eig c I degree (Function.update amp j t) r h
          (p.1.1, gaussianNamespaceJoin (j+1) (p.2,p.1.2))-
        spinPriorNamespacedLog π eig c I degree (Function.update amp j 0) r h
          (p.1.1, gaussianNamespaceJoin (j+1) (p.2,p.1.2)) := by
  have hbase := (measurePreserving_fst (μ := tensorFrozenLaw μ n b j)
    (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (spinPriorFrozenBase_exp_integrable_ae μ π eig c I degree amp n b r h hh h0 j)
  have hfull := (tensorFrozenInsertion_measurePreserving μ n b j).quasiMeasurePreserving.ae
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree (Function.update amp j t) n b r h hh h0)
  filter_upwards [hbase,hfull] with p hb hf
  let ν := labeledSpinReference n π p.1.1.2
  let H := tensorFrozenBaseEnergy eig c I degree amp n r h j p.1
  let Y := fun x : Spin N × LabeledLeaf n => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2
  have he (a : ℝ) (x : Spin N × LabeledLeaf n) :
      tensorNamespacedHamiltonian eig c I degree (Function.update amp j a) n r h
        (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x = H x+a*Y x := by
    simpa only [H,Y,tensorNamespacedHamiltonian,tensorFrozenBaseEnergy,Function.update_idem,Function.update_self] using
      tensorFrozenEnergy_insert eig c I degree (Function.update amp j a) n r h hh h0 j p.1 p.2 x
  have hi : Integrable (fun x => Real.exp (H x+t*Y x)) ν := by
    convert hf using 1
    funext x
    exact congrArg Real.exp (he t x).symm
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hb hi]
  change Real.log (∫ x, Real.exp (H x+t*Y x) ∂ν)-Real.log (∫ x, Real.exp (H x) ∂ν) = _
  change _ = Real.log (∫ x, Real.exp (tensorNamespacedHamiltonian eig c I degree
    (Function.update amp j t) n r h (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x) ∂ν)-
    Real.log (∫ x, Real.exp (tensorNamespacedHamiltonian eig c I degree
      (Function.update amp j 0) n r h (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x) ∂ν)
  simp only [he,zero_mul,add_zero]

theorem spinPriorFrozenCGF_statistics {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) (t B : ℝ)
    (hF : ∀ a : ℝ, a=t ∨ a=0 →
      MemLp (spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h) 2
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ a : ℝ, a=t ∨ a=0 →
      variance (spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h)
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤ B) :
    let P := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let M := fun a => ∫ p, spinPriorNamespacedLog π eig c I degree (Function.update amp j a) r h p ∂Q
    let Z := spinPriorFrozenCGF π eig c I degree amp n r h j t
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M t-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P) ≤ 2*Real.sqrt B := by
  intro P Q M Z
  let F := fun a => spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h
  let J := fun p : TensorFrozenData N n j × (ℕ → ℝ) =>
    (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2))
  have hp : MeasurePreserving J P Q := tensorFrozenInsertion_measurePreserving μ n b j
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F t (J p)-F 0 (J p)) := by
    simpa only [one_mul] using spinPriorFrozenCGF_eq_log_difference μ π eig c I degree amp n b r h hh h0 j t
  have ht := hF t (Or.inl rfl)
  have hz := hF 0 (Or.inr rfl)
  have hc := centered_scaled_difference_L1_bound P
    (ht.comp_measurePreserving hp) (hz.comp_measurePreserving hp)
    ((hp.variance_fun_comp ht.aemeasurable).trans_le (hv t (Or.inl rfl)))
    ((hp.variance_fun_comp hz.aemeasurable).trans_le (hv 0 (Or.inr rfl))) he
  refine ⟨hc.1,?_,?_⟩
  · rw [integral_congr_ae he]
    simp only [one_mul]
    exact (integral_sub ((ht.comp_measurePreserving hp).integrable (by norm_num))
      ((hz.comp_measurePreserving hp).integrable (by norm_num))).trans
      (congrArg₂ (·-·) (hp.hasLaw.integral_comp ht.aestronglyMeasurable)
        (hp.hasLaw.integral_comp hz.aestronglyMeasurable))
  · simpa only [abs_one,mul_one,one_mul] using hc.2

end InvariantIsing

end

end OAI
