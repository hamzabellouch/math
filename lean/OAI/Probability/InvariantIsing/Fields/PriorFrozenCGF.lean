import OAI.Probability.InvariantIsing.Fields.PriorFrozenReference
import OAI.Probability.InvariantIsing.Pressure.PressureDifferenceConcentration

namespace OAI

/-! Log-partition differences and concentration of a selected prior perturbation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorFrozenCGF {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : PriorFrozenData N j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1) I (degree j) n (r j) x) p.2)
    (priorFrozenReference ν eig c I degree amplitude r h j p.1) t

theorem priorFrozenCGF_eq_log_difference {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) (t : ℝ) :
    priorFrozenCGF ν eig c I degree amplitude r h j t =ᵐ[(priorFrozenLaw μ j).prod gaussianCoordinates]
      fun p => priorNamespacedLog ν eig c I degree (Function.update amplitude j t)
        (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j p) -
        priorNamespacedLog ν eig c I degree (Function.update amplitude j 0)
        (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j p) := by
  have hbase := (measurePreserving_fst (μ := priorFrozenLaw μ j)
    (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (priorFrozenBase_exp_integrable_ae μ ν eig c I degree amplitude r h hh h0 j)
  have hfull := (priorFrozenInsertion_preserving μ j).quasiMeasurePreserving.ae
    (priorNamespaced_exp_integrable_ae μ ν eig c I degree (Function.update amplitude j t) r h hh h0)
  filter_upwards [hbase,hfull] with p hb hf
  let H : Spin N × LabeledLeaf n → ℝ := priorFrozenBaseEnergy eig c I degree amplitude r h j p.1
  let Y := fun x : Spin N × LabeledLeaf n => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1) I (degree j) n (r j) x) p.2
  have he (a : ℝ) (x : Spin N × LabeledLeaf n) :
      priorNamespacedHamiltonian eig c I degree (Function.update amplitude j a)
        (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j p) x = H x+a*Y x := by
    simpa only [H,Y,priorFrozenBaseEnergy,Function.update_idem,Function.update_self] using
      priorFrozenHamiltonian_insert eig c I degree (Function.update amplitude j a) r h hh h0 j p.1 p.2 x
  have hi : Integrable (fun x => Real.exp (H x+t*Y x)) ν := by
    convert hf using 1
    funext x
    exact congrArg Real.exp (he t x).symm
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hb hi]
  unfold priorNamespacedLog
  simp only [he,zero_mul,add_zero]
  rfl

theorem priorFrozenCGF_statistics {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) (t B : ℝ)
    (hF : ∀ a : ℝ, a=t ∨ a=0 →
      MemLp (priorNamespacedLog ν eig c I degree (Function.update amplitude j a)
        (fun i => tensorPathProfile I degree n r h i)) 2 (μ.prod gaussianCoordinates))
    (hv : ∀ a : ℝ, a=t ∨ a=0 →
      variance (priorNamespacedLog ν eig c I degree (Function.update amplitude j a)
        (fun i => tensorPathProfile I degree n r h i)) (μ.prod gaussianCoordinates) ≤ B) :
    let P := (priorFrozenLaw μ j).prod gaussianCoordinates
    let M := fun a => ∫ p, priorNamespacedLog ν eig c I degree (Function.update amplitude j a)
      (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates
    let Z := priorFrozenCGF ν eig c I degree amplitude r h j t
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M t-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P)≤2*Real.sqrt B := by
  intro P M Z
  let F := fun a => priorNamespacedLog ν eig c I degree (Function.update amplitude j a)
    (fun i => tensorPathProfile I degree n r h i)
  have hp := priorFrozenInsertion_preserving μ j
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F t (priorFrozenInsertion j p)-F 0 (priorFrozenInsertion j p)) := by
    simpa only [one_mul] using priorFrozenCGF_eq_log_difference μ ν eig c I degree amplitude r h hh h0 j t
  have ht := hF t (Or.inl rfl)
  have hz := hF 0 (Or.inr rfl)
  have hc := centered_scaled_difference_L1_bound P
    (ht.comp_measurePreserving hp) (hz.comp_measurePreserving hp)
    ((hp.variance_fun_comp ht.aemeasurable).trans_le (hv t (Or.inl rfl)))
    ((hp.variance_fun_comp hz.aemeasurable).trans_le (hv 0 (Or.inr rfl))) he
  refine ⟨hc.1,?_,?_⟩
  · rw [integral_congr_ae he]
    simp only [one_mul]
    calc
      _ = (∫ p, F t (priorFrozenInsertion j p) ∂P) -
          ∫ p, F 0 (priorFrozenInsertion j p) ∂P :=
        integral_sub ((ht.comp_measurePreserving hp).integrable (by norm_num))
          ((hz.comp_measurePreserving hp).integrable (by norm_num))
      _ = M t-M 0 := congrArg₂ (·-·) (hp.hasLaw.integral_comp ht.aestronglyMeasurable)
        (hp.hasLaw.integral_comp hz.aestronglyMeasurable)
  · simpa only [abs_one,mul_one,one_mul] using hc.2

end InvariantIsing

end

end OAI
