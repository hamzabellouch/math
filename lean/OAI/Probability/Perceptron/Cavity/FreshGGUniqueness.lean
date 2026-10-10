import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshReplicaKernel
import OAI.Probability.Perceptron.Variational.UniformQuantileCells

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def CompactSpinGeometry (Q : CompactArray CompactJointOverlap) : Prop :=
  (∀ i j, (Q i j).1.val=(Q j i).1.val) ∧ (∀ i, (Q i i).1.val=1) ∧
    ∀ i j k, min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val

def compactSpinTop : CompactOverlap := ⟨1,by norm_num⟩

lemma compactSpinCode_geometry (n : ℕ) {Q : CompactArray CompactJointOverlap}
    (hQ : CompactSpinGeometry Q) :
    (∀ i j, compactSpinCode n (Q i j)=compactSpinCode n (Q j i)) ∧
      (∀ i, compactSpinCode n (Q i i)=compactSpinCode n (compactSpinTop,0)) ∧
      ∀ i j k, min (compactSpinCode n (Q i j)) (compactSpinCode n (Q i k)) ≤ compactSpinCode n (Q j k) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    exact le_antisymm (compactSpinCode_mono n (hQ.1 i j).le) (compactSpinCode_mono n (hQ.1 i j).ge)
  · intro i
    exact le_antisymm (compactSpinCode_mono n (hQ.2.1 i).le) (compactSpinCode_mono n (hQ.2.1 i).ge)
  · intro i j k
    rcases le_total (Q i j).1.val (Q i k).1.val with h|h
    · apply (min_le_left _ _).trans
      apply compactSpinCode_mono n
      simpa only [min_eq_left h] using hQ.2.2 i j k
    · apply (min_le_right _ _).trans
      apply compactSpinCode_mono n
      simpa only [min_eq_right h] using hQ.2.2 i j k

variable (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
variable (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
variable (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
variable (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))

include hGGμ hGGν hμ hν hpair in
lemma compactSpinCode_block_law_unique (n r : ℕ) :
    (μ : Measure (CompactArray CompactJointOverlap)).map
      (fun Q => compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q))=
    (ν : Measure (CompactArray CompactJointOverlap)).map
      (fun Q => compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q)) := by
  apply compact_finite_code_block_unique μ ν hGGμ hGGν (compactSpinCode_measurable n)
    (compactSpinCode n (compactSpinTop,0))
    (hμ.mono fun Q hQ => compactSpinCode_geometry n hQ)
    (hν.mono fun Q hQ => compactSpinCode_geometry n hQ) _ r
  have he := congrArg (fun ρ : Measure CompactOverlap =>
    ρ.map (fun x => uniformQuantileCell n (compactSpinTime x))) hpair
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1) := by fun_prop
  have hc : Measurable (fun x => uniformQuantileCell n (compactSpinTime x)) :=
    (uniformQuantileCell_measurable n).comp compactSpinTime_continuous.measurable
  rw [Measure.map_map hc hm,Measure.map_map hc hm] at he
  exact he

include hGGμ hGGν hμ hν hpair in
lemma compactSpinCode_integral_unique (n r : ℕ) (F : Matrix (Fin (r+1)) (Fin (r+1)) ℝ →ᵇ ℝ) :
    (∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j))) ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j))) ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  let D : FiniteBlock (Fin (n+1)) (r+1) → ℝ := fun A => F (fun i j => compactSpinDecode n (A i j))
  have hD : Measurable D := measurable_of_countable _
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap =>
      compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q)) :=
    (compactCodeBlock_measurable (compactSpinCode_measurable n) (r+1)).comp (compactBlock_continuous (r+1)).measurable
  have he := congrArg (fun ρ : Measure (FiniteBlock (Fin (n+1)) (r+1)) => ∫ A, D A ∂ρ)
    (compactSpinCode_block_law_unique μ ν hGGμ hGGν hμ hν hpair n r)
  rw [integral_map hm.aemeasurable hD.aestronglyMeasurable,
    integral_map hm.aemeasurable hD.aestronglyMeasurable] at he
  exact he

lemma compactSpinCode_integral_tendsto (ρ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j)))
      ∂(ρ : Measure (CompactArray CompactJointOverlap))) atTop
      (𝓝 (∫ Q, F (fun i j => (Q i j).1.val) ∂(ρ : Measure (CompactArray CompactJointOverlap)))) := by
  let : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (MeasurableSpace (Fin r → Fin r → ℝ))
  let : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (BorelSpace (Fin r → Fin r → ℝ))
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    apply (F.continuous.measurable.comp _).aestronglyMeasurable
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_of_countable (compactSpinDecode n)).comp ((compactSpinCode_measurable n).comp (by fun_prop))
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun Q => F.norm_coe_le_norm _
  · exact ae_of_all _ fun Q => F.continuous.continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => compactSpinDecode_tendsto (Q i j))

include hGGμ hGGν hμ hν hpair in

theorem scalarGram_eq_of_pair_law (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (∫ Q, F (fun i j => (Q i j).1.val) ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, F (fun i j => (Q i j).1.val) ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  cases r with
  | zero =>
    have he : ∀ Q : CompactArray CompactJointOverlap,
        F (fun i j : Fin 0 => (Q i j).1.val)=F (fun _ _ => 0) := by
      intro Q
      congr 1
      exact Subsingleton.elim _ _
    simp only [he,integral_const,probReal_univ,one_smul]
  | succ r =>
    have h1 := compactSpinCode_integral_tendsto μ (r+1) F
    have h2 := compactSpinCode_integral_tendsto ν (r+1) F
    have he := compactSpinCode_integral_unique μ ν hGGμ hGGν hμ hν hpair
    simp_rw [he] at h1
    exact tendsto_nhds_unique h1 h2

include hGGμ hGGν hμ hν hpair in

theorem freshReplicaKernel_eq_of_pair_law (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ Q, freshReplicaArrayKernel f r Q ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, freshReplicaArrayKernel f r Q ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  cases r with
  | zero =>
    have he : ∀ Q : CompactArray CompactJointOverlap,
        freshReplicaArrayKernel f 0 Q=freshReplicaMatrixKernel f 0 (fun _ _ => 0) := by
      intro Q
      change freshReplicaMatrixKernel f 0 _=_
      congr 1
      exact Subsingleton.elim _ _
    simp only [he,integral_const,probReal_univ,one_smul]
  | succ r =>
    let F := freshReplicaMatrixKernel f (r+1)
    have h1 := compactSpinCode_integral_tendsto μ (r+1) F
    have h2 := compactSpinCode_integral_tendsto ν (r+1) F
    have he := compactSpinCode_integral_unique μ ν hGGμ hGGν hμ hν hpair
    simp_rw [he] at h1
    exact tendsto_nhds_unique h1 h2

end SphericalPerceptronFreeEnergy
end

end OAI
