import Mathlib
import OAI.Analysis.SymmetricDomains.ParameterPeakMaximizer
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash
import OAI.Analysis.SymmetricDomains.CriticalAffineBundleNeighborhood
import OAI.Analysis.SymmetricDomains.RealCriticalMatrix

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical ContDiff

noncomputable def parameterLogBase {N : ℕ} (P : MvPolynomial (Fin N) ℂ) (z : Affine N) : ℝ :=
  Real.log ‖MvPolynomial.eval z P‖ + coordinateEnergy z

lemma coordinateEnergy_contDiff {N : ℕ} {r : ℕ∞ω} : ContDiff ℝ r (@coordinateEnergy N) := by
  unfold coordinateEnergy
  exact ContDiff.sum (fun i _ => (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℝ] ℂ).contDiff.norm_sq ℂ)

lemma parameterLogBase_contDiffAt {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) {r : ℕ∞ω} :
    ContDiffAt ℝ r (parameterLogBase P) z := by
  have hP : ContDiffAt ℝ r (fun z => MvPolynomial.eval z P) z :=
    (((AnalyticOnNhd.eval_mvPolynomial P) z (mem_univ z)).restrictScalars (𝕜 := ℝ)).contDiffAt
  exact ((hP.norm ℂ hz).log (norm_ne_zero_iff.mpr hz)).add coordinateEnergy_contDiff.contDiffAt

lemma parameterPotential_eq_exp {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) :
    parameterPotential P a z = Real.exp (parameterLogBase P z + (a z).re) := by
  rw [parameterLogBase,add_assoc,Real.exp_add,Real.exp_log (norm_pos_iff.mpr hz)]
  rfl

theorem actual_maximizer_critical {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (K : Set (Affine N)) (hqK : MapsTo q B K)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    {x : Fin d → ℝ} (hx : x ∈ B) (hq : DifferentiableAt ℝ q x)
    (a : Affine N →L[ℂ] ℂ) (hmax : IsMaxOn (parameterPotential P a) K (q x)) :
    realCriticalMatrix q x a = realCriticalConstant (parameterLogBase P ∘ q) x := by
  apply (realCriticalMatrix_eq_iff q (parameterLogBase P ∘ q) hq
    ((parameterLogBase_contDiffAt P (hP x hx) (r := 1)).differentiableAt one_ne_zero |>.comp x hq) a).2
  apply IsLocalMax.fderiv_eq_zero
  filter_upwards [hB.mem_nhds hx] with y hy
  apply Real.exp_le_exp.mp
  simpa only [Function.comp_apply,← parameterPotential_eq_exp P a (hP y hy),
    ← parameterPotential_eq_exp P a (hP x hx)] using (show parameterPotential P a (q y) ≤ parameterPotential P a (q x) from hmax (hqK hy))

theorem actual_critical_bundle {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hq : ContDiffOn ℝ 2 q B)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ B) (hi : Function.Injective (fderiv ℝ q x₀)) :
    ∃ (r : ℕ) (e : (Affine N →L[ℂ] ℂ) ≃L[ℝ]
        ((Fin d → ℝ) × (Fin r → ℝ))) (W : Set (Fin d → ℝ)),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ B ∧
      ContDiffOn ℝ 1 (criticalBundleParam (realCriticalMatrix q) e
        (realCriticalConstant (parameterLogBase P ∘ q))) (W ×ˢ univ) ∧
      ∀ x ∈ W, range (fun k => criticalBundleParam (realCriticalMatrix q) e
          (realCriticalConstant (parameterLogBase P ∘ q)) (x,k)) =
        {a | fderiv ℝ (fun y => parameterLogBase P (q y) + (a (q y)).re) x = 0} := by
  obtain ⟨r,e,he⟩ := exists_continuousLinearEquiv_prod_fin (realCriticalMatrix q x₀)
    (realCriticalMatrix_surjective q hi)
  have hq' (x : Fin d → ℝ) (hx : x ∈ B) : ContDiffAt ℝ 2 q x :=
    (hq x hx).contDiffAt (hB.mem_nhds hx)
  have hf (x : Fin d → ℝ) (hx : x ∈ B) :
      ContDiffAt ℝ 2 (parameterLogBase P ∘ q) x :=
    (parameterLogBase_contDiffAt P (hP x hx)).comp x (hq' x hx)
  obtain ⟨W,hWo,hx₀W,hWB,_,hpar,hfib⟩ := critical_affine_bundle_neighborhood
    (realCriticalMatrix q) B hB (fun x hx => realCriticalMatrix_contDiffAt q (hq' x hx))
    (realCriticalConstant (parameterLogBase P ∘ q))
    (fun x hx => realCriticalConstant_contDiffAt _ (hf x hx)) hx₀ e he
  refine ⟨r,e,W,hWo,hx₀W,hWB,hpar,?_⟩
  intro x hx
  rw [hfib x hx]
  ext a
  exact realCriticalMatrix_eq_iff q _ ((hq' x (hWB hx)).differentiableAt (by norm_num))
    ((hf x (hWB hx)).differentiableAt (by norm_num)) a

lemma parameterPotential_joint_continuous {N : ℕ} (P : MvPolynomial (Fin N) ℂ) :
    Continuous (Function.uncurry (parameterPotential P)) := by
  unfold parameterPotential Function.uncurry
  exact ((MvPolynomial.continuous_eval P).comp continuous_snd).norm.mul
    (Real.continuous_exp.comp ((coordinateEnergy_continuous.comp continuous_snd).add
      (Complex.continuous_re.comp (continuous_fst.clm_apply continuous_snd))))

lemma measurableSet_continuousOn_preimage
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    {W : Set X} (hW : MeasurableSet W) {f : X → Y} (hf : ContinuousOn f W)
    {T : Set Y} (hT : MeasurableSet T) : MeasurableSet {x | x ∈ W ∧ f x ∈ T} := by
  classical
  let y₀ : Y := Classical.choice inferInstance
  have hg : Measurable (W.piecewise f (fun _ => y₀)) :=
    hf.measurable_piecewise continuousOn_const hW
  convert hW.inter (hT.preimage hg) using 1
  ext x
  by_cases hx : x ∈ W <;> simp [hx]

theorem actual_maximizer_bundle_borel
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology X] [SecondCountableTopology K]
    {N : ℕ} (P : MvPolynomial (Fin N) ℂ) {C : Set (Affine N)} (hC : IsClosed C)
    {W : Set X} (hW : MeasurableSet W) (q : X → Affine N) (hq : ContinuousOn q W)
    (A : X × K → (Affine N →L[ℂ] ℂ)) (hA : ContinuousOn A (W ×ˢ univ)) :
    MeasurableSet {p : X × K | p.1 ∈ W ∧ q p.1 ∈ C ∧
      IsMaxOn (parameterPotential P (A p)) C (q p.1)} := by
  have hc := isClosed_maximizer_relation hC (parameterPotential_joint_continuous P)
  have hh := measurableSet_continuousOn_preimage (hW.prod MeasurableSet.univ)
    ((hq.comp continuousOn_fst (fun _ hp => hp.1)).prodMk hA) hc.measurableSet
  convert hh using 1
  ext p
  simp only [mem_ofPred_eq,mem_prod,mem_univ,and_true,IsMaxOn,IsMaxFilter,Filter.eventually_principal]
  rfl

end Release061

end

end OAI
