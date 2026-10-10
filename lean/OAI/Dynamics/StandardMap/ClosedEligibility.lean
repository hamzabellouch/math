import OAI.Dynamics.StandardMap.GridPartition

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma fast_prefix_row (v : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hB : 2 ≤ B) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ J : ℕ, (J=B ∨ J=B+1) ∧ ‖transferProduct v B‖/3 ≤ |tSolution v J| := by
  obtain ⟨s,hu,hver,hs,_⟩:=prefix_stable_vertical v M B (by omega) hM hq hsmall hv hg
  have he : transferProduct v B 1=⟨linearSolution v 0 1 (B+1),linearSolution v 0 1 B⟩ := transferProduct_pair v 0 1 B
  rcases (transferProduct_area v B).eligible_row s hu hver hs with hr|hr
  · refine ⟨B+1,Or.inr rfl,?_⟩
    simpa only [he,tSolution] using hr
  · refine ⟨B,Or.inl rfl,?_⟩
    simpa only [he,tSolution] using hr

lemma eligible_prefix_dirichlet (v : ℕ → ℝ) (M : ℝ) (B J : ℕ)
    (hB : 2 ≤ B) (hJ : J=B ∨ J=B+1) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖)
    (hrow : ‖transferProduct v B‖/3 ≤ |tSolution v J|) :
    tSolution v J ≠ 0 ∧ ∀ p, 1 ≤ p → p < J →
      |dirichletSolution v J p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)) := by
  obtain ⟨s,hu,hver,hs,hpref⟩:=prefix_stable_vertical v M B (by omega) hM hq hsmall hv hg
  have hpair (z : ℂ) : transferProduct v B z=
      ⟨linearSolution v z.im z.re (B+1),linearSolution v z.im z.re B⟩ := by
    exact transferProduct_pair v z.im z.re B
  rcases hJ with hJ|hJ
  · subst J
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B B hM (by omega) (by omega)
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.imCLM.comp (transferProduct v B))
    · intro z; change (transferProduct v B z).im=_; rw [hpair]
    · exact (Complex.abs_im_le_norm _).trans_eq hs
    · simpa only [ContinuousLinearMap.comp_apply,Complex.imCLM_apply,hpair,Complex.one_im,
        Complex.one_re,tSolution] using hrow
  · subst J
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B (B+1) hM (by omega) le_rfl
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.reCLM.comp (transferProduct v B))
    · intro z; change (transferProduct v B z).re=_; rw [hpair]
    · exact (Complex.abs_re_le_norm _).trans_eq hs
    · simpa only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,hpair,Complex.one_im,
        Complex.one_re,tSolution] using hrow

noncomputable def prefixEligible (k : ℝ) (B J : ℕ) (z : ℝ × ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤
    ‖transferProduct (orbitCoefficient k z.1 z.2) i‖) ∧
  ‖transferProduct (orbitCoefficient k z.1 z.2) B‖/3 ≤
    |tSolution (orbitCoefficient k z.1 z.2) J|

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

lemma continuous_orbitCoefficient_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2 n) := by
  have h := continuous_liftedOrbit_pair k n
  unfold orbitCoefficient potential
  exact continuous_const.add (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul h)))

lemma isClosed_prefixEligible (k : ℝ) (B J : ℕ) :
    IsClosed {z : ℝ × ℝ | prefixEligible k B J z} := by
  have hc n := continuous_transferProduct_params (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2)
    (continuous_orbitCoefficient_pair k) n
  have ht : Continuous (fun z : ℝ × ℝ => tSolution (orbitCoefficient k z.1 z.2) J) := by
    rw [← continuousOn_univ]
    exact continuousOn_linearSolution_params univ (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2) (fun _ => 0) (fun _ => 1) (fun p => (continuous_orbitCoefficient_pair k p).continuousOn)
      continuousOn_const continuousOn_const J
  simp only [prefixEligible,ofPred_and,ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (hc i).norm
  · exact isClosed_le ((hc B).norm.div_const 3) ht.abs
end StandardMapEntropy

end OAI
