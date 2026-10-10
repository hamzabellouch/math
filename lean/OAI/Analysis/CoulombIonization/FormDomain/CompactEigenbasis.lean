import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoherentSchwartz

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CompactEigenbasis_scope

open MeasureTheory Filter Module
open scoped BigOperators ComplexConjugate Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactEigenspaceIndex (T : H →L[ℂ] H) (μ : ℂ) : Set (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose

def compactEigenspaceBasis (T : H →L[ℂ] H) (μ : ℂ) :
    HilbertBasis (compactEigenspaceIndex T μ) ℂ (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose_spec.choose

abbrev CompactSpectralIndex (T : H →L[ℂ] H) := Σ μ : ℂ, compactEigenspaceIndex T μ

def compactSpectralVector (T : H →L[ℂ] H) (i : CompactSpectralIndex T) : H :=
  compactEigenspaceBasis T i.1 i.2

lemma compactSpectralVector_eigen (T : H →L[ℂ] H) (i : CompactSpectralIndex T) :
    T (compactSpectralVector T i) = i.1 • compactSpectralVector T i :=
  Module.End.mem_eigenspace_iff.mp (compactEigenspaceBasis T i.1 i.2).property

lemma compactSpectralVector_orthonormal (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric) :
    Orthonormal ℂ (compactSpectralVector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (compactEigenspaceBasis T μ).orthonormal)

lemma compactSpectralVector_orthogonal_eq_bot (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    (Submodule.span ℂ (Set.range (compactSpectralVector T)))ᗮ = ⊥ := by
  let S := Submodule.span ℂ (Set.range (compactSpectralVector T))
  have hs : (⨆ μ, Module.End.eigenspace T.toLinearMap μ) ≤ S.topologicalClosure := by
    apply iSup_le
    intro μ y hy
    let v : Module.End.eigenspace T.toLinearMap μ := ⟨y,hy⟩
    have hh := ((compactEigenspaceBasis T μ).hasSum_repr v).mapL
      (Module.End.eigenspace T.toLinearMap μ).subtypeL
    apply mem_closure_of_tendsto hh
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    change ((compactEigenspaceBasis T μ).repr v i) • (compactSpectralVector T ⟨μ,i⟩) ∈ S
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
  apply le_antisymm _ bot_le
  rw [← S.orthogonal_closure]
  exact (Submodule.orthogonal_le hs).trans
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs).le

def compactSpectralBasis (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    HilbertBasis (CompactSpectralIndex T) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (compactSpectralVector_orthonormal T hTs)
    (compactSpectralVector_orthogonal_eq_bot T hTc hTs)

lemma compactSpectralBasis_apply (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) : compactSpectralBasis T hTc hTs i = compactSpectralVector T i := by
  rw [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma compactSpectralBasis_eigen (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) :
    T (compactSpectralBasis T hTc hTs i) = i.1 • compactSpectralBasis T hTc hTs i := by
  simp only [compactSpectralBasis_apply,compactSpectralVector_eigen]

end Work_CompactEigenbasis_scope

section Work_HilbertCountable_scope

open scoped Topology

universe u v
lemma orthonormal_countable {H : Type u} {ι : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2 : ℝ)) (Metric.ball (v j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ),hv.norm_eq_one,hv.norm_eq_one,hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))

end Work_HilbertCountable_scope

section Work_HilbertTrace_scope

open MeasureTheory Filter
open scoped BigOperators Topology

universe u v w
variable {H : Type u} {ι : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma hilbertBasis_hasSum_norm_inner (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using lp.hasSum_norm (by norm_num : 0 < (2:ENNReal).toReal) (b.repr x)

lemma hilbertBasis_frame_trace {α : Type w} [MeasurableSpace α]
    (μ : Measure α) (b : HilbertBasis ι ℂ H) [Countable ι] (v : α → H)
    (hv : AEStronglyMeasurable v μ) (hn : Integrable (fun x => ‖v x‖^2) μ) :
    HasSum (fun i => ∫ x, ‖inner ℂ (b i) (v x)‖^2 ∂μ) (∫ x, ‖v x‖^2 ∂μ) := by
  have hmeas (i : ι) : AEStronglyMeasurable (fun x => ‖inner ℂ (b i) (v x)‖^2) μ :=
    (((continuous_const.inner continuous_id).norm.pow 2).comp_aestronglyMeasurable hv)
  apply hasSum_integral_of_dominated_convergence
    (fun i x => ‖inner ℂ (b i) (v x)‖^2) hmeas
  · intro i
    exact Eventually.of_forall (fun x => (Real.norm_of_nonneg (sq_nonneg _)).le)
  · exact Eventually.of_forall (fun x => b.orthonormal.inner_products_summable (v x))
  · convert hn using 1
    ext x
    exact (hilbertBasis_hasSum_norm_inner b (v x)).tsum_eq
  · exact Eventually.of_forall (fun x => hilbertBasis_hasSum_norm_inner b (v x))

end Work_HilbertTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

instance orbitalHilbert_secondCountable : SecondCountableTopology OrbitalHilbert := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  infer_instance

abbrev CoherentIndex {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) := CompactSpectralIndex (coherentOperator hg hcg μ)

def coherentBasis {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HilbertBasis (CoherentIndex hg hcg μ) ℂ OrbitalHilbert :=
  compactSpectralBasis _ (coherentOperator_compact hg hcg μ)
    (coherentOperator_positive hg hcg μ).isSymmetric

instance coherentIndex_countable {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] : Countable (CoherentIndex hg hcg μ) :=
  orthonormal_countable (coherentBasis hg hcg μ).orthonormal

lemma coherentBasis_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentOperator hg hcg μ (coherentBasis hg hcg μ i) =
      i.1 • coherentBasis hg hcg μ i := compactSpectralBasis_eigen _ _ _ i

lemma coherentBasis_inner_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    inner ℂ (coherentBasis hg hcg μ i) (coherentOperator hg hcg μ (coherentBasis hg hcg μ i)) = i.1 := by
  rw [coherentBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (coherentBasis hg hcg μ).orthonormal.norm_eq_one]
  simp

lemma coherentBasis_eigenvalue_eq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    i.1 = (((2*Real.pi)^3)⁻¹ * ∫ q,
      ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ : ℝ) := by
  rw [← coherentBasis_inner_eigen hg hcg μ i,coherentOperator_inner]
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => congrArg (fun t : ℝ => t^2) (norm_inner_symm _ _))

def coherentWeight {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) (i : CoherentIndex hg hcg μ) : ℝ := i.1.re

lemma coherentWeight_eq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentWeight hg hcg μ i = ((2*Real.pi)^3)⁻¹ * ∫ q,
      ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ := by
  rw [coherentWeight,coherentBasis_eigenvalue_eq,Complex.ofReal_re]

lemma coherentWeight_nonneg {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    0 ≤ coherentWeight hg hcg μ i := by
  rw [coherentWeight_eq]
  exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))

lemma coherentBasis_real_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentOperator hg hcg μ (coherentBasis hg hcg μ i) =
      coherentWeight hg hcg μ i • coherentBasis hg hcg μ i := by
  rw [coherentBasis_eigen,coherentBasis_eigenvalue_eq,coherentWeight_eq]
  rw [Complex.coe_smul]
  rfl

lemma coherentWeight_le_one {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (i : CoherentIndex hg.continuous hcg μ) : coherentWeight hg.continuous hcg μ i ≤ 1 := by
  have h := coherentOperator_quadratic_le hg hcg hgn μ hμ (coherentBasis hg.continuous hcg μ i)
  rw [coherentBasis_inner_eigen,(coherentBasis hg.continuous hcg μ).orthonormal.norm_eq_one] at h
  change i.1.re ≤ 1
  simpa only [one_pow] using h

lemma coherentWeight_hasSum {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HasSum (coherentWeight hg hcg μ) (((2*Real.pi)^3)⁻¹ * μ.real Set.univ * ∫ x : Space, ‖g x‖^2) := by
  have hn : Integrable (fun q => ‖coherentVector hg hcg q‖^2) μ := by
    simp_rw [coherentVector_norm_sq]
    exact integrable_const _
  have ht := hilbertBasis_frame_trace μ (coherentBasis hg hcg μ) (coherentVector hg hcg)
    (coherentVector_continuous hg hcg).aestronglyMeasurable hn
  have he : (∫ q, ‖coherentVector hg hcg q‖^2 ∂μ) = μ.real Set.univ * ∫ x : Space, ‖g x‖^2 := by
    simp only [coherentVector_norm_sq,integral_const,smul_eq_mul]
  rw [he] at ht
  have hsum := ht.mul_left (((2*Real.pi)^3)⁻¹)
  have hf : coherentWeight hg hcg μ = (fun i => ((2*Real.pi)^3)⁻¹ *
      ∫ q, ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ) :=
    funext (coherentWeight_eq hg hcg μ)
  rw [hf,mul_assoc]
  exact hsum

end CoulombAtom

end

end OAI
