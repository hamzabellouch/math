import Mathlib
import OAI.Probability.Perceptron.Interpolation.KernelInfiniteReplica

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma countableGaussianCovariance_posSemidef {S : Type*} [MeasurableSpace S]
    (v : ℕ → S → ℝ) (L : S → ℕ) (r : ℕ) (x : Fin r → S) :
    Matrix.PosSemidef (fun i j => countableGaussianCovariance v v L (x i) (x j)) := by
  classical
  have he : ∀ᶠ n in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (x i) (x j) = countableGaussianCovariance v v L (x i) (x j) := by
    simp only [Filter.eventually_all]
    exact fun i j => gaussianPrefixCovariance_eventually_eq v v L (x i) (x j)
  obtain ⟨n,hn⟩ := he.exists
  let A : Matrix (Fin n) (Fin r) ℝ := fun a i => maskedGaussianCoefficient v L a.val (x i)
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  have hm : (fun i j => countableGaussianCovariance v v L (x i) (x j)) = Aᴴ * A := by
    funext i j
    rw [← hn i j]
    simp only [gaussianPrefixCovariance,A]
    rfl
  rw [hm]
  exact hp

lemma sourceSpinArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).1:ℝ)) := by
  exact Matrix.posSemidef_gram ℝ (fun i : Fin r => (x i).1.val)

lemma sourceTreeArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).2:ℝ)) := by
  let q : Fin (k+1) → Fin 1 → ℝ := fun l _ => (l.val:ℝ)/(k+1:ℕ)
  let V : NormalizedSpin N → EuclideanSpace ℝ (Fin 1) := fun _ => WithLp.toLp 2 (fun _ => 1)
  let v := indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V
  have hq : ∀ i, Monotone (fun l => q l i) := by
    intro i a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have he (i j : Fin r) : countableGaussianCovariance v v
      (indexedGaussianRowLength (I := Fin 1) k) (x i) (x j) = ((sourceJointArray x i j).2:ℝ) := by
    rw [profileGaussianRow_covariance q (by intro; simp [q]) hq V V]
    simp [q,V,sourceJointArray,sourceJointOverlap]
  have hp := countableGaussianCovariance_posSemidef v
    (indexedGaussianRowLength (I := Fin 1) k) r (fun i => x i)
  simpa only [he] using hp

lemma sourceJointArray_diagonal {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (i : ℕ) :
    ((sourceJointArray x i i).1:ℝ) = 1 := by
  change inner ℝ (x i).1.val (x i).1.val = 1
  have hx : ‖(x i).1.val‖=1 := by simp
  simp [hx]

lemma isClosed_matrix_posSemidef (r : ℕ) : IsClosed {M : Matrix (Fin r) (Fin r) ℝ | M.PosSemidef} := by
  have he : {M : Matrix (Fin r) (Fin r) ℝ | M.PosSemidef} =
      {M : Matrix (Fin r) (Fin r) ℝ | ∀ i j, M j i=M i j} ∩ ⋂ x : Fin r → ℝ, {M : Matrix (Fin r) (Fin r) ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter,Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.IsHermitian.ext_iff,star_trivial]
  rw [he]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (by
      unfold dotProduct Matrix.mulVec
      fun_prop)

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma pi_iid_reindex_preserving {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → S => fun i => x (e i))
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : ι => μ)) := by
  have he : (fun x : ι → S => fun i => x (e i)) = MeasurableEquiv.piCongrLeft (fun _ : ι => S) e.symm := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm

lemma infinite_iid_reindex_preserving (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i => x (e i))
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have he : (fun x : ℕ → S => fun i => x (e i)) = MeasurableEquiv.piCongrLeft (fun _ : ℕ => S) e.symm := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact ⟨(MeasurableEquiv.piCongrLeft _ e.symm).measurable,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.symm⟩

lemma gibbsReplicaMean_reindex {H : S → ℝ} (hH : Measurable H)
    (hexp : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) (e : Equiv.Perm (Fin r))
    {G : (Fin r → S) → ℝ} (hG : Measurable G) :
    gibbsReplicaMean μ H r (fun x => G (fun i => x (e i))) = gibbsReplicaMean μ H r G := by
  let : IsProbabilityMeasure (tiltLaw μ H 1) :=
    tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hexp)
  rw [gibbsReplicaMean_integral_of_integrable μ hH hexp,
    gibbsReplicaMean_integral_of_integrable μ hH hexp]
  have hp := pi_iid_reindex_preserving (tiltLaw μ H 1) e
  calc
    _ = ∫ x, G x ∂Measure.map (fun x : Fin r → S => fun i => x (e i))
        (Measure.pi (fun _ : Fin r => tiltLaw μ H 1)) :=
      (integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

lemma gibbsReplicaMean_fresh_last {H : S → ℝ} (hH : Measurable H)
    (hexp : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ)
    {G : (Fin r → S) → S → ℝ} (hG : Measurable (Function.uncurry G)) :
    gibbsReplicaMean μ H (r+1) (fun x => G (fun i => x i.succ) (x 0)) =
      gibbsReplicaMean μ H (r+1) (fun x => G (fun i => x i.castSucc) (x (Fin.last r))) := by
  have hr := gibbsReplicaMean_reindex μ hH hexp (r+1) (finRotate (r+1))
    (G:=fun x => G (fun i => x i.castSucc) (x (Fin.last r)))
    (hG.comp (show Measurable (fun x : Fin (r+1) → S => ((fun i : Fin r => x i.castSucc),x (Fin.last r))) from by fun_prop))
  have he (i : Fin r) : finRotate (r+1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simpa only [finRotate_last,he] using hr

end

lemma annealedInfiniteReplica_reindex {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
    (H : A → S → ℝ) (hH : Measurable (Function.uncurry H)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun a : A×(ℕ→S) => (a.1,fun i => a.2 (e i)))
      (annealedInfiniteReplicaMeasure κ P H hH) (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun x : ℕ→S => fun i => x (e i)) := by fun_prop
  have he : (kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map (fun x i => x (e i)) =
      kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ := by
    ext a s hs
    rw [Kernel.map_apply _ hm _]
    exact congrArg (fun μ : Measure (ℕ→S) => μ s)
      (infinite_iid_reindex_preserving (gibbsProbabilityKernel κ H a) e).map_eq
  refine ⟨by fun_prop, ?_⟩
  change (P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map
    (Prod.map id (fun x i => x (e i))) = _
  rw [← Measure.compProd_map hm,he]
  rfl

def compactRelabel {K : Type*} (e : Equiv.Perm ℕ) (Q : CompactArray K) : CompactArray K :=
  fun i j => Q (e i) (e j)

lemma compactRelabel_continuous {K : Type*} [TopologicalSpace K] (e : Equiv.Perm ℕ) :
    Continuous (compactRelabel (K:=K) e) := by unfold compactRelabel; fun_prop

lemma sourceGibbsArray_exchangeable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) e
  have hm : Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) :=
    (sourceJointArray_measurable (n+1) k).comp measurable_snd
  refine ⟨(compactRelabel_continuous e).measurable, ?_⟩
  change Measure.map _ (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ∘
    (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => (a.1,fun i => a.2 (e i)))) _ = _
  rw [← Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

lemma compact_exchangeability_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    {μ : ℕ → ProbabilityMeasure (CompactArray K)} {ν : ProbabilityMeasure (CompactArray K)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (e : Equiv.Perm ℕ)
    (he : ∀ n, MeasurePreserving (compactRelabel (K:=K) e) (μ n : Measure _) (μ n : Measure _)) :
    MeasurePreserving (compactRelabel (K:=K) e) (ν : Measure _) (ν : Measure _) := by
  have hc := compactRelabel_continuous (K:=K) e
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hc
  have he' (n : ℕ) : (μ n).map (compactRelabel e) = μ n := by
    apply Subtype.ext
    exact (he n).map_eq
  simp_rw [he'] at hmap
  have hv := tendsto_nhds_unique hmap hμ
  exact ⟨hc.measurable,congrArg Subtype.val hv⟩

end SphericalPerceptronFreeEnergy

end

end OAI
