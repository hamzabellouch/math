import Mathlib
import OAI.Probability.Perceptron.Variational.ContactGGRate

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernelFiniteProduct_measurable (ι : Type*) [Fintype ι] :
    Measurable (fun a => Measure.pi (fun _ : ι => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨s,hs,rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => κ.measurable_coe (hs i (mem_univ i))

lemma kernelInfiniteReplica_measurable (ι : Type*) :
    Measurable (fun a => Measure.infinitePi (fun _ : ι => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  intro s hs
  obtain ⟨I,E,hE,rfl⟩ := (mem_measurableCylinders s).mp hs
  have hm := (Measure.measurable_coe hE).comp (kernelFiniteProduct_measurable κ I)
  convert hm using 1
  funext a
  change (Measure.infinitePi (fun _ : ι => κ a)) (I.restrict ⁻¹' E) =
    (Measure.pi (fun _ : I => κ a)) E
  have hmI : Measurable (I.restrict : (ι → S) → I → S) := by fun_prop
  rw [← Measure.map_apply (f := I.restrict) hmI hE,Measure.infinitePi_map_restrict]

def kernelInfiniteReplica (ι : Type*) : Kernel A (ι → S) :=
  ⟨(fun a => Measure.infinitePi (fun _ : ι => κ a)),kernelInfiniteReplica_measurable κ ι⟩

instance (ι : Type*) : IsMarkovKernel (kernelInfiniteReplica κ ι) := ⟨fun _ => by
  change IsProbabilityMeasure (Measure.infinitePi _)
  infer_instance⟩

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

def annealedInfiniteReplicaMeasure : Measure (A × (ℕ → S)) := by
  letI : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  exact P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ

instance : IsProbabilityMeasure (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  unfold annealedInfiniteReplicaMeasure
  infer_instance

lemma annealedInfiniteReplica_prefix_integral (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) ∂P := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val)) :=
    hG.comp (by fun_prop)
  have hi : Integrable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hGB (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => kernelInfiniteReplica_prefix_integral _ a r hG

lemma annealedInfiniteReplica_gibbs_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P := by
  rw [annealedInfiniteReplica_prefix_integral κ P H hH r hG hGB]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r G

end

def sourceJointOverlap {N k : ℕ} (x y : NormalizedSpin N×IndexedLeaf k) : CompactJointOverlap :=
  (⟨spinOverlap x.1 y.1,abs_le.mp (spinOverlap_abs_le x.1 y.1)⟩,
    ⟨((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ),by
      constructor
      · positivity
      · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
        exact_mod_cast (indexedCommonDepth k y.2 x.2).isLt.le⟩)

lemma sourceJointOverlap_measurable (N k : ℕ) :
    Measurable (Function.uncurry (sourceJointOverlap (N:=N) (k:=k))) := by
  apply Measurable.prodMk
  · apply Measurable.subtype_mk
    exact (measurable_fst.fst.subtype_val.inner measurable_snd.fst.subtype_val)
  · apply Measurable.subtype_mk
    have hm : Measurable (fun a : IndexedLeaf k × IndexedLeaf k =>
      ((indexedCommonDepth k a.2 a.1).val:ℝ)/(k+1:ℕ)) := measurable_of_countable _
    exact hm.comp (measurable_fst.snd.prodMk measurable_snd.snd)

def sourceJointArray {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) : CompactArray CompactJointOverlap :=
  fun i j => sourceJointOverlap (x i) (x j)

lemma sourceJointArray_measurable (N k : ℕ) : Measurable (sourceJointArray (N:=N) (k:=k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (sourceJointOverlap_measurable N k).comp (show Measurable (fun x : ℕ → NormalizedSpin N×IndexedLeaf k => (x i,x j)) from by fun_prop)

def sourceGibbsArrayLaw (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) :
    ProbabilityMeasure (CompactArray CompactJointOverlap) :=
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let H := sourceCouplingHamiltonian n k f p d h u
  let μ := annealedInfiniteReplicaMeasure (sourceFullSpinLeafKernel n k) P H
    (sourceCouplingHamiltonian_measurable n k f p d h u)
  ⟨μ.map (fun a => sourceJointArray a.2),inferInstance⟩

lemma sourceGibbsArray_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : CompactArray CompactJointOverlap → ℝ} (hF : Measurable F) :
    (∫ Q, F Q ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, F (sourceJointArray a.2) ∂annealedInfiniteReplicaMeasure (sourceFullSpinLeafKernel n k)
        ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
        (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) := by
  exact integral_map ((sourceJointArray_measurable (n+1) k).comp measurable_snd).aemeasurable hF.aestronglyMeasurable

lemma sourceGibbsArray_block_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (r : ℕ)
    {F : CompactBlock CompactJointOverlap r → ℝ} (hF : Measurable F)
    {B : ℝ} (hFB : ∀ Q, |F Q|≤B) :
    (∫ Q, F (compactBlock r Q) ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, gibbsReplicaMean (sourceFullSpinLeafKernel n k a)
        (sourceCouplingHamiltonian n k f p d h u a) r
        (fun x => F (fun i j => sourceJointOverlap (x i) (x j)))
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw := by
  rw [sourceGibbsArray_integral n k f p d h u z t (F:=fun Q => F (compactBlock r Q))
    (hF.comp (compactBlock_continuous r).measurable)]
  have he := sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t
  have he0 : ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
    filter_upwards [he] with a ha
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  exact annealedInfiniteReplica_gibbs_prefix (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) _
    (sourceCouplingHamiltonian_measurable n k f p d h u) he0 r
    (hF.comp (Measurable.of_eval fun row => Measurable.of_eval fun column =>
      (sourceJointOverlap_measurable (n+1) k).comp
        ((measurable_pi_apply row).prodMk (measurable_pi_apply column))))
    (fun x => hFB _)

end SphericalPerceptronFreeEnergy

end

end OAI
