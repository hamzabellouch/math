import Mathlib
import OAI.Probability.SKFluctuations.WeightedFeatureTraceTelescope

namespace OAI

/-! Has Deriv At Dynamic Variance Continuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_dynamic_varianceContinuation {n : ℕ}
    {F D : ℝ → (Fin (n+1) → ℝ) → ℝ}
    {G H : ℝ → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ t, LipschitzWith C (F t))
    (hG : ∀ t i, BddSmooth 0 (G t i)) (hH : ∀ t i, BddSmooth 0 (H t i))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcG : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 i p.2))
    (hcH : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 i p.2))
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbG : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 i p.2))
    (hbH : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 i p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hd : ∀ s x v t, HasDerivAt (fun r : ℝ => F s (x+r • v))
      (∑ i, v i*G s i (x+t • v)) t)
    (hd₁ : ∀ s i x t, HasDerivAt (fun r : ℝ => G s i (x+r • Pi.single i 1))
      (H s i (x+t • Pi.single i 1)) t)
    {l r : ℝ} (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => F q y) (D s y) s)
    (q d : Fin (n+1) → ℝ) {m t : ℝ} (hm : 0 < m)
    (ht : t ∈ Ioo l r) (hqt : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceContinuation m (F s) (fun i => q i+s*d i) x)
      (signedVarianceDerivative m (F t) (G t) (H t) d (fun i => q i+t*d i) x+
        varianceTest m (F t) (D t) (fun i => q i+t*d i) x) t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  choose KG hKG bG using hbG
  choose KH hKH bH using hbH
  let Q : ℝ × ℝ → Fin (n+1) → ℝ := fun p i => q i+p.1*d i
  have hQ : Continuous Q := continuous_pi fun i => continuous_const.add (continuous_fst.mul continuous_const)
  have hF' : ∀ p : ℝ × ℝ, LipschitzWith C (F p.2) := fun p => hF p.2
  have hcF' : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => F p.1.2 p.2) :=
    hcF.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hc₁ : Continuous (fun p : ℝ × ℝ =>
      signedVarianceDerivative m (F p.2) (G p.2) (H p.2) d (Q p) x) := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.const_mul
    apply Continuous.add
    · exact dynamic_varianceTest_continuous hF' hcF'
        ((hcH i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        (fun p y => bH i (p.2,y)) m hQ continuous_const
    · apply Continuous.const_mul
      exact dynamic_varianceTest_continuous (K := (KG i)^2) hF' hcF'
        (((hcG i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).pow 2)
        (fun p y => by
          rw [abs_sq]
          exact (sq_abs (G p.2 i y)) ▸ sq_le_sq₀ (abs_nonneg _) (hKG i) |>.mpr (bG i (p.2,y))) m hQ continuous_const
  have hc₂ : Continuous (fun p : ℝ × ℝ => varianceTest m (F p.2) (D p.2) (Q p) x) :=
    dynamic_varianceTest_continuous hF' hcF'
      (hcD.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => bD (p.2,y)) m hQ continuous_const
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (hqt i))
  have hc₃ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceContinuation m (F p.2) (fun i => q i+s*d i) x)
        (signedVarianceDerivative m (F p.2) (G p.2) (H p.2) d (fun i => q i+p.1*d i) x) p.1 := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hp] with p hp
    obtain ⟨a,b,hpab,hab⟩ := (show ∀ᶠ s in 𝓝 p.1, ∀ i, 0 < q i+s*d i from by
      rw [eventually_all]
      intro i
      exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
        (eventually_gt_nhds (hp i))).exists_Ioo_subset
    obtain ⟨K,hK⟩ := parametric_signed_variance (hF p.2) (hG p.2) (hH p.2)
      (hd p.2) (hd₁ p.2) q d hm
    exact (hK a b (fun s hs => hab hs)).derivative p.1 hpab x
  have hc₄ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceContinuation m (F s) (fun i => q i+p.1*d i) x)
        (varianceTest m (F p.2) (D p.2) (fun i => q i+p.1*d i) x) p.2 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)] with p hp
    exact hasDerivAt_continuation_local hp hKD hm.ne'
      (fun s _ => ((hF s).continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s _ z => bD (s,x+z))
      ((exponentialIncrement_gaussian (fun i => Real.toNNReal (q i+p.1*d i))).integrable_shift (hF p.2) m x)
  have hchain := hasDerivAt_bivariate_chain
    (f := fun a b => varianceContinuation m (F b) (fun i => q i+a*d i) x)
    (f₁ := fun a b => signedVarianceDerivative m (F b) (G b) (H b) d (fun i => q i+a*d i) x)
    (f₂ := fun a b => varianceTest m (F b) (D b) (fun i => q i+a*d i) x)
    hc₃ hc₄ hc₁.continuousAt hc₂.continuousAt (hasDerivAt_id t) (hasDerivAt_id t)
  simpa only [id_eq,mul_one] using hchain

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι P : Type*} [Fintype ι] [TopologicalSpace P] [FirstCountableTopology P]

theorem dynamic_varianceTest_joint_continuous {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2))
    (m : ℝ) {q : P → ι → ℝ} (hq : Continuous q) :
    Continuous (fun p : P × (ι → ℝ) => varianceTest m (F p.1) (A p.1) (q p.1) p.2) := by
  obtain ⟨K,_,hb⟩ := hbA
  exact dynamic_varianceTest_continuous
    (fun p : P × (ι → ℝ) => hF p.1)
    (hcF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (hcA.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (fun p y => hb (p.1,y)) m (hq.comp continuous_fst) continuous_snd

omit [FirstCountableTopology P] in
theorem dynamic_varianceTest_absBounded {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA : AbsBounded (fun p : P × (ι → ℝ) => A p.1 p.2)) (m : ℝ) (q : P → ι → ℝ) :
    AbsBounded (fun p : P × (ι → ℝ) => varianceTest m (F p.1) (A p.1) (q p.1) p.2) := by
  obtain ⟨K,hK,hb⟩ := hbA
  refine ⟨K,hK,fun p => ?_⟩
  exact abs_tiltedMean_le
    ((hcA.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
    ((exponentialIncrement_gaussian _).integrable_shift (hF p.1) m p.2) (fun z => hb (p.1,p.2+z))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

noncomputable def affineVariation (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    List (SignedStep ι) → ℝ → (ι → ℝ) → ℝ
  | [], _ => fun _ => 0
  | st::ss, t => fun x =>
      signedVarianceDerivative st.1 (gaussianHierarchy w φ (affineSteps ss t))
        (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss t))
        (fun i y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1))
        st.2.2 (fun i => st.2.1 i+t*st.2.2 i) x+
      varianceTest st.1 (gaussianHierarchy w φ (affineSteps ss t)) (affineVariation w φ ss t)
        (fun i => st.2.1 i+t*st.2.2 i) x

theorem affineVariation_regular {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    Continuous (fun p : ℝ × (ι → ℝ) => affineVariation w φ ss p.1 p.2) ∧
      AbsBounded (fun p : ℝ × (ι → ℝ) => affineVariation w φ ss p.1 p.2) := by
  obtain ⟨C,hF⟩ := affineHierarchy_lipschitz hw φ
  induction ss generalizing a with
  | nil => exact ⟨continuous_const,0,le_rfl,fun _ => by simp [affineVariation]⟩
  | cons st ss ih =>
    have ht := ih ha.2.2.2
    have hFc := affineHierarchy_continuous hw φ ss ha.2.2.2
    have hGc (i : ι) := affineHierarchyMean_continuous hw φ (fun σ => φ σ (Pi.single i 1)) ss ha.2.2.2
    have hHc (i : ι) := affineHierarchyHessian_continuous hw φ (Pi.single i 1) ss ha.2.2.2
    have hGb (i : ι) := affineHierarchyMean_absBounded hw φ (fun σ => φ σ (Pi.single i 1)) ss ha.2.2.2
    have hHb (i : ι) := affineHierarchyHessian_absBounded hw φ (Pi.single i 1) ss ha.2.2.2
    have hGsq (i : ι) : AbsBounded (fun p : ℝ × (ι → ℝ) =>
        (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss p.1) p.2)^2) := by
      simpa only [pow_two] using (hGb i).mul (hGb i)
    have hq : Continuous (fun t i => st.2.1 i+t*st.2.2 i) :=
      continuous_pi fun i => continuous_const.add (continuous_id.mul continuous_const)
    have hcH (i : ι) := dynamic_varianceTest_joint_continuous
      (A := fun t y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1)) (hF ss ha.2.2.2) hFc (hHc i) (hHb i) st.1 hq
    have hcG (i : ι) := dynamic_varianceTest_joint_continuous
      (A := fun t y => (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss t) y)^2) (hF ss ha.2.2.2) hFc ((hGc i).pow 2) (hGsq i) st.1 hq
    have hbH (i : ι) := dynamic_varianceTest_absBounded
      (A := fun t y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1)) (hF ss ha.2.2.2) (hHc i) (hHb i) st.1 (fun t i => st.2.1 i+t*st.2.2 i)
    have hbG (i : ι) := dynamic_varianceTest_absBounded
      (A := fun t y => (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss t) y)^2) (hF ss ha.2.2.2) ((hGc i).pow 2) (hGsq i) st.1 (fun t i => st.2.1 i+t*st.2.2 i)
    constructor
    · exact (continuous_finsetSum _ fun i _ => ((hcH i).add ((hcG i).const_mul st.1)).const_mul (st.2.2 i/2)).add
        (dynamic_varianceTest_joint_continuous (hF ss ha.2.2.2) hFc ht.1 ht.2 st.1 hq)
    · exact (AbsBounded.sum (fun i => ((hbH i).add ((hbG i).const_mul st.1)).const_mul (st.2.2 i/2))).add
        (dynamic_varianceTest_absBounded (hF ss ha.2.2.2) ht.1 ht.2 st.1 (fun t i => st.2.1 i+t*st.2.2 i))

 

theorem gaussianHierarchy_affine_variation {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (ss : List (SignedStep (Fin (n+1)))) {a l r : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0))
    (hq : ∀ st ∈ ss, ∀ t ∈ Ioo l r, ∀ i, 0 < st.2.1 i+t*st.2.2 i)
    {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => gaussianHierarchy w φ (affineSteps ss s) x)
      (affineVariation w φ ss t x) t := by
  induction ss generalizing a t x with
  | nil => exact hasDerivAt_const t _
  | cons st ss ih =>
    obtain ⟨C,hF⟩ := affineHierarchy_lipschitz hw φ
    have htail := affineSteps_ordered ss ha.2.2.2
    have hD := affineVariation_regular hw φ ss ha.2.2.2
    exact hasDerivAt_dynamic_varianceContinuation
      (F := fun t => gaussianHierarchy w φ (affineSteps ss t))
      (G := fun t i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss t))
      (H := fun t i y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1))
      (D := affineVariation w φ ss)
      (hF ss ha.2.2.2)
      (fun t i => gaussianHierarchyMean_smooth hw φ _ _ (htail t) 0)
      (fun t i => gaussianHierarchyResponse_smooth hw φ _ _ _ (htail t) 0)
      (affineHierarchy_continuous hw φ ss ha.2.2.2)
      (fun i => affineHierarchyMean_continuous hw φ _ ss ha.2.2.2)
      (fun i => affineHierarchyHessian_continuous hw φ _ ss ha.2.2.2)
      hD.1
      (fun i => affineHierarchyMean_absBounded hw φ _ ss ha.2.2.2)
      (fun i => affineHierarchyHessian_absBounded hw φ _ ss ha.2.2.2)
      hD.2
      (fun s y v u => by
        rw [← gaussianHierarchyMean_feature_components hw φ _ (htail s) v (y+u • v)]
        exact gaussianHierarchy_hasDerivAt hw φ _ (htail s) y v u)
      (fun s i y u => gaussianHierarchyMean_hasDerivAt hw φ _ _ (htail s) y _ u)
      (fun s hs y => ih ha.2.2.2 (fun z hz => hq z (List.mem_cons_of_mem _ hz)) hs y)
      st.2.1 st.2.2 ha.2.2.1 ht (hq st List.mem_cons_self t ht) x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

noncomputable def featureKernel (φ : S → (ι → ℝ) →L[ℝ] ℝ) (d : ι → ℝ) (σ τ : S) : ℝ :=
  ∑ i, d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)

 

noncomputable def pathKernelPenalty (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (S → S → ℝ) → ℝ → List (SignedStep ι) → ℝ → (ι → ℝ) → ℝ
  | K,a,[],_ => fun x => (1-a)*hierarchyPairMean w φ K [] x
  | K,a,st::ss,t => fun x => (st.1-a)*hierarchyPairMean w φ K (affineSteps (st::ss) t) x+
      varianceTest st.1 (gaussianHierarchy w φ (affineSteps ss t))
        (pathKernelPenalty w φ (fun σ τ => K σ τ+featureKernel φ st.2.2 σ τ) st.1 ss t)
        (fun i => st.2.1 i+t*st.2.2 i) x

theorem pathKernelPenalty_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (t : ℝ) (r : ℕ) :
    BddSmooth r (pathKernelPenalty w φ K a ss t) := by
  induction ss generalizing a K with
  | nil => exact (hierarchyPairMean_smooth hw φ K [] ha r).const_mul (1-a)
  | cons st ss ih =>
    exact ((hierarchyPairMean_smooth hw φ K _ (affineSteps_ordered _ ha t) r).const_mul (st.1-a)).add
      ((ih _ ha.2.2.2).shiftedMean (gaussianHierarchy_regular hw φ _ (affineSteps_ordered _ ha.2.2.2 t) r)
        (gaussianHierarchy_integrable hw φ _ (affineSteps_ordered _ ha.2.2.2 t) st.1 _))

omit [DecidableEq ι] in
theorem kernelPenalty_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K L : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => K σ τ+L σ τ) a steps x =
      kernelPenalty w φ K a steps x+kernelPenalty w φ L a steps x := by
  simpa only [one_mul] using kernelPenalty_linear hw φ K L steps ha 1 1 x

theorem affineVariation_kernel_telescope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Q : SignedStep ι → ℝ) (ss : List (SignedStep ι))
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Q st)
    (K : S → S → ℝ) {a : ℝ} (ha : OrderedSteps a (affineSteps ss 0)) (t : ℝ) (x : ι → ℝ) :
    affineVariation w φ ss t x = (ss.map Q).sum/2+
      (1/2:ℝ)*kernelPenalty w φ K a (affineSteps ss t) x-
      (1/2:ℝ)*pathKernelPenalty w φ K a ss t x := by
  induction ss generalizing a K x with
  | nil => simp [affineVariation,pathKernelPenalty,kernelPenalty]
  | cons st ss ih =>
    have ht : OrderedSteps st.1 (affineSteps ss t) := affineSteps_ordered ss ha.2.2.2 t
    have hi := gaussianHierarchy_integrable hw φ (affineSteps ss t) ht st.1
      (fun i => Real.toNNReal (st.2.1 i+t*st.2.2 i)) x
    have hk := kernelPenalty_smooth hw φ K (affineSteps ss t) ht 0
    have hd := kernelPenalty_smooth hw φ (featureKernel φ st.2.2) (affineSteps ss t) ht 0
    have hp := pathKernelPenalty_smooth hw φ
      (fun σ τ => K σ τ+featureKernel φ st.2.2 σ τ) ss ha.2.2.2 t 0
    have he := funext fun y => ih (fun z hz => hQ z (List.mem_cons_of_mem _ hz))
      (fun σ τ => K σ τ+featureKernel φ st.2.2 σ τ) ha.2.2.2 y
    simp only [affineVariation,gaussianHierarchyHessian]
    rw [signedVarianceDerivative_feature_trace hw φ _ (fun i => st.2.1 i+t*st.2.2 i) (hQ st List.mem_cons_self) _ ht]
    have hfeat := funext fun y => kernelPenalty_weighted_features hw φ (fun i => Pi.single i 1)
      st.2.2 (affineSteps ss t) ht y
    change (fun y => kernelPenalty w φ (featureKernel φ st.2.2) st.1 (affineSteps ss t) y) = _ at hfeat
    rw [← hfeat,he]
    have hadd := funext fun y => kernelPenalty_add hw φ K (featureKernel φ st.2.2) (affineSteps ss t) ht y
    rw [hadd]
    simp only [varianceTest]
    rw [shiftedMean_sub ((BddSmooth.const 0 ((ss.map Q).sum/2)).add ((hk.add hd).const_mul (1/2:ℝ)))
      (hp.const_mul (1/2:ℝ)) hi,
      shiftedMean_add (BddSmooth.const 0 ((ss.map Q).sum/2)) ((hk.add hd).const_mul (1/2:ℝ)) hi,
      shiftedMean_const _ hi,shiftedMean_const_mul,shiftedMean_const_mul,
      shiftedMean_add hk hd hi]
    simp only [List.map_cons,List.sum_cons,affineSteps_cons,kernelPenalty,pathKernelPenalty,varianceTest]
    ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

def PathKernelBound (φ : S → (ι → ℝ) →L[ℝ] ℝ) (B : List (SignedStep ι) → ℝ) :
    (S → S → ℝ) → List (SignedStep ι) → Prop
  | K,[] => ∀ σ τ, -B [] ≤ K σ τ
  | K,st::ss => (∀ σ τ, -B (st::ss) ≤ K σ τ) ∧
      PathKernelBound φ B (fun σ τ => K σ τ+featureKernel φ st.2.2 σ τ) ss

def pathKernelCost (B : List (SignedStep ι) → ℝ) : ℝ → List (SignedStep ι) → ℝ
  | a,[] => (1-a)*B []
  | a,st::ss => (st.1-a)*B (st::ss)+pathKernelCost B st.1 ss

theorem pathKernelPenalty_lower {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (B : List (SignedStep ι) → ℝ) (K : S → S → ℝ)
    (ss : List (SignedStep ι)) {a : ℝ} (ha : OrderedSteps a (affineSteps ss 0))
    (hB : PathKernelBound φ B K ss) (t : ℝ) (x : ι → ℝ) :
    -pathKernelCost B a ss ≤ pathKernelPenalty w φ K a ss t x := by
  induction ss generalizing a K x with
  | nil =>
    change -((1-a)*B []) ≤ (1-a)*hierarchyPairMean w φ K [] x
    have hh := hierarchyPairMean_mono hw φ hB [] ha x
    rw [hierarchyPairMean_const hw φ [] ha] at hh
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ha.2)
  | cons st ss ih =>
    have ht : OrderedSteps st.1 (affineSteps ss t) := affineSteps_ordered ss ha.2.2.2 t
    have hi := gaussianHierarchy_integrable hw φ (affineSteps ss t) ht st.1
      (fun i => Real.toNNReal (st.2.1 i+t*st.2.2 i)) x
    have hh := hierarchyPairMean_mono hw φ hB.1 (affineSteps (st::ss) t) (affineSteps_ordered _ ha t) x
    rw [hierarchyPairMean_const hw φ _ (affineSteps_ordered _ ha t)] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ha.2.1)
    have hp := pathKernelPenalty_smooth hw φ
      (fun σ τ => K σ τ+featureKernel φ st.2.2 σ τ) ss ha.2.2.2 t 0
    have hmean := shiftedMean_mono (BddSmooth.const 0 (-pathKernelCost B st.1 ss)) hp
      (fun y => ih _ ha.2.2.2 hB.2 y) hi
    rw [shiftedMean_const _ hi] at hmean
    change -((st.1-a)*B (st::ss)+pathKernelCost B st.1 ss) ≤ _
    change _ ≤ (st.1-a)*hierarchyPairMean w φ K (affineSteps (st::ss) t) x+_
    simp only [varianceTest]
    linarith

 
theorem affineVariation_le_cost {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Q : SignedStep ι → ℝ) (ss : List (SignedStep ι))
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Q st)
    (B : List (SignedStep ι) → ℝ) {a : ℝ} (ha : OrderedSteps a (affineSteps ss 0))
    (hB : PathKernelBound φ B (fun _ _ => 0) ss) (t : ℝ) (x : ι → ℝ) :
    affineVariation w φ ss t x-(ss.map Q).sum/2 ≤ pathKernelCost B a ss/2 := by
  rw [affineVariation_kernel_telescope hw φ Q ss hQ (fun _ _ => 0) ha t x,
    kernelPenalty_const hw φ _ (affineSteps_ordered _ ha t)]
  have hh := pathKernelPenalty_lower hw φ B (fun _ _ => 0) ss ha hB t x
  linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem gaussianHierarchy_affine_chord_pos {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (Q : SignedStep (Fin (n+1)) → ℝ)
    (ss : List (SignedStep (Fin (n+1))))
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Q st)
    (B : List (SignedStep (Fin (n+1))) → ℝ) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (hB : PathKernelBound φ B (fun _ _ => 0) ss)
    (hq : ∀ st ∈ ss, ∀ t ∈ Ioo (0:ℝ) 1, ∀ i, 0 < st.2.1 i+t*st.2.2 i)
    (x : Fin (n+1) → ℝ) :
    gaussianHierarchy w φ (affineSteps ss 1) x-gaussianHierarchy w φ (affineSteps ss 0) x-
      (ss.map Q).sum/2 ≤ pathKernelCost B a ss/2 := by
  have hc : Continuous (fun t : ℝ => gaussianHierarchy w φ (affineSteps ss t) x -
      (ss.map Q).sum * t / 2) := by
    exact ((affineHierarchy_continuous hw φ ss ha).comp
      (continuous_id.prodMk (continuous_const (y := x)))).fun_sub
      ((continuous_id.const_mul (ss.map Q).sum).div_const 2)
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) := (gaussianHierarchy_affine_variation hw φ ss ha hq ht x).fun_sub
    (((hasDerivAt_id t).const_mul (ss.map Q).sum).div_const 2)
  simp only [id_eq] at hd
  have hh := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc.continuousOn
    (fun t ht => (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hd t (by simpa only [interior_Icc] using ht)).deriv]
      simpa only [mul_one] using affineVariation_le_cost hw φ Q ss hQ B ha hB t x)
    0 (by simp) 1 (by simp) (by norm_num)
  simp only [mul_one,mul_zero,zero_div,sub_zero] at hh
  linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

def bumpSignedSteps (ss : List (SignedStep ι)) (e : ℝ) : List (SignedStep ι) :=
  ss.map fun st => (st.1,(fun i => st.2.1 i+e),st.2.2)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem bumpSignedSteps_nil (e : ℝ) : bumpSignedSteps ([] : List (SignedStep ι)) e = [] := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem bumpSignedSteps_cons (st : SignedStep ι) (ss : List (SignedStep ι)) (e : ℝ) :
    bumpSignedSteps (st::ss) e = (st.1,(fun i => st.2.1 i+e),st.2.2)::bumpSignedSteps ss e := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem bumpSignedSteps_zero (ss : List (SignedStep ι)) : bumpSignedSteps ss 0 = ss := by
  simp [bumpSignedSteps]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem bumpSignedSteps_neg (ss : List (SignedStep ι)) (e : ℝ) :
    bumpSignedSteps (bumpSignedSteps ss e) (-e) = ss := by
  simp [bumpSignedSteps,List.map_map,Function.comp_def]

omit [Fintype ι] [DecidableEq ι] in
theorem bumpSignedSteps_ordered (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (e : ℝ) :
    OrderedSteps a (affineSteps (bumpSignedSteps ss e) 0) := by
  induction ss generalizing a with
  | nil => exact ha
  | cons st ss ih => exact ⟨ha.1,ha.2.1,ha.2.2.1,ih ha.2.2.2⟩

omit [Fintype S] [Nonempty S] in
theorem PathKernelBound.bump {φ : S → (ι → ℝ) →L[ℝ] ℝ} {B : List (SignedStep ι) → ℝ}
    {K : S → S → ℝ} {ss : List (SignedStep ι)} (hB : PathKernelBound φ B K ss) (e : ℝ) :
    PathKernelBound φ (fun tail => B (bumpSignedSteps tail (-e))) K (bumpSignedSteps ss e) := by
  induction ss generalizing K with
  | nil => exact hB
  | cons st ss ih =>
    constructor
    · change ∀ σ τ, -B (bumpSignedSteps (bumpSignedSteps (st::ss) e) (-e)) ≤ K σ τ
      simpa only [bumpSignedSteps_neg] using hB.1
    · exact ih hB.2

omit [Fintype ι] [DecidableEq ι] in
theorem pathKernelCost_bump (B : List (SignedStep ι) → ℝ) (ss : List (SignedStep ι)) (a e : ℝ) :
    pathKernelCost (fun tail => B (bumpSignedSteps tail (-e))) a (bumpSignedSteps ss e) =
      pathKernelCost B a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons st ss ih =>
    change (st.1-a)*B (bumpSignedSteps (bumpSignedSteps (st::ss) e) (-e))+
      pathKernelCost (fun tail => B (bumpSignedSteps tail (-e))) st.1 (bumpSignedSteps ss e) =
        (st.1-a)*B (st::ss)+pathKernelCost B st.1 ss
    rw [bumpSignedSteps_neg,ih]

omit [DecidableEq ι] in
theorem affineBump_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (t : ℝ) (x : ι → ℝ) :
    Continuous (fun e => gaussianHierarchy w φ (affineSteps (bumpSignedSteps ss e) t) x) := by
  let cs : List (ℝ × (ℝ → ι → ℝ)) := ss.map fun st =>
    (st.1,fun e i => st.2.1 i+e+t*st.2.2 i)
  have he (e : ℝ) : covarianceSteps cs e = affineSteps (bumpSignedSteps ss e) t := by
    simp only [cs,covarianceSteps,affineSteps,affineCovariances,bumpSignedSteps,List.map_map,Function.comp_def]
  have hc : ∀ st ∈ cs, Continuous st.2 := by
    intro st hs
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hs
    exact continuous_pi fun i => (continuous_const.add continuous_id).add continuous_const
  have hp : ∀ st ∈ cs, 0 < st.1 := by
    intro st hs
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact affineCovariances_positive ss ha (z.1,fun u i => z.2.1 i+u*z.2.2 i)
      (List.mem_map.mpr ⟨z,hz,rfl⟩)
  have hh := (covarianceFamily_potential_continuous hw φ cs hp hc).comp
    (continuous_id.prodMk (continuous_const (y := x)))
  simpa only [he, Function.comp_def, id_eq] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem gaussianHierarchy_affine_chord {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (Q : SignedStep (Fin (n+1)) → ℝ)
    (ss : List (SignedStep (Fin (n+1))))
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Q st)
    (B : List (SignedStep (Fin (n+1))) → ℝ) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (hB : PathKernelBound φ B (fun _ _ => 0) ss)
    (hq : ∀ st ∈ ss, ∀ i, 0 ≤ st.2.1 i ∧ 0 ≤ st.2.1 i+st.2.2 i)
    (x : Fin (n+1) → ℝ) :
    gaussianHierarchy w φ (affineSteps ss 1) x-gaussianHierarchy w φ (affineSteps ss 0) x-
      (ss.map Q).sum/2 ≤ pathKernelCost B a ss/2 := by
  have hlim : Tendsto (fun e : ℝ =>
      gaussianHierarchy w φ (affineSteps (bumpSignedSteps ss e) 1) x-
      gaussianHierarchy w φ (affineSteps (bumpSignedSteps ss e) 0) x-(ss.map Q).sum/2)
      (𝓝 0) (𝓝 (gaussianHierarchy w φ (affineSteps ss 1) x-
      gaussianHierarchy w φ (affineSteps ss 0) x-(ss.map Q).sum/2)) := by
    simpa only [bumpSignedSteps_zero] using
      (((affineBump_continuous hw φ ss ha 1 x).continuousAt (x := 0)).tendsto.sub
        ((affineBump_continuous hw φ ss ha 0 x).continuousAt (x := 0)).tendsto).sub_const ((ss.map Q).sum/2)
  have he (e : ℝ) (he : 0 < e) :
      gaussianHierarchy w φ (affineSteps (bumpSignedSteps ss e) 1) x-
      gaussianHierarchy w φ (affineSteps (bumpSignedSteps ss e) 0) x-
      (ss.map Q).sum/2 ≤ pathKernelCost B a ss/2 := by
    let Qe : SignedStep (Fin (n+1)) → ℝ :=
      fun st => Q (st.1,(fun i => st.2.1 i-e),st.2.2)
    have hQe : ∀ st ∈ bumpSignedSteps ss e, ∀ σ,
        ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Qe st := by
      intro st hs σ
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
      simpa only [Qe,add_sub_cancel_right] using hQ z hz σ
    have hp : ∀ st ∈ bumpSignedSteps ss e, ∀ t ∈ Ioo (0:ℝ) 1, ∀ i,
        0 < st.2.1 i+t*st.2.2 i := by
      intro st hs t ht i
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
      dsimp only
      have hz₀ := (hq z hz i).1
      have hz₁ := (hq z hz i).2
      have h := mul_nonneg (sub_nonneg.mpr ht.2.le) hz₀
      have h' := mul_nonneg ht.1.le hz₁
      nlinarith
    have hv := gaussianHierarchy_affine_chord_pos hw φ Qe (bumpSignedSteps ss e) hQe
      (fun tail => B (bumpSignedSteps tail (-e))) (bumpSignedSteps_ordered ss ha e)
      (hB.bump e) hp x
    have hsum : ((bumpSignedSteps ss e).map Qe).sum = (ss.map Q).sum := by
      simp only [bumpSignedSteps,List.map_map,Function.comp_def,Qe,add_sub_cancel_right]
    rw [hsum,pathKernelCost_bump] at hv
    exact hv
  apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  filter_upwards [self_mem_nhdsWithin] with e he'
  exact he e he' 

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem PathKernelBound.congr_bounds {φ : S → (ι → ℝ) →L[ℝ] ℝ} {B C : List (SignedStep ι) → ℝ}
    {K : S → S → ℝ} {ss : List (SignedStep ι)} (hB : PathKernelBound φ B K ss)
    (he : ∀ tail, tail.length ≤ ss.length → B tail = C tail) : PathKernelBound φ C K ss := by
  induction ss generalizing K with
  | nil => simpa only [PathKernelBound,← he [] (by simp)] using hB
  | cons st ss ih =>
    refine ⟨?_,ih hB.2 (fun tail htail => he tail (htail.trans (by simp)))⟩
    simpa only [← he (st::ss) le_rfl] using hB.1

omit [Fintype ι] [DecidableEq ι] in
theorem pathKernelCost_congr {B C : List (SignedStep ι) → ℝ} (ss : List (SignedStep ι)) (a : ℝ)
    (he : ∀ tail, tail.length ≤ ss.length → B tail = C tail) :
    pathKernelCost B a ss = pathKernelCost C a ss := by
  induction ss generalizing a with
  | nil => simp only [pathKernelCost,he [] (by simp)]
  | cons st ss ih => rw [pathKernelCost,pathKernelCost,he (st::ss) le_rfl,ih _ (fun tail ht => he tail (ht.trans (by simp)))]

omit [Fintype ι] [DecidableEq ι] in
theorem pathKernelCost_continuous (B : List (SignedStep ι) → ℝ) (ss : List (SignedStep ι)) :
    Continuous (fun a => pathKernelCost B a ss) := by
  cases ss with
  | nil => exact (continuous_const.sub continuous_id).mul continuous_const
  | cons st ss => exact ((continuous_const.sub continuous_id).mul continuous_const).add continuous_const

omit [Fintype ι] [DecidableEq ι] in
def affineInitialMass : List (SignedStep ι) → ℝ
  | [] => 1
  | st::_ => st.1

omit [Fintype ι] [DecidableEq ι] in
theorem affineInitialMass_pos (ss : List (SignedStep ι)) (ha : OrderedSteps 0 (affineSteps ss 0)) :
    0 < affineInitialMass ss := by
  cases ss with
  | nil => exact zero_lt_one
  | cons st ss => exact ha.2.2.1

omit [Fintype ι] [DecidableEq ι] in
theorem affineSteps_ordered_initial (ss : List (SignedStep ι)) (ha : OrderedSteps 0 (affineSteps ss 0))
    {a : ℝ} (h₀ : 0 ≤ a) (h₁ : a ≤ affineInitialMass ss) : OrderedSteps a (affineSteps ss 0) := by
  cases ss with
  | nil => exact ⟨h₀,h₁⟩
  | cons st ss => exact ⟨h₀,h₁,ha.2.2⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_affine_chord {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (T : (Fin (n+1) → ℝ) → ℝ)
    (ss : List (SignedStep (Fin (n+1)))) (q d : Fin (n+1) → ℝ)
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = T st.2.2)
    (hD : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = T d)
    (B : List (SignedStep (Fin (n+1))) → ℝ)
    (ha : OrderedSteps 0 (affineSteps ss 0)) (hB : PathKernelBound φ B (featureKernel φ d) ss)
    (hq : ∀ st ∈ ss, ∀ i, 0 ≤ st.2.1 i)
    (hr : ∀ st ∈ ss, ∀ i, 0 ≤ st.2.1 i+st.2.2 i)
    (hq₀ : ∀ i, 0 ≤ q i) (hr₀ : ∀ i, 0 ≤ q i+d i) (x : Fin (n+1) → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+d i)))
        (gaussianHierarchy w φ (affineSteps ss 1)) x-
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i)))
        (gaussianHierarchy w φ (affineSteps ss 0)) x-
      (T d+(ss.map fun st => T st.2.2).sum)/2 ≤ pathKernelCost B 0 ss/2 := by
  let C : List (SignedStep (Fin (n+1))) → ℝ := fun tail =>
    if ss.length < tail.length then 0 else B tail
  have hCB : ∀ tail, tail.length ≤ ss.length → B tail = C tail := by
    intro tail ht
    simp only [C,ite_eq_right (not_lt.mpr ht)]
  have htailB := hB.congr_bounds hCB
  have hcost (a) : pathKernelCost C a ss = pathKernelCost B a ss := (pathKernelCost_congr ss a hCB).symm
  have hp (e : ℝ) (he : 0 < e) (hem : e ≤ affineInitialMass ss) :
      gaussianHierarchy w φ (affineSteps ((e,q,d)::ss) 1) x-
        gaussianHierarchy w φ (affineSteps ((e,q,d)::ss) 0) x-
          (T d+(ss.map fun st => T st.2.2).sum)/2 ≤ pathKernelCost B e ss/2 := by
    have hordered : OrderedSteps 0 (affineSteps ((e,q,d)::ss) 0) :=
      ⟨le_rfl,he.le,he,affineSteps_ordered_initial ss ha he.le hem⟩
    have hbounds : PathKernelBound φ C (fun _ _ => 0) ((e,q,d)::ss) := by
      constructor
      · intro σ τ
        simp [C,List.length_cons]
      · simpa only [zero_add] using htailB
    have hh := gaussianHierarchy_affine_chord hw φ (fun st => T st.2.2) ((e,q,d)::ss)
      (fun st hst => by rcases List.mem_cons.mp hst with rfl|hst; exact hD; exact hQ st hst)
      C hordered hbounds
      (fun st hst i => by
        rcases List.mem_cons.mp hst with rfl|hst
        · exact ⟨hq₀ i,hr₀ i⟩
        · exact ⟨hq st hst i,hr st hst i⟩) x
    simpa only [List.map_cons,List.sum_cons,pathKernelCost,C,ite_eq_left (by simp : ss.length < (((e,q,d)::ss).length)),
      mul_zero,zero_add,hcost] using hh
  have hlim (t : ℝ) : Tendsto
      (fun e => gaussianHierarchy w φ (affineSteps ((e,q,d)::ss) t) x) (𝓝[>] (0:ℝ))
      (𝓝 (zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+t*d i)))
        (gaussianHierarchy w φ (affineSteps ss t)) x)) := by
    obtain ⟨L,hL⟩ := (gaussianHierarchy_regular hw φ _ (affineSteps_ordered ss ha t) 0).1
    exact shiftedContinuation_tendsto_zero_mass hL
      (exponentialIncrement_gaussian (fun i => Real.toNNReal (q i+t*d i))) x
  have hleft := ((hlim 1).sub (hlim 0)).sub_const ((T d+(ss.map fun st => T st.2.2).sum)/2)
  have hright := ((pathKernelCost_continuous B ss).div_const 2).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0:ℝ)) (a := 0))
  have hevent : ∀ᶠ e in 𝓝[>] (0:ℝ),
      gaussianHierarchy w φ (affineSteps ((e,q,d)::ss) 1) x-
        gaussianHierarchy w φ (affineSteps ((e,q,d)::ss) 0) x-
          (T d+(ss.map fun st => T st.2.2).sum)/2 ≤ pathKernelCost B e ss/2 := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (affineInitialMass_pos ss ha))] with e he hem
    exact hp e he hem.le
  have hh := le_of_tendsto_of_tendsto hleft hright hevent
  simpa only [one_mul,zero_mul,add_zero] using hh

end SKFluctuations.Hierarchy

end

end OAI
