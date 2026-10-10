import Mathlib
import OAI.Probability.IsingPerceptron.RetainedDisplacement
import OAI.Probability.IsingPerceptron.TiltedLabelLaw

namespace OAI

/-! Sampling Independent. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

lemma independent_marks_sampling {Ω G X : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace X] (P : Measure Ω) (Q : Measure G) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (K : Kernel Ω X) [IsMarkovKernel K] :
    ((P.prod Q) ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) =
      (K ∘ₘ P).prod Q := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  simp only [Kernel.comap_apply]
  have hI : Measurable (fun p : Ω × G => ∫⁻ x, F (x,p.2) ∂K p.1) :=
    (show Measurable (fun p : (Ω × G) × X => F (p.2,p.1.2)) from by fun_prop).lintegral_kernel_prod_right' (κ := K.comap Prod.fst measurable_fst)
  rw [lintegral_prod _ hI.aemeasurable]
  have he (ω : Ω) : (∫⁻ g, ∫⁻ x, F (x,g) ∂K ω ∂Q) = ∫⁻ x, ∫⁻ g, F (x,g) ∂Q ∂K ω :=
    lintegral_lintegral_swap (by fun_prop)
  simp_rw [he]
  rw [lintegral_prod _ hF.aemeasurable]
  exact (Measure.lintegral_bind (Kernel.aemeasurable K) (hF.lintegral_prod_right').aemeasurable).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev PrefixPattern (n r : ℕ) := Fin r → Fin r → Fin n → Bool

def labelPrefixPattern (n r : ℕ) (σ : Fin r → LabeledLeaf n) : PrefixPattern n r :=
  fun i j d => if (labeledAddress n (σ i)).take (d+1) = (labeledAddress n (σ j)).take (d+1) then true else false

def markPrefixPattern (n r : ℕ) (σ : Fin r → NoiseLeaf ℝ n) : PrefixPattern n r :=
  fun i j d => if noiseLeafMark n (σ i) d = noiseLeafMark n (σ j) d then true else false

lemma measurable_markPrefixPattern (n r : ℕ) : Measurable (markPrefixPattern n r) := by
  unfold markPrefixPattern
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  apply Measurable.of_eval; intro d
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_noiseLeafMark n d).comp (measurable_pi_apply i))
    ((measurable_noiseLeafMark n d).comp (measurable_pi_apply j))

lemma markPrefixPattern_labeled (n r : ℕ) (ω : LabeledTree n) (g : ForestVertex n → ℝ)
    (hg : Function.Injective g) (σ : Fin r → LabeledLeaf n) :
    markPrefixPattern n r (fun i => labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n g) (σ i)) =
      labelPrefixPattern n r σ := by
  funext i j d
  unfold markPrefixPattern labelPrefixPattern
  simp only [noiseLeafMark_eq_iff_prefix n ω g hg]

lemma noiseLeafProduct_exp_marks (n : ℕ) (E : ℕ → ℝ → ℝ) (v : NoiseLeaf ℝ n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => Real.exp (E i p.2))
      (fun _ _ => PUnit.unit) PUnit.unit v =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, E i (noiseLeafMark n v i))) := by
  induction n generalizing E with
  | zero => simp [noiseLeafProduct]
  | succ n ih =>
    rw [noiseLeafProduct,ih,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
      Fin.sum_univ_succ]
    rfl

lemma noiseLeafProduct_retained_labeled (n : ℕ) (b a : ℕ → ℝ) (ω : LabeledTree n)
    (g : ForestVertex n → ℝ) (v : LabeledLeaf n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2)
      (fun _ _ => PUnit.unit) PUnit.unit (labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n g) v) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, (a i*g (edgeAt n v i)-b i*a i^2/2))) := by
  rw [show (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2) =
    (fun i p => Real.exp (a i*p.2-b i*a i^2/2)) by rfl]
  rw [noiseLeafProduct_exp_marks n (fun i x => a i*x-b i*a i^2/2)]
  simp only [noiseLeafMark_labeled]

lemma noiseLeafProduct_single_level (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (ω : LabeledTree n) (g : ForestVertex n → ℝ) (v : LabeledLeaf n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (if i = d then t else 0) p.2)
      (fun _ _ => PUnit.unit) PUnit.unit (labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n g) v) =
      ENNReal.ofReal (Real.exp (t*g (edgeAt n v d)-b d*t^2/2)) := by
  rw [noiseLeafProduct_retained_labeled]
  congr 2
  rw [Finset.sum_eq_single d]
  · simp
  · intro i _ hi
    have hne : (i:ℕ) ≠ d := fun h => hi (Fin.ext h)
    simp [hne]
  · simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_selected_coordinate {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {e : X → I} (he : Measurable e) :
    Measurable (fun p : X × (I → ℝ) => p.2 (e p.1)) := by
  have hv : Measurable (fun p : (I → ℝ) × I => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  exact hv.comp (measurable_snd.prodMk (he.comp measurable_fst))

lemma selected_coordinate_prod_law {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {e : X → I} (he : Measurable e) (v : Measure ℝ) [IsProbabilityMeasure v]
    (hm : ∀ x, μ (e x) = v) :
    (P.prod (Measure.infinitePi μ)).map (fun p => (p.1,p.2 (e p.1))) = P.prod v := by
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hT]
  have hFT : Measurable (fun p : X × (I → ℝ) => F (p.1,p.2 (e p.1))) := hF.comp hT
  rw [lintegral_prod _ hFT.aemeasurable]
  rw [lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro x
  have hFx : Measurable (fun y => F (x,y)) := hF.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hFx (measurable_pi_apply (e x))]
  change (∫⁻ a, F (x,a) ∂(Measure.infinitePi μ).map (fun g => g (e x))) = _
  rw [Measure.infinitePi_map_eval,hm]

lemma selected_gaussian_score {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (mean : I → ℝ)
    {e : X → I} (he : Measurable e) (m : ℝ) (hm : ∀ x, mean (e x) = m)
    {D : X → ℝ} (hD : Measurable D) :
    (∫ p : X × (I → ℝ), D p.1*p.2 (e p.1) ∂P.prod (Measure.infinitePi (fun i => gaussianReal (mean i) 1))) =
      (∫ x, D x ∂P)*m := by
  have hlaw := selected_coordinate_prod_law P (fun i => gaussianReal (mean i) 1) he
    (gaussianReal m 1) (fun x => by rw [hm x])
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  have hF : Measurable (fun p : X × ℝ => D p.1*p.2) := by fun_prop
  rw [← integral_map hT.aemeasurable hF.aestronglyMeasurable,hlaw,integral_prod_mul D (fun y : ℝ => y),integral_id_gaussianReal]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def cascadeReplicaLaw (n : ℕ) (b : ℕ → ℝ) : Measure (ℕ → LabeledLeaf n) :=
  probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n) ∘ₘ
    (labeledCascadeLaw n b : Measure (LabeledTree n))

instance cascadeReplicaLaw_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (cascadeReplicaLaw n b) :=
  inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ _))

def replicaMarkPath {A : Type} (n : ℕ) (σ : ℕ → NoiseLeaf A n) : ℕ → Fin n → A :=
  fun i => noiseLeafMark n (σ i)

lemma measurable_replicaMarkPath {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (replicaMarkPath (A := A) n) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro d
  exact (measurable_noiseLeafMark n d).comp (measurable_pi_apply i)

def coordinateMarkPath {A : Type} (n : ℕ) (p : (ℕ → LabeledLeaf n) × (ForestVertex n → A)) : ℕ → Fin n → A :=
  fun i d => p.2 (edgeAt n (p.1 i) d)

lemma measurable_coordinateMarkPath {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (coordinateMarkPath (A := A) n) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro d
  have hv : Measurable (fun p : (ForestVertex n → A) × LabeledLeaf n => p.1 (edgeAt n p.2 d)) :=
    measurable_from_prod_countable_left (fun v => measurable_pi_apply (edgeAt n v d))
  exact hv.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

 

theorem marked_path_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    (markedReplicaLaw n b μ).map (replicaMarkPath n) =
      ((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map (coordinateMarkPath n) := by
  let Q := Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod Q
  let K := probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n)
  have hΨ : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) := by
    apply Measurable.of_eval; intro i
    have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n =>
        labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left; intro v
      exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
    exact hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [← labeled_marked_replica_law n b hb μ,Measure.map_map (measurable_replicaMarkPath n) hΨ]
  have he := independent_marks_sampling (labeledCascadeLaw n b : Measure (LabeledTree n)) Q K
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map _ = _
  rw [show (cascadeReplicaLaw n b).prod Q =
    (P ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) from he.symm,
    Measure.map_map (measurable_coordinateMarkPath n) (by fun_prop)]
  congr 1
  funext p i d
  exact noiseLeafMark_labeled n p.1.1 p.1.2 (p.2 i) d

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def retainedLabelLeafLaw (n : ℕ) (b a : ℕ → ℝ) :
    LabeledTree n × (ForestVertex n → ℝ) → Measure (LabeledLeaf n) :=
  labeledWeightedLeafLaw n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2)
    (fun _ _ => PUnit.unit) PUnit.unit

instance retainedLabelLeafLaw_probability (n : ℕ) (b a : ℕ → ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ)) : IsProbabilityMeasure (retainedLabelLeafLaw n b a p) :=
  labeledWeightedLeafLaw_probability _ _ _ _ _

lemma measurable_retainedLabelLeafLaw (n : ℕ) (b a : ℕ → ℝ) :
    Measurable (retainedLabelLeafLaw n b a) :=
  measurable_labeledWeightedLeafLaw n (fun i => by unfold retainedGaussianScale; fun_prop)
    (fun _ => measurable_const) PUnit.unit

def retainedLabelBase (n : ℕ) (b : ℕ → ℝ) : Measure (LabeledTree n × (ForestVertex n → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))

instance retainedLabelBase_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (retainedLabelBase n b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

def retainedLabelJoint (n : ℕ) (b a : ℕ → ℝ) :
    Measure ((LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n)) :=
  retainedLabelBase n b ⊗ₘ probabilityReplicaKernel (retainedLabelLeafLaw n b a)
    (measurable_retainedLabelLeafLaw n b a)

instance retainedLabelJoint_probability (n : ℕ) (b a : ℕ → ℝ) : IsProbabilityMeasure (retainedLabelJoint n b a) :=
  inferInstanceAs (IsProbabilityMeasure (_ ⊗ₘ _))

def sampledMarkPath (n : ℕ) (p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n)) :
    ℕ → Fin n → ℝ := coordinateMarkPath n (p.2,p.1.2)

lemma measurable_sampledMarkPath (n : ℕ) : Measurable (sampledMarkPath n) :=
  (measurable_coordinateMarkPath n).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

 
theorem retained_joint_path_law (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    (retainedLabelJoint n b a).map (sampledMarkPath n) =
      (markedReplicaLaw n b (fun i => ⟨gaussianReal (b i*a i) 1,inferInstance⟩)).map (replicaMarkPath n) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,inferInstance⟩
  let ν : ℕ → ProbabilityMeasure ℝ := fun i => ⟨gaussianReal (b i*a i) 1,inferInstance⟩
  let c := fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2
  let u := fun (_ : ℕ) (_ : PUnit × ℝ) => PUnit.unit
  have hc : ∀ i, Measurable (c i) := fun i => by unfold c retainedGaussianScale; fun_prop
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_const
  have hm : ∀ i s, ∫⁻ x, ENNReal.ofReal (c i (s,x)^b i) ∂(μ i : Measure ℝ) = 1 :=
    fun i _ => retainedGaussianScale_normalized _ _
  have hL := labeled_weighted_marked_replica_law n b hb μ hc hu
    (fun i s x => Real.exp_pos _) hm PUnit.unit
  have hM := noise_mark_replica_transport n b hb μ ν
    (fun i x => retainedGaussianScale (b i) (a i) x)
    (fun i => by unfold retainedGaussianScale; fun_prop) (fun i x => Real.exp_pos _)
    (fun i => (retainedGaussianScale_density _ _).symm)
  have hΨ : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i)) := by
    apply Measurable.of_eval; intro i
    have hψ : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × LabeledLeaf n =>
        labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left; intro v
      exact (measurable_labeledNoiseLeaf ℝ n v).comp (by fun_prop)
    exact hψ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have he := congrArg (fun P : Measure (ℕ → NoiseLeaf ℝ n) => P.map (replicaMarkPath n)) hL
  rw [Measure.map_map (measurable_replicaMarkPath n) hΨ] at he
  have hpath : (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      replicaMarkPath n (fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i))) =
      sampledMarkPath n := by
    funext p i d
    exact noiseLeafMark_labeled n p.1.1 p.1.2 (p.2 i) d
  change (retainedLabelJoint n b a).map _ = _ at he
  change (retainedLabelJoint n b a).map _ = _
  rw [show (replicaMarkPath n ∘ (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
    fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i))) = sampledMarkPath n from hpath] at he
  exact he.trans hM

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma tilted_sub_constant {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (c : ℝ) :
    ν.tilted (fun x => H x-c) = ν.tilted H := by
  have := isProbabilityMeasure_tilted he
  have h := tilted_tilted he (fun _ => -c)
  simpa only [tilted_const,Pi.add_def,sub_eq_add_neg] using h.symm

lemma retainedLabelLeafLaw_single_tilted (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ))
    (he : Integrable (fun v => Real.exp (t*p.2 (edgeAt n v d))) (labeledLeafLaw n p.1)) :
    retainedLabelLeafLaw n b (fun i => if i = d then t else 0) p =
      (labeledLeafLaw n p.1).tilted (fun v => t*p.2 (edgeAt n v d)) := by
  have hW : (fun v => labeledWeight n
      (fun i (q : PUnit × ℝ) => retainedGaussianScale (b i) (if i = d then t else 0) q.2)
      (fun _ _ => PUnit.unit) PUnit.unit (p,v)) =
      (fun v => ENNReal.ofReal (Real.exp (t*p.2 (edgeAt n v d)-b d*t^2/2))) := by
    funext v
    exact noiseLeafProduct_single_level n b d t p.1 p.2 v
  unfold retainedLabelLeafLaw labeledWeightedLeafLaw labeledWeightedMass
  rw [hW]
  have hei : Integrable (fun v => Real.exp (t*p.2 (edgeAt n v d)-b d*t^2/2)) (labeledLeafLaw n p.1) := by
    simpa only [Real.exp_sub] using he.div_const (Real.exp (b d*t^2/2))
  rw [normalizeMass_exp _ _ (measurable_of_countable _) hei,
    tilted_sub_constant _ _ he]

def leafLevelCoefficients (n : ℕ) (d : Fin n) (v : LabeledLeaf n) : ℕ →₀ ℝ :=
  Finsupp.single (edgeGaussianTag n (edgeAt n v d)) 1

lemma leafLevelCoefficients_field (n : ℕ) (d : Fin n) (v : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (leafLevelCoefficients n d v) g = edgeGaussianCoordinates n g (edgeAt n v d) := by
  simp [leafLevelCoefficients,cylinderField,Finsupp.sum_single_index,edgeGaussianCoordinates]

lemma leafLevelCoefficients_bound (n : ℕ) (d : Fin n) (v : LabeledLeaf n) :
    (leafLevelCoefficients n d v).sum (fun _ c => c^2) ≤ 1 := by
  simp [leafLevelCoefficients,Finsupp.sum_single_index]

lemma leafLevelCoefficients_diag (n : ℕ) (d : Fin n) (v : LabeledLeaf n) :
    cylinderCross (leafLevelCoefficients n d v) (leafLevelCoefficients n d v) = 1 := by
  simp [leafLevelCoefficients,cylinderCross_single_left]

lemma leafLevelCoefficients_cross (n : ℕ) (d : Fin n) (v w : LabeledLeaf n) :
    cylinderCross (leafLevelCoefficients n d v) (leafLevelCoefficients n d w) =
      if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then 1 else 0 :=
  labelLevelCoefficients_cross n d (PUnit.unit,v) (PUnit.unit,w)

def rawLeafGibbs (n : ℕ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ℕ → ℝ)) : Measure (LabeledLeaf n) :=
  gibbsProbability (labeledLeafLaw n p.1) (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2)

instance rawLeafGibbs_probability (n : ℕ) (d : Fin n) (t : ℝ) (p : LabeledTree n × (ℕ → ℝ)) :
    IsProbabilityMeasure (rawLeafGibbs n d t p) := gibbsProbability_probability _ _

lemma measurable_rawLeafGibbs (n : ℕ) (d : Fin n) (t : ℝ) : Measurable (rawLeafGibbs n d t) := by
  have hH : Measurable (fun p : (LabeledTree n × (ℕ → ℝ)) × LabeledLeaf n =>
      t*cylinderField (leafLevelCoefficients n d p.2) p.1.2) :=
    ((measurable_cylinderFields (leafLevelCoefficients n d)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).const_mul t
  have hν : Measurable (fun p : LabeledTree n × (ℕ → ℝ) => labeledLeafLaw n p.1) :=
    (measurable_labeledLeafLaw n).comp measurable_fst
  exact measurable_gibbsProbability hν hH

def rawLabelBase (n : ℕ) (b : ℕ → ℝ) : Measure (LabeledTree n × (ℕ → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates

instance rawLabelBase_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (rawLabelBase n b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

def rawLabelJoint (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    Measure ((LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n)) :=
  rawLabelBase n b ⊗ₘ probabilityReplicaKernel (rawLeafGibbs n d t) (measurable_rawLeafGibbs n d t)

instance rawLabelJoint_probability (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    IsProbabilityMeasure (rawLabelJoint n b d t) := inferInstanceAs (IsProbabilityMeasure (_ ⊗ₘ _))

lemma rawLeafGibbs_retained (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ℕ → ℝ))
    (he : Integrable (fun v => Real.exp (t*cylinderField (leafLevelCoefficients n d v) p.2)) (labeledLeafLaw n p.1)) :
    rawLeafGibbs n d t p =
      retainedLabelLeafLaw n b (fun i => if i = d then t else 0) (p.1,edgeGaussianCoordinates n p.2) := by
  have heq : (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) =
      (fun v => t*edgeGaussianCoordinates n p.2 (edgeAt n v d)) := by
    funext v; rw [leafLevelCoefficients_field]
  have he' : Integrable (fun v => Real.exp (t*edgeGaussianCoordinates n p.2 (edgeAt n v d))) (labeledLeafLaw n p.1) := by
    simpa only [leafLevelCoefficients_field] using he
  have hR := retainedLabelLeafLaw_single_tilted n b d t (p.1,edgeGaussianCoordinates n p.2) he'
  have hG : rawLeafGibbs n d t p = (labeledLeafLaw n p.1).tilted
      (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) := gibbsProbability_eq_tilted _ _ he
  exact hG.trans ((congrArg (fun H => (labeledLeafLaw n p.1).tilted H) heq).trans hR.symm)

lemma rawLeafGibbs_retained_ae (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    ∀ᵐ p ∂rawLabelBase n b, rawLeafGibbs n d t p =
      retainedLabelLeafLaw n b (fun i => if i = d then t else 0) (p.1,edgeGaussianCoordinates n p.2) := by
  have ha := random_cylinder_all_exp_ae (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
  exact ha.mono (fun p hp => rawLeafGibbs_retained n b d t p (hp t))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma compProd_base_map {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] (P : Measure Ω) [SFinite P] (Q : Measure Ω') [SFinite Q]
    (K : Kernel Ω X) [IsSFiniteKernel K] (L : Kernel Ω' X) [IsSFiniteKernel L]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    (hK : ∀ᵐ ω ∂P, K ω = L (T ω)) :
    (P ⊗ₘ K).map (fun p => (T p.1,p.2)) = Q ⊗ₘ L := by
  have hS : Measurable (fun p : Ω × X => (T p.1,p.2)) := (hT.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext_of_lintegral
  intro F hF
  have hFS : Measurable (fun p : Ω × X => F (T p.1,p.2)) := hF.comp hS
  rw [lintegral_map hF hS,Measure.lintegral_compProd hFS,
    Measure.lintegral_compProd hF]
  calc
    _ = ∫⁻ ω, ∫⁻ x, F (T ω,x) ∂L (T ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hK] with ω hω
      rw [hω]
    _ = _ := by
      have hI : Measurable (fun ω' => ∫⁻ x, F (ω',x) ∂L ω') :=
        Measurable.lintegral_kernel_prod_right (f := fun ω' x => F (ω',x)) hF
      rw [← lintegral_map hI hT,hPQ]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def rawLabelToRetained (n : ℕ) (p : (LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n)) :
    (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) :=
  ((p.1.1,edgeGaussianCoordinates n p.1.2),p.2)

lemma measurable_rawLabelToRetained (n : ℕ) : Measurable (rawLabelToRetained n) :=
  (measurable_fst.fst.prodMk ((edgeGaussianCoordinates_preserving n).measurable.comp measurable_fst.snd)).prodMk measurable_snd

lemma raw_retained_joint_preserving (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    MeasurePreserving (rawLabelToRetained n) (rawLabelJoint n b d t)
      (retainedLabelJoint n b (fun i => if i = d then t else 0)) := by
  have hp : MeasurePreserving (fun p : LabeledTree n × (ℕ → ℝ) => (p.1,edgeGaussianCoordinates n p.2))
      (rawLabelBase n b) (retainedLabelBase n b) :=
    (MeasurePreserving.id _).prod (edgeGaussianCoordinates_preserving n)
  refine ⟨measurable_rawLabelToRetained n,?_⟩
  apply compProd_base_map _ _ _ _ hp.measurable hp.map_eq
  filter_upwards [rawLeafGibbs_retained_ae n b d t] with p he
  change Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p) =
    Measure.infinitePi (fun _ : ℕ => retainedLabelLeafLaw n b (fun i => if i = d then t else 0)
      (p.1,edgeGaussianCoordinates n p.2))
  rw [he]

lemma rawJoint_integral_reference (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) (r : ℕ)
    (F : (LabeledTree n × (ℕ → ℝ)) → (Fin r → LabeledLeaf n) → ℝ)
    (hi : Integrable (fun p => F p.1 (fun i => p.2 i)) (rawLabelJoint n b d t)) :
    (∫ p, F p.1 (fun i => p.2 i) ∂rawLabelJoint n b d t) =
      ∫ p, referenceReplicaMean (labeledLeafLaw n p.1)
        (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) (F p) ∂rawLabelBase n b := by
  rw [show rawLabelJoint n b d t = rawLabelBase n b ⊗ₘ
    probabilityReplicaKernel (rawLeafGibbs n d t) (measurable_rawLeafGibbs n d t) from rfl,
    Measure.integral_compProd hi]
  have ha := random_cylinder_all_exp_ae (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
  apply integral_congr_ae
  filter_upwards [ha] with p hp
  have he := hp t
  have hg : rawLeafGibbs n d t p = (labeledLeafLaw n p.1).tilted
      (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) := gibbsProbability_eq_tilted _ _ he
  rw [referenceReplicaMean_eq_tilted _ _ he,← hg]
  change (∫ σ, F p (fun i => σ i) ∂Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p)) = _
  have hh := (HasLaw.mk (P := Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p))
    (show AEMeasurable (fun σ : ℕ → LabeledLeaf n => fun i : Fin r => σ i) _ from (by fun_prop : Measurable _).aemeasurable)
    (replica_prefix_map (rawLeafGibbs n d t p) r)).integral_comp
    (measurable_of_countable (F p)).aestronglyMeasurable
  exact hh

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def pathPrefixPattern (n r : ℕ) (z : ℕ → Fin n → ℝ) : PrefixPattern n r :=
  fun i j d => if z i d = z j d then true else false

lemma measurable_pathPrefixPattern (n r : ℕ) : Measurable (pathPrefixPattern n r) := by
  unfold pathPrefixPattern
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  apply Measurable.of_eval; intro d
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply d).comp (measurable_pi_apply (i:ℕ)))
    ((measurable_pi_apply d).comp (measurable_pi_apply (j:ℕ)))

lemma measurable_labelPrefixPattern (n r : ℕ) : Measurable (labelPrefixPattern n r) :=
  measurable_of_countable _

lemma measurable_infiniteLabelPattern (n r : ℕ) :
    Measurable (fun σ : ℕ → LabeledLeaf n => labelPrefixPattern n r (fun i => σ i)) :=
  (measurable_labelPrefixPattern n r).comp (by fun_prop)

lemma pathPrefixPattern_coordinates (n r : ℕ) (σ : ℕ → LabeledLeaf n)
    (g : ForestVertex n → ℝ) (hg : Function.Injective g) :
    pathPrefixPattern n r (coordinateMarkPath n (σ,g)) =
      labelPrefixPattern n r (fun i => σ i) := by
  funext i j d
  unfold pathPrefixPattern coordinateMarkPath labelPrefixPattern
  simp only [hg.eq_iff,edgeAt_eq_iff_prefix]

def gaussianMarkedPathLaw (n : ℕ) (b m : ℕ → ℝ) : Measure (ℕ → Fin n → ℝ) :=
  (markedReplicaLaw n b (fun i => ⟨gaussianReal (m i) 1,inferInstance⟩)).map (replicaMarkPath n)

lemma gaussianMarkedPathLaw_eq (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (m : ℕ → ℝ) :
    gaussianMarkedPathLaw n b m =
      ((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))).map (coordinateMarkPath n) :=
  marked_path_law n b hb _

lemma path_shape_ae_coordinates (n r : ℕ) (b m : ℕ → ℝ) :
    ∀ᵐ p ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)),
      pathPrefixPattern n r (coordinateMarkPath n p) = labelPrefixPattern n r (fun i => p.1 i) := by
  have ha := gaussian_marks_injective n m
  have hp := measurePreserving_snd (μ := cascadeReplicaLaw n b)
    (ν := Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually ha] with p hp
  exact pathPrefixPattern_coordinates n r p.1 p.2 hp

 
theorem gaussian_marked_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ z, D (pathPrefixPattern n r z) ∂gaussianMarkedPathLaw n b m) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hD := measurable_of_countable D
  have hF : Measurable (fun z => D (pathPrefixPattern n r z)) := hD.comp (measurable_pathPrefixPattern n r)
  rw [gaussianMarkedPathLaw_eq n b hb m,
    integral_map (measurable_coordinateMarkPath n).aemeasurable hF.aestronglyMeasurable]
  calc
    _ = ∫ p, D (labelPrefixPattern n r (fun i => p.1 i))
        ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
          (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)) :=
      integral_congr_ae ((path_shape_ae_coordinates n r b m).mono (fun _ h => congrArg D h))
    _ = _ := by
      simpa using integral_fun_fst (μ := cascadeReplicaLaw n b)
        (ν := Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))
        (fun σ => D (labelPrefixPattern n r (fun i => σ i)))

 

theorem gaussian_marked_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    (∫ z, D (pathPrefixPattern n r z)*z 0 d ∂gaussianMarkedPathLaw n b m) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*m d := by
  have hD := measurable_of_countable D
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    (hD.comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  rw [gaussianMarkedPathLaw_eq n b hb m,
    integral_map (measurable_coordinateMarkPath n).aemeasurable hF.aestronglyMeasurable]
  calc
    _ = ∫ p, D (labelPrefixPattern n r (fun i => p.1 i))*p.2 (edgeAt n (p.1 0) d)
        ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
          (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)) := by
      apply integral_congr_ae
      filter_upwards [path_shape_ae_coordinates n r b m] with p hp
      rw [hp]; rfl
    _ = _ := by
      let : MeasurableSpace (ForestVertex n) := ⊤
      let : MeasurableSingletonClass (ForestVertex n) := ⟨fun _ => MeasurableSet.of_discrete⟩
      exact selected_gaussian_score (cascadeReplicaLaw n b) (fun v => m (forestVertexDepth n v))
        ((measurable_of_countable (fun v : LabeledLeaf n => edgeAt n v d)).comp (measurable_pi_apply 0))
        (m d) (fun σ => by simp only [Function.comp_apply,forestVertexDepth_edgeAt])
        (hD.comp (measurable_infiniteLabelPattern n r))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma selected_gaussian_score_integrable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (mean : I → ℝ)
    {e : X → I} (he : Measurable e) (m : ℝ) (hm : ∀ x, mean (e x) = m)
    {D : X → ℝ} (hD : Measurable D) (hi : Integrable D P) :
    Integrable (fun p : X × (I → ℝ) => D p.1*p.2 (e p.1))
      (P.prod (Measure.infinitePi (fun i => gaussianReal (mean i) 1))) := by
  have hlaw := selected_coordinate_prod_law P (fun i => gaussianReal (mean i) 1) he
    (gaussianReal m 1) (fun x => by rw [hm x])
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  have hF : Measurable (fun p : X × ℝ => D p.1*p.2) := by fun_prop
  have hG : Integrable (fun x : ℝ => x) (gaussianReal m 1) :=
    (memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable (by norm_num)
  have hiF : Integrable (fun p : X × ℝ => D p.1*p.2) (P.prod (gaussianReal m 1)) := hi.mul_prod hG
  rw [← hlaw] at hiF
  exact (integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable).mp hiF

lemma gaussian_marked_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) {c : ℝ} (hD : ∀ x, |D x| ≤ c) :
    Integrable (fun z => D (pathPrefixPattern n r z)*z 0 d) (gaussianMarkedPathLaw n b m) := by
  have hDm := measurable_of_countable D
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    (hDm.comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  rw [gaussianMarkedPathLaw_eq n b hb m]
  apply (integrable_map_measure hF.aestronglyMeasurable (measurable_coordinateMarkPath n).aemeasurable).mpr
  let : MeasurableSpace (ForestVertex n) := ⊤
  let : MeasurableSingletonClass (ForestVertex n) := ⟨fun _ => MeasurableSet.of_discrete⟩
  have hiD : Integrable (fun σ : ℕ → LabeledLeaf n => D (labelPrefixPattern n r (fun i => σ i)))
      (cascadeReplicaLaw n b) :=
    integrable_of_measurable_abs_le (hDm.comp (measurable_infiniteLabelPattern n r)) (fun _ => hD _)
  have hi := selected_gaussian_score_integrable (cascadeReplicaLaw n b)
    (fun v => m (forestVertexDepth n v))
    ((measurable_of_countable (fun v : LabeledLeaf n => edgeAt n v d)).comp (measurable_pi_apply 0))
    (m d) (fun σ => by simp only [Function.comp_apply,forestVertexDepth_edgeAt])
    (hDm.comp (measurable_infiniteLabelPattern n r)) hiD
  apply hi.congr
  filter_upwards [path_shape_ae_coordinates n r b m] with p hp
  change D (labelPrefixPattern n r (fun i => p.1 i))*p.2 (edgeAt n (p.1 0) d) = _
  rw [← hp]; rfl

end IsingPerceptron

end

end OAI
