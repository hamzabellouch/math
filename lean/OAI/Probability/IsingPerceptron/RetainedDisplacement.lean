import Mathlib
import OAI.Probability.IsingPerceptron.EnergyShift

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
lemma map_powerIntensity_retained {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    {T : B → C} (hT : Measurable T) (hLaw : P.map T = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2.2))) =
      (powerIntensity b).prod ((μ.withDensity (fun a => ENNReal.ofReal (c a ^ b))).prod Q) := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1*p.1,(p.2.1,T p.2.2))) := by fun_prop
  have hw : Measurable (fun a => ENNReal.ofReal (c a ^ b)) := (hc.pow_const b).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF,lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,(p.2.1,T p.2.2))) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,(a,T v)) ∂P) = ∫⁻ w, f (c a*x,(a,w)) ∂Q := by
    rw [← hLaw,lintegral_map]
    · fun_prop
    · exact hT
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,(v.1,T v.2)) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,(a,w)) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,(v.1,T v.2)))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,(p.2,w)) ∂Q) :=
    (hf.comp (by fun_prop : Measurable (fun p : (ℝ × A) × C => (c p.1.2*p.1.1,(p.1.2,p.2))))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,(a,w)) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b) := by
    have hfa : Measurable (fun x : ℝ => ∫⁻ w, f (x,(a,w)) ∂Q) :=
      (hf.comp (by fun_prop : Measurable (fun z : ℝ × C => (z.1,(a,z.2))))).lintegral_prod_right'
    rw [← lintegral_map hfa (measurable_const_mul (c a)),map_powerIntensity_mul (hcpos a),lintegral_smul_measure]
    rfl
  simp_rw [hx]
  have hga : Measurable (fun a : A => ∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b) :=
    ((hf.comp (by fun_prop : Measurable (fun z : (A × ℝ) × C => (z.1.2,(z.1.1,z.2))))).lintegral_prod_right').lintegral_prod_right'
  calc
    _ = ∫⁻ a, ∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b
        ∂μ.withDensity (fun a => ENNReal.ofReal (c a ^ b)) :=
      (lintegral_withDensity_eq_lintegral_mul μ hw hga).symm
    _ = _ := by
      rw [lintegral_lintegral_swap]
      · rw [lintegral_prod _ hf.aemeasurable]
        congr 1; funext x
        exact (lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
      · exact ((hf.comp (by fun_prop : Measurable (fun z : (A × ℝ) × C => (z.1.2,(z.1.1,z.2))))).lintegral_prod_right').aemeasurable

 

theorem noiseTreeKeep_independent_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ ν : ℕ → ProbabilityMeasure A) (c : ℕ → A → ℝ)
    (hc : ∀ i, Measurable (c i)) (hcpos : ∀ i a, 0 < c i a)
    (hν : ∀ i, (ν i : Measure A) = (μ i : Measure A).withDensity (fun a => ENNReal.ofReal (c i a ^ b i))) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map
      (noiseTreeKeep n b μ (fun i (p : PUnit × A) => c i p.2) (fun _ _ => PUnit.unit) PUnit.unit) =
      noiseCascadeLaw A n b ν := by
  induction n generalizing b μ ν c with
  | zero => exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let μ' := fun i => μ (i+1)
    let ν' := fun i => ν (i+1)
    let b' := fun i => b (i+1)
    let c' := fun i => c (i+1)
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let Q : Measure (NoiseTree A n) := noiseCascadeLaw A n b' ν'
    let T := noiseTreeKeep n b' μ' (fun i (p : PUnit × A) => c' i p.2) (fun _ _ => PUnit.unit) PUnit.unit
    have hT : Measurable T := (measurable_noiseTreeKeep n b' μ' (fun i => (hc (i+1)).comp measurable_snd)
      (fun _ => measurable_const)).comp (measurable_const.prodMk measurable_id)
    have hLaw : P.map T = Q := ih b' μ' ν' c' (fun i => hc (i+1)) (fun i => hcpos (i+1)) (fun i => hν (i+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) := fun p => (c 0 p.2.1*p.1,(p.2.1,T p.2.2))
    have hG : Measurable G := by fun_prop
    have hI : I.map G = (powerIntensity (b 0)).prod ((ν 0 : Measure A).prod Q) := by
      rw [hν 0]
      exact map_powerIntensity_retained (b 0) (μ 0 : Measure A) P Q (hc 0) (hcpos 0) hT hLaw
    rw [noiseCascadeLaw_succ,noiseCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod ((ν 0 : Measure A).prod Q))
    calc
      _ = (poissonLaw I).map (fun V => V.map G) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with V hV
        change (sigmaPart I V).map G = V.map G
        rw [hV]
      _ = poissonLaw (I.map G) := poissonLaw_map I hG
      _ = _ := poissonLaw_congr hI

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_probability_pi {Ω I X : Type*} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace X] {ν : Ω → Measure X} (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : Measurable (fun ω => Measure.pi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.pi (fun _ : I => ν ω)) s))
    _root_.generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]; exact measurable_const
  · rintro s ⟨t,ht,rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (ht i (mem_univ _))).comp hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) sᶜ = 1-(Measure.pi (fun _ : I => ν ω)) s := by
      rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]; exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.pi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]; exact Measurable.tsum ih

lemma measurable_probability_infinitePi {Ω I X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {ν : Ω → Measure X} (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : Measurable (fun ω => Measure.infinitePi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.infinitePi (fun _ : I => ν ω)) s))
    (s := measurableCylinders (fun _ : I => X))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]; exact measurable_const
  · intro s hs
    obtain ⟨J,S,hS,rfl⟩ := (mem_measurableCylinders s).mp hs
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (cylinder J S) =
        (Measure.pi (fun _ : J => ν ω)) S := Measure.infinitePi_cylinder _ hS
    simp_rw [he]
    exact (Measure.measurable_coe hS).comp (measurable_probability_pi hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) sᶜ =
        1-(Measure.infinitePi (fun _ : I => ν ω)) s := by rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]; exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.infinitePi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]; exact Measurable.tsum ih

def probabilityReplicaKernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Kernel Ω (ℕ → X) :=
  ⟨fun ω => Measure.infinitePi (fun _ : ℕ => ν ω),measurable_probability_infinitePi hν⟩

instance probabilityReplicaKernel_markov {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsMarkovKernel (probabilityReplicaKernel ν hν) := by
  constructor
  intro ω
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => ν ω))
  infer_instance

def markedReplicaLaw {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) : Measure (ℕ → NoiseLeaf A n) :=
  probabilityReplicaKernel (noiseLeafKernel A n) (noiseLeafKernel A n).measurable ∘ₘ
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))

instance markedReplicaLaw_probability {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) : IsProbabilityMeasure (markedReplicaLaw n b μ) :=
  inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ _))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {A : Type} [MeasurableSpace A]

def noiseLeafMark : (n : ℕ) → NoiseLeaf A n → Fin n → A
  | 0, _, i => i.elim0
  | n+1, v, i => Fin.cases v.2.1 (noiseLeafMark n v.2.2) i

lemma measurable_noiseLeafMark (n : ℕ) (i : Fin n) : Measurable (fun v : NoiseLeaf A n => noiseLeafMark n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst.comp measurable_snd
    · exact (ih j).comp (measurable_snd.comp measurable_snd)

omit [MeasurableSpace A] in
lemma noiseLeafMark_keep {S : Type} (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) (i : Fin n) :
    noiseLeafMark n (noiseLeafKeep n c u s v) i = noiseLeafMark n v i := by
  induction n generalizing c u s with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih _ _ _ _ j

lemma noiseLeafMark_labeled (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (v : LabeledLeaf n) (i : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) i = g (edgeAt n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [noiseLeafMark,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_zero]
    · simpa only [noiseLeafMark,Fin.cases_succ,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_succ] using
        ih (ω.2 v.1.1 v.1.2) (fun w => g (v.1.1,v.1.2,some w)) v.2 j

lemma edgeAt_eq_iff_prefix (n : ℕ) (v w : LabeledLeaf n) (d : Fin n) :
    edgeAt n v d = edgeAt n w d ↔ (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) := by
  rw [← Option.some_inj,← (nodeAddress_injective n).eq_iff,← nodeAt_succ,← nodeAt_succ,
    nodeAddress_nodeAt,nodeAddress_nodeAt]
  rfl

lemma noiseLeafMark_eq_iff_prefix (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (hg : Function.Injective g) (v w : LabeledLeaf n) (d : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) d =
      noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) w) d ↔
      (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) := by
  rw [noiseLeafMark_labeled,noiseLeafMark_labeled,hg.eq_iff,edgeAt_eq_iff_prefix]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma sampling_replica_morphism {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure Y} (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {ψ : Ω → X → Y} (hψ : Measurable (fun p : Ω × X => ψ p.1 p.2))
    (h : ∀ᵐ ω ∂P, (ν ω).map (ψ ω) = κ (T ω)) :
    (P ⊗ₘ probabilityReplicaKernel ν hν).map (fun p i => ψ p.1 (p.2 i)) =
      probabilityReplicaKernel κ hκ ∘ₘ Q := by
  have hΨ : Measurable (fun p : Ω × (ℕ → X) => fun i => ψ p.1 (p.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hψ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hΨ,Measure.lintegral_compProd
    (show Measurable (fun p : Ω × (ℕ → X) => F (fun i => ψ p.1 (p.2 i))) from hF.comp hΨ)]
  have he : (∫⁻ ω, ∫⁻ σ, F (fun i => ψ ω (σ i)) ∂(probabilityReplicaKernel ν hν) ω ∂P) =
      ∫⁻ ω, ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) (T ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [h] with ω hω
    change (∫⁻ σ, F (fun i => ψ ω (σ i)) ∂Measure.infinitePi (fun _ : ℕ => ν ω)) =
      ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => κ (T ω))
    have hψω : Measurable (ψ ω) := hψ.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hF (by fun_prop : Measurable (fun σ : ℕ → X => fun i => ψ ω (σ i))),
      Measure.infinitePi_map_pi _ (fun _ => hψω)]
    simp only [hω]
  rw [he]
  have hI : Measurable (fun ω => ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) ω) := hF.lintegral_kernel
  rw [← lintegral_map hI hT,hPQ]
  change _ = ∫⁻ σ, F σ ∂Q.bind (probabilityReplicaKernel κ hκ)
  exact (Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable).symm

 

theorem labeled_marked_replica_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
    (P ⊗ₘ probabilityReplicaKernel (fun p => labeledLeafLaw n p.1)
      ((measurable_labeledLeafLaw n).comp measurable_fst)).map
      (fun p i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) =
      markedReplicaLaw n b μ := by
  intro P
  let T := fun p : LabeledTree n × (ForestVertex n → A) =>
    labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : P.map T = (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) :=
    labeledNoiseCoordinates_law A n b μ
  have hp : MeasurePreserving T P (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism P _ (ν := fun p : LabeledTree n × (ForestVertex n → A) => labeledLeafLaw n p.1)
    (κ := noiseLeafKernel A n) ((measurable_labeledLeafLaw n).comp measurable_fst)
    (noiseLeafKernel A n).measurable hT hPQ
    (ψ := fun p v => labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2) v)
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
  · filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good A n b hb μ)] with p hp
    apply labeledLeafLaw_noiseMap A n p.1 (markForestOfCoords A n p.2) hp
    cases n with
    | zero => simp [noiseTreeTotal,rawTreeTotal]
    | succ n => exact hp.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

lemma normalizeMass_weight_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (ν : Measure X) {ψ : X → Y} (hψ : Measurable ψ)
    {w : Y → ℝ≥0∞} (hw : Measurable w)
    (hm : 0 < ((ν.map ψ).withDensity w) univ ∧ ((ν.map ψ).withDensity w) univ < ∞) :
    (normalizeMass (ν.withDensity (fun x => w (ψ x)))).map ψ =
      normalizeMass ((ν.map ψ).withDensity w) := by
  have he := withDensity_map_pullback ν hψ hw
  have hmass : (ν.withDensity (fun x => w (ψ x))) univ = ((ν.map ψ).withDensity w) univ := by
    rw [← he,Measure.map_apply hψ MeasurableSet.univ]; rfl
  rw [normalizeMass_map _ hψ (by simpa only [hmass] using hm),he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma kernel_comap_comp_measure {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] (P : Measure Ω) (K : Kernel Ω' X) {T : Ω → Ω'} (hT : Measurable T) :
    K.comap T hT ∘ₘ P = K ∘ₘ P.map T := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),Measure.bind_apply hs K.aemeasurable,
    lintegral_map (K.measurable_coe hs) hT]
  rfl

lemma replica_mark_transport {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure X} (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {ψ : X → Y} (hψ : Measurable ψ)
    (h : ∀ᵐ ω ∂P, (ν ω).map ψ = (κ (T ω)).map ψ) :
    ((probabilityReplicaKernel ν hν) ∘ₘ P).map (fun σ i => ψ (σ i)) =
      ((probabilityReplicaKernel κ hκ) ∘ₘ Q).map (fun σ i => ψ (σ i)) := by
  let K := (probabilityReplicaKernel κ hκ).map (fun σ i => ψ (σ i))
  have hΨ : Measurable (fun σ : ℕ → X => fun i => ψ (σ i)) := by fun_prop
  rw [Measure.map_comp _ _ hΨ,Measure.map_comp _ _ hΨ]
  calc
    _ = K.comap T hT ∘ₘ P := by
      apply Measure.comp_congr
      filter_upwards [h] with ω hω
      simp only [Kernel.map_apply _ hΨ,Kernel.comap_apply,probabilityReplicaKernel,K]
      change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => ψ (σ i)) =
        (Measure.infinitePi (fun _ : ℕ => κ (T ω))).map (fun σ i => ψ (σ i))
      rw [Measure.infinitePi_map_pi _ (fun _ => hψ),Measure.infinitePi_map_pi _ (fun _ => hψ)]
      simp only [hω]
    _ = K ∘ₘ Q := by rw [kernel_comap_comp_measure,hPQ]

lemma measurable_noiseTiltedLeafLaw {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    [Nonempty A] (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (noiseTiltedLeafLaw n c u s) :=
  measurable_normalizeMass.comp ((measurable_withDensity_fixed
    ((measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id))).comp
    (noiseLeafKernel A n).measurable)

 

theorem noise_mark_replica_transport {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ ν : ℕ → ProbabilityMeasure A)
    (c : ℕ → A → ℝ) (hc : ∀ i, Measurable (c i)) (hcpos : ∀ i a, 0 < c i a)
    (hν : ∀ i, (ν i : Measure A) = (μ i : Measure A).withDensity (fun a => ENNReal.ofReal (c i a ^ b i))) :
    ((probabilityReplicaKernel
      (noiseTiltedLeafLaw n (fun i (p : PUnit × A) => c i p.2) (fun _ _ => PUnit.unit) PUnit.unit)
      (measurable_noiseTiltedLeafLaw n (fun i => (hc i).comp measurable_snd) (fun _ => measurable_const) PUnit.unit)) ∘ₘ
      (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))).map
      (fun σ i => noiseLeafMark n (σ i)) =
      (markedReplicaLaw n b ν).map (fun σ i => noiseLeafMark n (σ i)) := by
  let c' := fun i (p : PUnit × A) => c i p.2
  let u := fun (_ : ℕ) (_ : PUnit × A) => PUnit.unit
  let T := noiseTreeKeep n b μ c' u PUnit.unit
  let ψ := noiseLeafMark (A := A) n
  have hc' : ∀ i, Measurable (c' i) := fun i => (hc i).comp measurable_snd
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_const
  have hT : Measurable T := (measurable_noiseTreeKeep n b μ hc' hu).comp (measurable_const.prodMk measurable_id)
  have hψ : Measurable ψ := Measurable.of_eval (measurable_noiseLeafMark n)
  have hm (i : ℕ) (s : PUnit) : ∫⁻ a, ENNReal.ofReal (c' i (s,a)^b i) ∂(μ i : Measure A) = 1 := by
    have he := congrArg (fun P : Measure A => P univ) (hν i)
    simpa only [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,measure_univ] using he.symm
  apply replica_mark_transport _ _ (measurable_noiseTiltedLeafLaw n hc' hu PUnit.unit)
    (noiseLeafKernel A n).measurable hT (noiseTreeKeep_independent_law n b μ ν c hc hcpos hν) hψ
  filter_upwards [noiseGibbsRegular_ae n b hb μ hc' hu (fun i _ a => hcpos i a) hm PUnit.unit] with ω hω
  have he := noiseTiltedLeafLaw_keep n b μ hc' hu (fun i _ a => hcpos i a) PUnit.unit ω hω
  have hk : Measurable (noiseLeafKeep n c' u PUnit.unit) :=
    (measurable_noiseLeafKeep n hc' hu).comp (measurable_const.prodMk measurable_id)
  rw [← he,Measure.map_map hψ hk]
  congr 1
  funext v i
  exact (noiseLeafMark_keep n c' u PUnit.unit v i).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_random_withDensity {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {W : Ω × X → ℝ≥0∞} (hW : Measurable W) :
    Measurable (fun ω => (ν ω).withDensity (fun x => W (ω,x))) := by
  let K : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel K := ⟨fun _ => inferInstance⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [withDensity_apply _ hs,← lintegral_indicator hs]
  exact (hW.indicator (hs.preimage measurable_snd)).lintegral_kernel_prod_right' (κ := K)

lemma regular_product_mass {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]
    {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    0 < ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)) univ ∧
      ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)) univ < ∞ := by
  let m := (noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  have he : (noiseTreeTotal A n ν • m).map (noiseLeafKeep n c u s) =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := noiseWeightedLeafMeasure_eq n b μ hc hu hcpos s ν hν
    unfold noiseWeightedLeafMeasure at hh
    change Measure.map (noiseLeafKeep n c u s)
      ((noiseLeafKernel A n ν).withDensity (noiseTreeTotal A n ν • noiseLeafProduct n c u s)) = _ at hh
    rwa [withDensity_smul _ hp] at hh
  have hm : noiseTreeTotal A n ν * m univ = noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf A n) => η univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m univ := by
    by_contra hh
    have hz : m univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz,mul_zero] at hm
    exact hν.masses.2.1.ne' hm.symm
  refine ⟨hm0,?_⟩
  have hlt : noiseTreeTotal A n ν * m univ < ∞ := hm ▸ hν.masses.2.2
  rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
  · exact h.2
  · exact (hν.masses.1.1.ne' h).elim
  · exact (hm0.ne' h).elim

def labeledWeight {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n) : ℝ≥0∞ :=
  noiseLeafProduct n c u s (labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) p.2)

def labeledWeightedMass {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : Measure (LabeledLeaf n) :=
  (labeledLeafLaw n p.1).withDensity (fun v => labeledWeight n c u s (p,v))

def labeledWeightedLeafLaw {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : Measure (LabeledLeaf n) :=
  normalizeMass (labeledWeightedMass n c u s p)

instance labeledWeightedLeafLaw_probability {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : IsProbabilityMeasure (labeledWeightedLeafLaw n c u s p) :=
  normalizeMass_probability _

lemma measurable_labeledWeight {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeight (A := A) n c u s) := by
  apply measurable_from_prod_countable_left
  intro v
  exact (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk
    ((measurable_labeledNoiseLeaf A n v).comp (by fun_prop)))

lemma measurable_labeledWeightedMass {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeightedMass (A := A) n c u s) := by
  have hν : Measurable (fun p : LabeledTree n × (ForestVertex n → A) => labeledLeafLaw n p.1) :=
    (measurable_labeledLeafLaw n).comp measurable_fst
  exact measurable_random_withDensity hν (measurable_labeledWeight n hc hu s)

lemma measurable_labeledWeightedLeafLaw {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeightedLeafLaw (A := A) n c u s) :=
  measurable_normalizeMass.comp (measurable_labeledWeightedMass n hc hu s)

 

theorem labeled_weighted_marked_replica_law {A S : Type} [MeasurableSpace A]
    [MeasurableSpace S] [Nonempty A] (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, ∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A) = 1) (s : S) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
    (P ⊗ₘ probabilityReplicaKernel (labeledWeightedLeafLaw n c u s)
      (measurable_labeledWeightedLeafLaw n hc hu s)).map
      (fun p i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) =
      probabilityReplicaKernel (noiseTiltedLeafLaw n c u s)
        (measurable_noiseTiltedLeafLaw n hc hu s) ∘ₘ (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := by
  intro P
  let T := fun p : LabeledTree n × (ForestVertex n → A) =>
    labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : P.map T = (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) :=
    labeledNoiseCoordinates_law A n b μ
  have hp : MeasurePreserving T P (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism P _ (measurable_labeledWeightedLeafLaw n hc hu s)
    (measurable_noiseTiltedLeafLaw n hc hu s) hT hPQ
    (ψ := fun p v => labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2) v)
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
  · filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good A n b hb μ),
      hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseGibbsRegular_ae n b hb μ hc hu hcpos hm s)] with p hg hr
    have hleaf := labeledLeafLaw_noiseMap A n p.1 (markForestOfCoords A n p.2) hg hr.masses.1
    have hw : Measurable (noiseLeafProduct n c u s) :=
      (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
    have he := normalizeMass_weight_map (labeledLeafLaw n p.1)
      (measurable_of_countable (labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2))) hw
      (by rw [hleaf]; exact regular_product_mass hc hu hcpos hr)
    simpa only [hleaf,labeledWeightedLeafLaw,labeledWeightedMass,labeledWeight,noiseTiltedLeafLaw] using he

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianReal_shift_density (m : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (Real.exp (m*x-m^2/2))) =
      gaussianReal m 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul volume (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext x
  dsimp only [Pi.mul_apply,gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,mul_assoc,← Real.exp_add]
  congr 2
  ring

def retainedGaussianScale (b a x : ℝ) : ℝ := Real.exp (a*x-b*a^2/2)

lemma retainedGaussianScale_density (b a : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (retainedGaussianScale b a x ^ b)) =
      gaussianReal (b*a) 1 := by
  convert gaussianReal_shift_density (b*a) using 1
  congr 1; funext x
  rw [retainedGaussianScale,← Real.exp_mul]
  congr 2
  ring

lemma retainedGaussianScale_normalized (b a : ℝ) :
    (∫⁻ x, ENNReal.ofReal (retainedGaussianScale b a x ^ b) ∂gaussianReal 0 1) = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (retainedGaussianScale_density b a)
  simpa only [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,measure_univ] using h

 

theorem noiseTreeKeep_gaussian_law (n : ℕ) (b a : ℕ → ℝ) :
    (noiseCascadeLaw ℝ n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩) : Measure (NoiseTree ℝ n)).map
      (noiseTreeKeep n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩)
        (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2)
        (fun _ _ => PUnit.unit) PUnit.unit) =
      noiseCascadeLaw ℝ n b (fun i => ⟨gaussianReal (b i*a i) 1,inferInstance⟩) := by
  apply noiseTreeKeep_independent_law
  · intro i; unfold retainedGaussianScale; fun_prop
  · intro i x; exact Real.exp_pos _
  · intro i; exact (retainedGaussianScale_density _ _).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma independent_atomless_injective {I : Type*} [Countable I]
    (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] :
    ∀ᵐ g ∂Measure.infinitePi μ, Function.Injective g := by
  change ∀ᵐ g ∂Measure.infinitePi μ, ∀ i j, g i=g j → i=j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i=j
  · subst j; exact ae_of_all _ (fun _ _ => rfl)
  have hp : MeasurePreserving (fun g : I → ℝ => (g i,g j)) (Measure.infinitePi μ) ((μ i).prod (μ j)) :=
    ⟨by fun_prop,Measure.infinitePi_map_eval_prod hij⟩
  have ha : ∀ᵐ p : ℝ × ℝ ∂(μ i).prod (μ j), p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact ae_of_all _ (fun x => by simp only [ae_iff]; simp)
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually ha] with g hg
  exact fun h => (hg h).elim

lemma gaussian_marks_injective (n : ℕ) (m : ℕ → ℝ) :
    ∀ᵐ g ∂Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1),
      Function.Injective g := by
  let (v : ForestVertex n) : NullSingletonClass (gaussianReal (m (forestVertexDepth n v)) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  exact independent_atomless_injective _

end IsingPerceptron

end

end OAI
