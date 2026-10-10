import Mathlib
import OAI.Probability.IsingPerceptron.WeightedPartitionNumeratorIncrement

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTreeKeep : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → NoiseTree A n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n+1, b, μ, c, u, s, ν =>
    (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν).map
      (fun p => (c 0 (s,p.2.1)*p.1, (p.2.1,
        noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)))

lemma measurable_noiseTreeKeep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeKeep n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeKeep
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1, (p.2.2.1,
          noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)))
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
          (ℝ × (A × NoiseTree A n)) => p.2.2.1)).prodMk
        ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

lemma noiseTreeKeep_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeForget A n (noiseTreeKeep n b μ c u s ν) = noiseTreeDisplace n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeKeep noiseTreeForget noiseTreeDisplace
    rw [Measure.map_map]
    · congr 1
      funext p
      dsimp only [Function.comp_apply]
      rw [ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))]
    · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (by fun_prop))
    · exact (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul
          measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_keep_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    {T : A × B → C} (hT : Measurable T) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2))) =
      (powerIntensity b).prod
        (((μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b))).map (fun p => (p.1,T p))) := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2))) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (hT.comp measurable_snd))
  have hD : Measurable (fun p : A × B => ENNReal.ofReal (c p.1^b)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF]
  rw [lintegral_prod_symm _ (show Measurable (fun p : ℝ × (A × B) =>
    f (c p.2.1*p.1,(p.2.1,T p.2))) from hf.comp hF).aemeasurable]
  have hx (p : A × B) : (∫⁻ x, f (c p.1*x,(p.1,T p)) ∂powerIntensity b) =
      ENNReal.ofReal (c p.1^b) * ∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b := by
    calc
      _ = ∫⁻ x, f (x,(p.1,T p)) ∂(powerIntensity b).map (fun x => c p.1*x) :=
        (lintegral_map (hf.comp (measurable_id.prodMk measurable_const))
          (measurable_const_mul (c p.1))).symm
      _ = _ := by
        rw [map_powerIntensity_mul (hcpos p.1), lintegral_smul_measure]
        rfl
  simp_rw [hx]
  have hg : Measurable (fun p : A × B => ∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b) := by
    have hh : Measurable (fun p : (A × B) × ℝ => f (p.2,(p.1.1,T p.1))) :=
      hf.comp (measurable_snd.prodMk
        ((measurable_fst.comp measurable_fst).prodMk (hT.comp measurable_fst)))
    exact hh.lintegral_prod_right'
  calc
    _ = ∫⁻ p, (∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b)
        ∂(μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b)) :=
      (lintegral_withDensity_eq_lintegral_mul _ hD hg).symm
    _ = ∫⁻ p, (∫⁻ x, f (x,p) ∂powerIntensity b)
        ∂(((μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b))).map
          (fun p => (p.1,T p))) :=
      (lintegral_map hf.lintegral_prod_left' (measurable_fst.prodMk hT)).symm
    _ = _ := (lintegral_prod_symm _ hf.aemeasurable).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeKeep_law_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) :
    let P := (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n))
    let G := fun p : A × NoiseTree A n => (p.1,
      noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2)
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))).map
      (noiseTreeKeep (n+1) b μ c u s) =
      poissonLaw ((powerIntensity (b 0)).prod
        ((((μ 0 : Measure A).prod P).withDensity (fun p => ENNReal.ofReal (c 0 (s,p.1)^b 0))).map G)) := by
  dsimp only
  let P := (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n))
  let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
  let T : A × NoiseTree A n → NoiseTree A n := fun p =>
    noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
      (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
  have hT : Measurable T :=
    (measurable_noiseTreeKeep n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  let G : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) :=
    fun p => (c 0 (s,p.2.1)*p.1,(p.2.1,T p.2))
  have hG : Measurable G :=
    (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
      measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (hT.comp measurable_snd))
  rw [noiseCascadeLaw_succ]
  calc
    _ = (poissonLaw I).map (fun ν => ν.map G) := by
      apply Measure.map_congr
      filter_upwards [sigmaPart_eq_ae I] with ν hν
      change (sigmaPart I ν).map G = ν.map G
      rw [hν]
    _ = poissonLaw (I.map G) := poissonLaw_map I hG
    _ = _ := by
      apply poissonLaw_congr
      exact map_powerIntensity_keep_subtree (b 0) (μ 0 : Measure A) P
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) hT

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_measure_ae {E : Type*} [MeasurableSpace E] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) : MeasurableSet {ν : Measure E | ∀ᵐ x ∂ν, p x} := by
  simp only [ae_iff]
  exact measurableSet_eq_fun (Measure.measurable_coe hp.compl) measurable_const

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul _ hf.aemeasurable]

lemma withDensity_map_pullback {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure E) {f : E → F} (hf : Measurable f) {w : F → ℝ≥0∞} (hw : Measurable w) :
    (ν.withDensity (fun x => w (f x))).map f = (ν.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    _ = ∫⁻ x, g (f x) ∂ν.withDensity (fun x => w (f x)) :=
      lintegral_map' hg.aemeasurable hf.aemeasurable
    _ = ∫⁻ x, w (f x) * g (f x) ∂ν :=
      lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf) (hg.comp hf)
    _ = ∫⁻ x, w x * g x ∂ν.map f :=
      (lintegral_map' (hw.mul hg).aemeasurable hf.aemeasurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hw hg).symm

variable (A : Type) [MeasurableSpace A] [Nonempty A]

def GoodNoiseTree : (n : ℕ) → NoiseTree A n → Prop
  | 0, _ => True
  | n+1, ν => (0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞) ∧
      ∀ᵐ p ∂ν, GoodNoiseTree n p.2.2

omit [Nonempty A] in
lemma measurableSet_GoodNoiseTree (n : ℕ) : MeasurableSet {ν | GoodNoiseTree A n ν} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    exact ((measurableSet_lt measurable_const (measurable_noiseTreeTotal A (n+1))).inter
      (measurableSet_lt (measurable_noiseTreeTotal A (n+1)) measurable_const)).inter
        (measurable_measure_ae (ih.preimage (measurable_snd.comp measurable_snd)))

lemma noiseCascade_good (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), GoodNoiseTree A n ν := by
  induction n generalizing b μ with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    have htot : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞ := by
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        (measurable_noiseTreeForget A (n+1)).aemeasurable
      rw [noiseCascadeLaw_forget]
      exact (rawCascade_total_moments (n+1) b hb).1
    have hm : MeasurableSet {p : ℝ × (A × NoiseTree A n) | GoodNoiseTree A n p.2.2} :=
      (measurableSet_GoodNoiseTree A n).preimage (by fun_prop)
    have hdesc : ∀ᵐ p ∂(powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)))), GoodNoiseTree A n p.2.2 := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply ae_of_all
      intro _
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_GoodNoiseTree A n).preimage measurable_snd)).mpr
      exact ae_of_all _ (fun _ => ih (fun j => b (j+1)) hb.tail (fun j => μ (j+1)))
    have hc := poissonLaw_ae_intensity _ hm hdesc
    filter_upwards [htot, hc] with ν ht hd
    exact ⟨ht, hd⟩

def noiseChildMass (n : ℕ) (ν : NoiseTree A (n+1)) : Measure (ℝ × (A × NoiseTree A n)) :=
  ν.withDensity (fun p => ENNReal.ofReal (max p.1 0)*noiseTreeTotal A n p.2.2)

omit [Nonempty A] in
lemma noiseChildMass_univ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseChildMass A n ν univ = noiseTreeTotal A (n+1) ν := by
  rw [noiseTreeTotal_succ]
  simp [noiseChildMass, withDensity_apply]

omit [Nonempty A] in
lemma measurable_noiseChildMass (n : ℕ) : Measurable (noiseChildMass A n) :=
  measurable_withDensity_fixed ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
    ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))

def noiseChildKernel (n : ℕ) : Kernel (NoiseTree A (n+1)) (ℝ × (A × NoiseTree A n)) :=
  ⟨fun ν => normalizeMass (noiseChildMass A n ν),
    measurable_normalizeMass.comp (measurable_noiseChildMass A n)⟩

instance noiseChildKernel_markov (n : ℕ) : IsMarkovKernel (noiseChildKernel A n) :=
  ⟨fun _ => normalizeMass_probability _⟩

@[reducible] def NoiseLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ℝ × (A × NoiseLeaf n)

instance noiseLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (NoiseLeaf A n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := noiseLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ℝ × (A × NoiseLeaf A n)))

instance noiseLeafNonempty : (n : ℕ) → Nonempty (NoiseLeaf A n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := noiseLeafNonempty n
    inferInstanceAs (Nonempty (ℝ × (A × NoiseLeaf A n)))

def noiseLeafKernelData : (n : ℕ) → {κ : Kernel (NoiseTree A n) (NoiseLeaf A n) // IsMarkovKernel κ}
  | 0 => ⟨Kernel.const _ (Measure.dirac PUnit.unit), by
      change IsMarkovKernel (Kernel.const PUnit (Measure.dirac (PUnit.unit : PUnit)))
      infer_instance⟩
  | n+1 =>
    let κ := (noiseLeafKernelData n).val
    letI : IsMarkovKernel κ := (noiseLeafKernelData n).property
    ⟨((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ κ)) ∘ₖ noiseChildKernel A n, by
      change IsMarkovKernel (((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ κ)) ∘ₖ noiseChildKernel A n)
      infer_instance⟩

def noiseLeafKernel (n : ℕ) : Kernel (NoiseTree A n) (NoiseLeaf A n) := (noiseLeafKernelData A n).val

instance noiseLeafKernel_markov (n : ℕ) : IsMarkovKernel (noiseLeafKernel A n) :=
  (noiseLeafKernelData A n).property

def noiseLeafForget : (n : ℕ) → NoiseLeaf A n → RawLeaf n
  | 0, _ => PUnit.unit
  | n+1, p => (p.1, noiseLeafForget n p.2.2)

omit [Nonempty A] in
lemma measurable_noiseLeafForget (n : ℕ) : Measurable (noiseLeafForget A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_fst.prodMk (ih.comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable (A : Type) [MeasurableSpace A] [Nonempty A]

omit [Nonempty A] in
lemma noiseChildMass_forget (n : ℕ) (ν : NoiseTree A (n+1)) :
    (noiseChildMass A n ν).map (fun p => (p.1, noiseTreeForget A n p.2.2)) =
      childMass n (noiseTreeForget A (n+1) ν) := by
  change (ν.withDensity (fun p => ENNReal.ofReal (max p.1 0) * rawTreeTotal n (noiseTreeForget A n p.2.2))).map
    (fun p => (p.1,noiseTreeForget A n p.2.2)) = (ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))).withDensity
      (fun p => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2)
  exact withDensity_map_pullback ν
    (f := fun p : ℝ × (A × NoiseTree A n) => (p.1,noiseTreeForget A n p.2.2))
    (w := fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2)
    (measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (by fun_prop)))
    ((by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd))

lemma noiseChildKernel_forget (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞) :
    (noiseChildKernel A n ν).map (fun p => (p.1, noiseTreeForget A n p.2.2)) =
    rawChildKernel n (noiseTreeForget A (n+1) ν) := by
  change (normalizeMass (noiseChildMass A n ν)).map _ = normalizeMass _
  rw [normalizeMass_map (noiseChildMass A n ν)
    (f := fun p : ℝ × (A × NoiseTree A n) => (p.1,noiseTreeForget A n p.2.2))
    (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (by fun_prop)))
      (by simpa only [noiseChildMass_univ] using hν), noiseChildMass_forget]

lemma noiseChildKernel_ae (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {p : ℝ × (A × NoiseTree A n) → Prop} (hp : ∀ᵐ x ∂ν, p x) :
    ∀ᵐ x ∂noiseChildKernel A n ν, p x := by
  change ∀ᵐ x ∂normalizeMass (noiseChildMass A n ν), p x
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν)]
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous ν _).ae_le hp) _

lemma noiseLeafKernel_succ (n : ℕ) : noiseLeafKernel A (n+1) =
    ((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ noiseLeafKernel A n)) ∘ₖ
      noiseChildKernel A n := rfl

lemma noiseLeafKernel_step (n : ℕ) (ν : NoiseTree A (n+1))
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2 ∂noiseChildKernel A n ν := by
  rw [noiseLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  swap
  · exact hF.lintegral_prod_right'
  rw [Kernel.parallelComp_apply, Kernel.id_apply,
    lintegral_prod _ (show AEMeasurable (fun y : A × NoiseLeaf A n => F (p.1,y)) _ from
      (hF.comp measurable_prodMk_left).aemeasurable),
    lintegral_dirac']
  exact (hF.comp measurable_prodMk_left).lintegral_prod_right'

omit [Nonempty A] in
lemma rawLeafKernel_step (n : ℕ) (ν : RawTree (n+1))
    {F : RawLeaf (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂rawLeafKernel (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,v) ∂rawLeafKernel n p.2 ∂rawChildKernel n ν := by
  rw [rawLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  exact hF.lintegral_prod_right'

theorem noiseLeafKernel_forget (n : ℕ) (ν : NoiseTree A n) (hν : GoodNoiseTree A n ν) :
    (noiseLeafKernel A n ν).map (noiseLeafForget A n) = rawLeafKernel n (noiseTreeForget A n ν) := by
  induction n with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_noiseLeafForget A (n+1)).aemeasurable,
      noiseLeafKernel_step A n ν (F := fun v => F (noiseLeafForget A (n+1) v))
        (hF.comp (measurable_noiseLeafForget A (n+1))),
      rawLeafKernel_step n _ hF]
    have hm : Measurable (fun p : ℝ × RawTree n =>
        ∫⁻ v, F (p.1,v) ∂rawLeafKernel n p.2) :=
      (hF.comp (by fun_prop : Measurable (fun p : (ℝ × RawTree n) × RawLeaf n => (p.1.1,p.2)))).lintegral_kernel_prod_right'
        (κ := (rawLeafKernel n).comap Prod.snd measurable_snd)
    rw [← noiseChildKernel_forget A n ν hν.1,
      lintegral_map' hm.aemeasurable (show AEMeasurable (fun p : ℝ × (A × NoiseTree A n) =>
          (p.1,noiseTreeForget A n p.2.2)) _ from (measurable_fst.prodMk
        ((measurable_noiseTreeForget A n).comp (by fun_prop))).aemeasurable)]
    apply lintegral_congr_ae
    filter_upwards [noiseChildKernel_ae A n ν hν.1 hν.2] with p hp
    change (∫⁻ v, F (p.1,noiseLeafForget A n v) ∂noiseLeafKernel A n p.2.2) = _
    rw [← ih p.2.2 hp,
      lintegral_map' (show AEMeasurable (fun v : RawLeaf n => F (p.1,v)) _ from
        (hF.comp measurable_prodMk_left).aemeasurable) (measurable_noiseLeafForget A n).aemeasurable]

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseLeafTerminal : (n : ℕ) → (ℕ → S → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → ℝ
  | 0, X, _, s, _ => X 0 s
  | n+1, X, u, s, v => noiseLeafTerminal n (fun i => X (i+1))
      (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2

omit [Nonempty A] in
lemma measurable_noiseLeafTerminal (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafTerminal n X u p.1 p.2) := by
  induction n generalizing X u with
  | zero => exact (hX 0).comp measurable_fst
  | succ n ih =>
    exact (ih (fun i => hX (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))

lemma noiseChildKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : ℝ × (A × NoiseTree A n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂noiseChildKernel A n ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (noiseChildMass A n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, noiseChildMass_univ, noiseChildMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × (A × NoiseTree A n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2) from
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))) hF

lemma noiseLeafKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_step A n ν hF]
  apply noiseChildKernel_lintegral n ν hν
  exact (hF.comp (by fun_prop : Measurable (fun p :
      (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))

lemma measurable_noiseLeafIntegral (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => ∫⁻ v,
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u p.1 v)) ∂noiseLeafKernel A n p.2) :=
  (((measurable_noiseLeafTerminal n hX hu).comp (by fun_prop : Measurable
    (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)))).exp.ennreal_ofReal).lintegral_kernel_prod_right'
      (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

theorem noiseTreeFactor_leafIntegral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      noiseTreeFactor n b μ X u s ν = noiseTreeTotal A n ν *
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v)) ∂noiseLeafKernel A n ν := by
  induction n generalizing b μ X u s with
  | zero =>
    apply ae_of_all
    intro ν
    simp [noiseTreeFactor, noiseTreeTotal, rawTreeTotal, noiseLeafTerminal,
      noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let Xt := fun j => X (j+1)
    let ut := fun j => u (j+1)
    let P := (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 = noiseTreeTotal A n p.2.2 *
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n Xt ut (u 0 (s,p.2.1)) v))
        ∂noiseLeafKernel A n p.2.2
    have hme : MeasurableSet {p | E p} := by
      apply measurableSet_eq_fun
      · exact (measurable_noiseTreeFactor n bt μt (fun i => hX (i+1))
          (fun i => hu (i+1))).comp (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
      · exact ((measurable_noiseTreeTotal A n).comp (by fun_prop)).mul
          ((measurable_noiseLeafIntegral n (fun i => hX (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    have he : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hme).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hme.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih bt hb.tail μt (fun i => hX (i+1)) (fun i => hu (i+1)) (u 0 (s,a))
    have ha := poissonLaw_ae_intensity I hme he
    have hg := noiseCascade_good A n.succ b hb μ
    have hσ := sigmaPart_eq_ae I
    filter_upwards [ha,hg,hσ] with ν hν hg hσ
    rw [noiseTreeFactor]
    change (∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 ∂sigmaPart I ν) = _
    rw [hσ, noiseLeafKernel_lintegral n ν hg.1
      (F := fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal (n+1) X u s v)))
      (((measurable_noiseLeafTerminal (n+1) hX hu).comp
        (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hg.1.1.ne' hg.1.2.ne, one_mul]
    apply lintegral_congr_ae
    filter_upwards [hν] with p hp
    rw [hp]
    exact (mul_assoc _ _ _).symm

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseLeafProduct : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | n+1, c, u, s, v => ENNReal.ofReal (c 0 (s,v.2.1)) *
      noiseLeafProduct n (fun i => c (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2

def noiseLeafKeep : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → NoiseLeaf A n
  | 0, _, _, _, _ => PUnit.unit
  | n+1, c, u, s, v => (c 0 (s,v.2.1)*v.1, (v.2.1,
      noiseLeafKeep n (fun i => c (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2))

omit [Nonempty A] in
lemma measurable_noiseLeafProduct (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafProduct n c u p.1 p.2) := by
  induction n generalizing c u with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((hc 0).comp (by fun_prop)).ennreal_ofReal.mul
      ((ih (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

omit [Nonempty A] in
lemma measurable_noiseLeafKeep (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafKeep n c u p.1 p.2) := by
  induction n generalizing c u with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : S × NoiseLeaf A (n+1) => p.2.2.1)).prodMk
        ((ih (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

def noiseWeightedLeafMeasure (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  ((noiseLeafKernel A n ν).withDensity
    (fun v => noiseTreeTotal A n ν * noiseLeafProduct n c u s v)).map (noiseLeafKeep n c u s)

lemma noiseWeightedLeafMeasure_lintegral (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) {F : NoiseLeaf A n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseWeightedLeafMeasure n c u s ν) = noiseTreeTotal A n ν *
      ∫⁻ v, noiseLeafProduct n c u s v * F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν := by
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  rw [noiseWeightedLeafMeasure, lintegral_map' hF.aemeasurable hk.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun v => noiseTreeTotal A n ν * noiseLeafProduct n c u s v) from measurable_const.mul hp)
      (show Measurable (fun v => F (noiseLeafKeep n c u s v)) from hF.comp hk)]
  change (∫⁻ v, (noiseTreeTotal A n ν * noiseLeafProduct n c u s v) *
    F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν) = _
  simp_rw [mul_assoc]
  exact lintegral_const_mul _ (hp.mul (hF.comp hk))

lemma measurable_noiseWeightedLeafMeasure (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseWeightedLeafMeasure n c u p.1 p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have he (p : S × NoiseTree A n) : noiseWeightedLeafMeasure n c u p.1 p.2 B =
      noiseTreeTotal A n p.2 * ∫⁻ v, noiseLeafProduct n c u p.1 v *
        B.indicator (fun _ => (1 : ℝ≥0∞)) (noiseLeafKeep n c u p.1 v) ∂noiseLeafKernel A n p.2 := by
    rw [← setLIntegral_one, ← lintegral_indicator hB (fun _ => (1 : ℝ≥0∞)),
      noiseWeightedLeafMeasure_lintegral n hc hu p.1 p.2 (measurable_const.indicator hB)]
  simp_rw [he]
  apply ((measurable_noiseTreeTotal A n).comp measurable_snd).mul
  have hh : Measurable (fun p : (S × NoiseTree A n) × NoiseLeaf A n =>
      noiseLeafProduct n c u p.1.1 p.2 *
        B.indicator (fun _ => (1 : ℝ≥0∞)) (noiseLeafKeep n c u p.1.1 p.2)) :=
    ((measurable_noiseLeafProduct n hc hu).comp (show Measurable (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)) from (by fun_prop))).mul
      ((measurable_const.indicator hB).comp ((measurable_noiseLeafKeep n hc hu).comp (show Measurable (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)) from (by fun_prop))))
  exact hh.lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

lemma measurable_noiseUnnormalizedLeaf (n : ℕ) :
    Measurable (fun ν : NoiseTree A n => noiseTreeTotal A n ν • noiseLeafKernel A n ν) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simp only [Measure.smul_apply, smul_eq_mul]
  exact (measurable_noiseTreeTotal A n).mul ((noiseLeafKernel A n).measurable_coe hB)

end IsingPerceptron

end

end OAI
