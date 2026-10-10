import Mathlib
import OAI.Probability.IsingPerceptron.NoiseTreeKeep

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def NoiseGibbsRegular : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → Prop
  | 0, _, _, _, _, _, _ => True
  | n+1, b, μ, c, u, s, ν =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    (0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞) ∧
    (0 < noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) ∧
      noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) < ∞) ∧
    Marked.PoissonGood I ν ∧ ∀ᵐ p ∂sigmaPart I ν,
      NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2

lemma measurableSet_noiseGibbsRegular (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    MeasurableSet {p : S × NoiseTree A n | NoiseGibbsRegular n b μ c u p.1 p.2} := by
  induction n generalizing b μ c u with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot : Measurable (fun p : S × NoiseTree A (n+1) => noiseTreeTotal A (n+1) p.2) :=
      (measurable_noiseTreeTotal A (n+1)).comp measurable_snd
    have hkeep : Measurable (fun p : S × NoiseTree A (n+1) =>
        noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u p.1 p.2)) :=
      (measurable_noiseTreeTotal A (n+1)).comp (measurable_noiseTreeKeep (n+1) b μ hc hu)
    have hgood : MeasurableSet {p : S × NoiseTree A (n+1) | Marked.PoissonGood I p.2} :=
      by
        simp only [Marked.PoissonGood, ofPred_forall]
        exact MeasurableSet.iInter (fun j => measurableSet_lt
          ((Measure.measurable_coe (MeasurableSet.disjointed (measurableSet_spanningSets I) j)).comp measurable_snd)
          (measurable_const (a := (∞ : ℝ≥0∞))))
    let B := {p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) |
      ¬ NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2}
    have hB : MeasurableSet B :=
      ((ih _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))).compl
    have hm : Measurable (fun p : S × NoiseTree A (n+1) =>
        ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) :=
      measurable_sigmaPart_param I measurable_snd (measurable_const.indicator hB)
    have he : {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} =
        {p | (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) = 0} := by
      ext p
      rw [mem_ofPred_eq, mem_ofPred_eq, ae_iff]
      change (sigmaPart I p.2) {x | (p,x) ∈ B} = 0 ↔ _
      have hh := lintegral_indicator_one (μ := sigmaPart I p.2)
        (show MeasurableSet {x : ℝ × (A × NoiseTree A n) | (p,x) ∈ B} from
          hB.preimage (measurable_const.prodMk measurable_id))
      simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using Iff.of_eq (congrArg (· = 0) hh).symm
    have htail : MeasurableSet {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} := by
      rw [he]
      exact measurableSet_eq_fun hm measurable_const
    exact ((measurableSet_lt measurable_const htot).inter (measurableSet_lt htot measurable_const)).inter
      (((measurableSet_lt measurable_const hkeep).inter (measurableSet_lt hkeep measurable_const)).inter
        (hgood.inter htail))

lemma noiseGibbsRegular_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, ∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A) = 1) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), NoiseGibbsRegular n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot := noiseCascade_good A (n+1) b hb μ
    have hkeep : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) ∧
          noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) < ∞ := by
      simp_rw [noiseTreeTotal, noiseTreeKeep_forget (n+1) b μ hc hu]
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        ((measurable_noiseTreeDisplace (n+1) b μ hc hu).comp
          (measurable_const.prodMk measurable_id)).aemeasurable
      change ∀ᵐ y ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))).map
        (noiseTreeDisplace (n+1) b μ c u s), 0 < rawTreeTotal (n+1) y ∧ rawTreeTotal (n+1) y < ∞
      rw [noiseTreeDisplace_law (n+1) b μ hc hu hcpos hm s]
      exact (rawCascade_total_moments (n+1) b hb).1
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2
    have hE : MeasurableSet {p | E p} :=
      (measurableSet_noiseGibbsRegular n _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
    have ha : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hE).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hE.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih _ hb.tail _ (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (fun j => hm (j+1)) (u 0 (s,a))
    have hd := poissonLaw_ae_intensity I hE ha
    filter_upwards [htot,hkeep,Marked.poissonGood_ae I,hd] with ν hν hk hg hd
    refine ⟨hν.1,hk,hg,?_⟩
    rwa [Marked.sigmaPart_eq_of_good I hg]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

theorem noiseWeightedLeafMeasure_eq (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    noiseWeightedLeafMeasure n c u s ν =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
  induction n generalizing b μ c u s with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    simp [noiseWeightedLeafMeasure_lintegral 0 hc hu s ν hF,
      noiseTreeKeep, noiseTreeTotal, rawTreeTotal, noiseLeafProduct,
      noiseLeafKeep, noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let ct := fun j => c (j+1)
    let ut := fun j => u (j+1)
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) := fun p =>
      (c 0 (s,p.2.1)*p.1,(p.2.1,noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n bt μt (fun j => hc (j+1)) (fun j => hu (j+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))
    have hσ : sigmaPart I ν = ν := Marked.sigmaPart_eq_of_good I hν.2.2.1
    have hd : ∀ᵐ p ∂ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := by
      have hh : ∀ᵐ p ∂sigmaPart I ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := hν.2.2.2
      rwa [hσ] at hh
    have hkeep : noiseTreeKeep (n+1) b μ c u s ν = ν.map T := by
      change (sigmaPart I ν).map T = _
      rw [hσ]
    apply Measure.ext_of_lintegral
    intro F hF
    have hG : Measurable (fun v : NoiseLeaf A (n+1) =>
        noiseLeafProduct (n+1) c u s v * F (noiseLeafKeep (n+1) c u s v)) :=
      ((measurable_noiseLeafProduct (n+1) hc hu).comp (measurable_const.prodMk measurable_id)).mul
        (hF.comp ((measurable_noiseLeafKeep (n+1) hc hu).comp (measurable_const.prodMk measurable_id)))
    rw [noiseWeightedLeafMeasure_lintegral (n+1) hc hu s ν hF,
      noiseLeafKernel_unnormalized_lintegral n ν hν.1 hG,
      lintegral_smul_measure, smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hν.2.1 hF, hkeep]
    have hmF : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p : (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n =>
        (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
          (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    rw [lintegral_map' (show AEMeasurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) _ from
      (((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (by fun_prop))).mul hmF).aemeasurable) hT.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with p hp
    have hFp : Measurable (fun v : NoiseLeaf A n => F (c 0 (s,p.2.1)*p.1,(p.2.1,v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun η : Measure (NoiseLeaf A n) =>
      ∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v)) ∂η)
      (ih bt μt (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (u 0 (s,p.2.1)) p.2.2 hp)
    rw [noiseWeightedLeafMeasure_lintegral n (fun j => hc (j+1)) (fun j => hu (j+1)) _ _ hFp,
      lintegral_smul_measure, smul_eq_mul] at he
    change ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
      (∫⁻ v, (ENNReal.ofReal (c 0 (s,p.2.1)) * noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v) *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
          ∂noiseLeafKernel A n p.2.2) =
      ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
        noiseTreeTotal A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2) *
        (∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v))
          ∂noiseLeafKernel A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hcmax : max (c 0 (s,p.2.1)*p.1) 0 = c 0 (s,p.2.1)*max p.1 0 := by
      rw [mul_max_of_nonneg _ _ (hcpos 0 s p.2.1).le, mul_zero]
    rw [hcmax, ENNReal.ofReal_mul (hcpos 0 s p.2.1).le]
    simp_rw [mul_assoc]
    have hz : Measurable (fun v : NoiseLeaf A n => noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))) :=
      (((measurable_noiseLeafProduct n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
        (measurable_const.prodMk measurable_id)).mul
        (hFp.comp ((measurable_noiseLeafKeep n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
          (measurable_const.prodMk measurable_id))))
    rw [lintegral_const_mul _ hz]
    calc
      _ = ENNReal.ofReal (c 0 (s,p.2.1)) * ENNReal.ofReal (max p.1 0) *
          (noiseTreeTotal A n p.2.2 * ∫⁻ v, noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
            F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
              ∂noiseLeafKernel A n p.2.2) := by ring
      _ = _ := by rw [he]; ring

end IsingPerceptron

namespace IsingPerceptron

lemma normalizeMass_of_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] : normalizeMass ν = ν := by
  simp [normalizeMass, measure_univ]

lemma normalizeMass_smul {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞)
    (hν : 0 < ν univ ∧ ν univ < ∞) : normalizeMass (c • ν) = normalizeMass ν := by
  have ht : 0 < (c • ν) univ ∧ (c • ν) univ < ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos hc.1.ne' hν.1.ne', ENNReal.mul_lt_top hc.2 hν.2⟩
  rw [normalizeMass, ite_eq_left ht, normalizeMass, ite_eq_left hν,
    Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc.1.ne') (Or.inl hc.2.ne)]
  congr 1
  calc
    c⁻¹ * (ν univ)⁻¹ * c = (c⁻¹*c)*(ν univ)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc.1.ne' hc.2.ne, one_mul]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma NoiseGibbsRegular.masses {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S} {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞) ∧
      (0 < noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) ∧
        noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) < ∞) := by
  cases n with
  | zero => simp [noiseTreeTotal, rawTreeTotal]
  | succ n => exact ⟨hν.1,hν.2.1⟩

def noiseTiltedLeafLaw (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  normalizeMass ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s))

instance noiseTiltedLeafLaw_probability (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : IsProbabilityMeasure (noiseTiltedLeafLaw n c u s ν) :=
  normalizeMass_probability _

theorem noiseTiltedLeafLaw_keep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (noiseTiltedLeafLaw n c u s ν).map (noiseLeafKeep n c u s) =
      noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
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
    rw [hz, mul_zero] at hm
    exact hν.masses.2.1.ne' hm.symm
  have him : m univ < ∞ := by
    have hlt : noiseTreeTotal A n ν * m univ < ∞ := hm ▸ hν.masses.2.2
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact (hν.masses.1.1.ne' h).elim
    · exact (hm0.ne' h).elim
  change (normalizeMass m).map _ = _
  rw [← normalizeMass_smul m hν.masses.1 ⟨hm0,him⟩,
    normalizeMass_map _ hk (by
      simp only [Measure.smul_apply, smul_eq_mul, hm]
      exact hν.masses.2), he,
    normalizeMass_smul _ hν.masses.2 (by simp), normalizeMass_of_probability]

omit [MeasurableSpace A] [MeasurableSpace S] [Nonempty A] in
lemma noiseLeafProduct_telescoping (n : ℕ) (X : ℕ → S → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) :
    noiseLeafProduct n (fun i p => Real.exp (X (i+1) (u i p) - X i p.1)) u s v =
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v - X 0 s)) := by
  induction n generalizing X u s with
  | zero => simp [noiseLeafProduct, noiseLeafTerminal]
  | succ n ih =>
    rw [noiseLeafProduct]
    have hi := ih (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2
    rw [hi]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    change X 1 (u 0 (s,v.2.1)) - X 0 s +
      (noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 -
        X 1 (u 0 (s,v.2.1))) = _
    change _ = noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 - X 0 s
    ring

end IsingPerceptron

namespace IsingPerceptron
lemma normalizeMass_smul_any {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞) :
    normalizeMass (c • ν) = normalizeMass ν := by
  by_cases hν : 0 < ν univ ∧ ν univ < ∞
  · exact normalizeMass_smul ν hc hν
  · have ht : ¬ (0 < (c • ν) univ ∧ (c • ν) univ < ∞) := by
      intro h
      apply hν
      simp only [Measure.smul_apply, smul_eq_mul] at h
      constructor
      · by_contra hh
        have hz : ν univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
        simpa [hz] using h.1
      · rcases ENNReal.mul_lt_top_iff.mp h.2 with hh | hh | hh
        · exact hh.2
        · exact (hc.1.ne' hh).elim
        · simp [hh]
    simp only [normalizeMass, ite_eq_right ht, ite_eq_right hν]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTerminalGibbsLaw (n : ℕ) (X : ℕ → S → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  normalizeMass ((noiseLeafKernel A n ν).withDensity
    (fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v))))

lemma noiseTerminalGibbsLaw_eq_tilted (n : ℕ) {X : ℕ → S → ℝ}
    {u : ℕ → S × A → S} (hX : ∀ i, Measurable (X i))
    (hu : ∀ i, Measurable (u i)) (s : S) (ν : NoiseTree A n) :
    noiseTerminalGibbsLaw n X u s ν = noiseTiltedLeafLaw n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν := by
  have hm : Measurable (noiseLeafProduct n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s) :=
    (measurable_noiseLeafProduct n (fun i => ((hX (i+1) |>.comp (hu i)).sub
      ((hX i).comp measurable_fst)).exp) hu).comp (measurable_const.prodMk measurable_id)
  have hd : (fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v))) =
      ENNReal.ofReal (Real.exp (X 0 s)) • noiseLeafProduct n
        (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, noiseLeafProduct_telescoping]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  unfold noiseTerminalGibbsLaw noiseTiltedLeafLaw
  rw [hd, withDensity_smul _ hm, normalizeMass_smul_any _]
  exact ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top⟩

theorem noiseTerminalGibbsLaw_keep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν) :
    (noiseTerminalGibbsLaw n X u s ν).map (noiseLeafKeep n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s) =
      noiseLeafKernel A n (noiseTreeKeep n b μ
        (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν) := by
  rw [noiseTerminalGibbsLaw_eq_tilted n hX hu]
  exact noiseTiltedLeafLaw_keep n b μ (fun i => ((hX (i+1) |>.comp (hu i)).sub
    ((hX i).comp measurable_fst)).exp) hu (fun _ _ _ => Real.exp_pos _) s ν hν

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

def labeledPoissonLaw {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) : Measure (ℕ → ℕ × (ℕ → E)) :=
  Measure.infinitePi (fun n => finitePoissonCloud (μ n).mass (μ n).normalize)

instance labeledPoissonLaw_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) : IsProbabilityMeasure (labeledPoissonLaw μ) := by
  unfold labeledPoissonLaw
  infer_instance

def labeledPoissonMeasure {E : Type*} [MeasurableSpace E]
    (ω : ℕ → ℕ × (ℕ → E)) : Measure E :=
  Measure.sum (fun n => finiteCloudMeasure (ω n))

lemma measurable_labeledPoissonMeasure {E : Type*} [MeasurableSpace E] :
    Measurable (labeledPoissonMeasure (E := E)) :=
  measurable_measureSum.comp (Measurable.of_eval
    (fun _ => measurable_finiteCloudMeasure.comp (measurable_pi_apply _)))

lemma labeledPoissonMeasure_lintegral {E : Type*} [MeasurableSpace E]
    (ω : ℕ → ℕ × (ℕ → E)) {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x ∂labeledPoissonMeasure ω) = ∑' n, ∑ i : Fin (ω n).1, F ((ω n).2 i) := by
  simp only [labeledPoissonMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hF]

lemma labeledPoissonLaw_push {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (labeledPoissonLaw μ).map labeledPoissonMeasure =
      (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum := by
  have hm : Measurable (fun ω : ℕ → ℕ × (ℕ → E) => fun n => finiteCloudMeasure (ω n)) :=
    Measurable.of_eval (fun _ => measurable_finiteCloudMeasure.comp (measurable_pi_apply _))
  unfold labeledPoissonLaw labeledPoissonMeasure
  rw [show (fun ω : ℕ → ℕ × (ℕ → E) => Measure.sum (fun n => finiteCloudMeasure (ω n))) =
    Measure.sum ∘ (fun ω n => finiteCloudMeasure (ω n)) from rfl,
    ← Measure.map_map measurable_measureSum hm,Measure.infinitePi_map_pi]
  rfl
  exact fun _ => measurable_finiteCloudMeasure

lemma finitePoissonProduct_laplace_partial {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i)
      ∂Measure.infinitePi (fun i => finitePoissonLaw (μ i))) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ i : Measure E)) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind := iIndepFun_infinitePi (P := fun i => finitePoissonLaw (μ i)) (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂Measure.infinitePi (fun j => finitePoissonLaw (μ j))) =
        negExp (∫⁻ x, c x ∂(μ i : Measure E)) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂finitePoissonLaw (μ i) :=
        (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (μ j)) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace (μ i) hψ hpos
  simpa only [negExp_sum, hei] using hh

theorem finitePoissonProduct_sum_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  let P := Measure.infinitePi (fun n => finitePoissonLaw (μ n))
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto P ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂(μ i : Measure E)))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂Measure.sum (fun n => (μ n : Measure E))))) := by
    rw [lintegral_sum_measure]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂(μ i : Measure E))]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw_laplace _ hψ hpos,
    integral_map measurable_measureSum.aemeasurable heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂P) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a,P,finitePoissonProduct_laplace_partial μ hψ hpos] using hlim) (by simpa only [lintegral_sum_measure] using hr)

theorem labeledPoissonLaw_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (labeledPoissonLaw μ).map labeledPoissonMeasure =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  rw [labeledPoissonLaw_push,finitePoissonProduct_sum_law]

lemma finiteCloud_laplace {E : Type*} [MeasurableSpace E] (r : ℝ≥0)
    (ρ : Measure E) [IsProbabilityMeasure ρ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) ∂finitePoissonCloud r ρ) =
      negExp ((r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂ρ) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) ρ := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) ρ := (integrable_const 1).sub hi
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace r ρ hψ hpos,
    ← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg,
    negExp_ofReal (mul_nonneg r.coe_nonneg (integral_nonneg hcost)),
    integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring

lemma finiteCloud_mark_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (r : ℝ≥0) (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((finitePoissonCloud r μ).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) = finitePoissonCloud r (μ.prod ν) := by
  have hj : MeasurePreserving (fun p : (ℕ → E) × (ℕ → F) => fun i => (p.1 i,p.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hp := (MeasurePreserving.id (poissonMeasure r)).prod hj
  have ha := measurePreserving_prodAssoc (poissonMeasure r)
    (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => ν))
  exact (hp.comp ha).map_eq

lemma finiteCloud_mark_measure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : FiniteMeasure E) (ν : Measure F) [IsProbabilityMeasure ν] :
    ((finitePoissonCloud μ.mass (μ.normalize : Measure E)).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
      finitePoissonLaw ⟨(μ : Measure E).prod ν,inferInstance⟩ := by
  let ξ : FiniteMeasure (E × F) := ⟨(μ : Measure E).prod ν,inferInstance⟩
  change _ = finitePoissonLaw ξ
  rw [show (fun p : (ℕ × (ℕ → E)) × (ℕ → F) =>
    finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
    finiteCloudMeasure ∘ (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) from rfl,
    ← Measure.map_map measurable_finiteCloudMeasure (by fun_prop),finiteCloud_mark_law]
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun π : Measure (E × F) => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂π)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map measurable_finiteCloudMeasure.aemeasurable hm.aestronglyMeasurable,
    finiteCloud_laplace _ _ hψ hpos,finitePoissonLaw_laplace ξ hψ hpos]
  change _ = negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E).prod ν)
  rw [finiteMeasure_mass_normalize μ,Measure.prod_smul_left,lintegral_smul_measure]
  rfl

def labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) : Measure (E × F) :=
  Measure.sum (fun n => finiteCloudMeasure ((ω.1 n).1,fun i => ((ω.1 n).2 i,ω.2 n i)))

lemma measurable_labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] :
    Measurable (labeledMarkedMeasure (E := E) (F := F)) := by
  apply measurable_measureSum.comp
  apply Measurable.of_eval
  intro n
  apply measurable_finiteCloudMeasure.comp
  fun_prop

theorem labeledMarkedMeasure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : ℕ → FiniteMeasure E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    ((labeledPoissonLaw μ).prod (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => ν)))).map labeledMarkedMeasure =
    poissonLaw ((Measure.sum (fun n => (μ n : Measure E))).prod ν) := by
  let f : (ℕ × (ℕ → E)) × (ℕ → F) → Measure (E × F) :=
    fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))
  have hf : Measurable f := measurable_finiteCloudMeasure.comp (by fun_prop)
  have hjoin : Measurable (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := by
    fun_prop
  have hfpi : Measurable (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) :=
    Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))
  have hcomp : (labeledMarkedMeasure (E := E) (F := F)) =
    Measure.sum ∘ (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) ∘
      (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := rfl
  rw [hcomp,← Function.comp_assoc,← Measure.map_map (measurable_measureSum.comp hfpi) hjoin,
    labeledPoissonLaw,infinitePi_prod_join,
    ← Measure.map_map measurable_measureSum hfpi,Measure.infinitePi_map_pi _ (fun _ => hf)]
  simp only [f,finiteCloud_mark_measure_law]
  let η : ℕ → FiniteMeasure (E × F) := fun i => ⟨(μ i : Measure E).prod ν,inferInstance⟩
  change (Measure.infinitePi (fun i => finitePoissonLaw (η i))).map Measure.sum = _
  rw [finitePoissonProduct_sum_law η]
  have hcongr {P Q : Measure (E × F)} [SFinite P] [SFinite Q] (h : P = Q) :
      poissonLaw P = poissonLaw Q := by subst Q; rfl
  apply hcongr
  exact (Measure.prod_sum_left _ _).symm

end IsingPerceptron

end

end OAI
