import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FiniteOrthogonalEnergy

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineNoiseEnergy
open Classical MeasureTheory

theorem noise_centered_integrable_product {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s t : Finset ι) (p q : ι → NoiseFactor) :
    Integrable (fun x : ι → ℝ =>
      centeredNoiseTensor f s (fun i => noiseFactor f (p i)) x*
      centeredNoiseTensor f t (fun i => noiseFactor f (q i)) x)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply noiseTensor_integrable_inner
  intro i
  split_ifs
  · exact noiseFactor_integrable_product hf hc _ _
  · exact noiseFactor_integrable_product hf hc (p i) .base
  · exact noiseFactor_integrable_product hf hc .base (q i)
  · exact noiseFactor_integrable_product hf hc .base .base

theorem integrable_sum_product {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    (μ : Measure X) (f : I → X → ℝ) (g : J → X → ℝ)
    (h : ∀i j,Integrable (fun x => f i x*g j x) μ) :
    Integrable (fun x => (∑i,f i x)*(∑j,g j x)) μ := by
  simp only [Finset.sum_mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))

theorem integrable_three_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b c : X → ℝ) (h : ∀u∈({a,b,c} : Finset (X → ℝ)),
      ∀v∈({a,b,c} : Finset (X → ℝ)),Integrable (fun x => u x*v x) μ) :
    (∫x,(a x+b x+c x)^2 ∂μ)≤
      3*((∫x,a x^2 ∂μ)+(∫x,b x^2 ∂μ)+(∫x,c x^2 ∂μ)) := by
  have haa := h a (by simp) a (by simp)
  have hbb := h b (by simp) b (by simp)
  have hcc := h c (by simp) c (by simp)
  have hab := h a (by simp) b (by simp)
  have hac := h a (by simp) c (by simp)
  have hbc := h b (by simp) c (by simp)
  have hleft : Integrable (fun x => (a x+b x+c x)^2) μ := by
    apply ((((haa.add hbb).add hcc).add (hab.const_mul 2)).add
      ((hac.const_mul 2).add (hbc.const_mul 2))).congr
    filter_upwards with x
    dsimp only [Pi.add_apply]
    ring
  have hright : Integrable (fun x => 3*(a x^2+b x^2+c x^2)) μ := by
    convert! ((haa.add hbb).add hcc).const_mul 3 using 1
    ext x
    simp only [Pi.add_apply,pow_two]
  have hh := integral_mono hleft hright (fun x => by
    nlinarith [sq_nonneg (a x-b x),sq_nonneg (b x-c x),sq_nonneg (a x-c x)])
  rwa [integral_const_mul,integral_add (by convert! haa.add hbb using 1; ext x; simp only [Pi.add_apply,pow_two])
    (by convert! hcc using 1; ext x; simp only [pow_two]),integral_add
    (by convert! haa using 1; ext x; simp only [pow_two]) (by convert! hbb using 1; ext x; simp only [pow_two])] at hh

noncomputable def affineNoiseGenerator {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (L : Matrix ι ι ℝ) (v : ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑i,L i i*singletonNoise f .diagonal i x)+
  (∑i,v i*singletonNoise f .score i x)+
  ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x

noncomputable def affineNoiseEnergyConstant (f : ℝ → ℝ) : ℝ :=
  3*(noiseEnergy f .diagonal+noiseEnergy f .score+2*(noiseEnergy f .score*noiseEnergy f .position))

theorem affineNoiseEnergyConstant_nonneg (f : ℝ → ℝ) : 0≤affineNoiseEnergyConstant f := by
  unfold affineNoiseEnergyConstant
  have := noiseEnergy_nonneg f .diagonal
  have := noiseEnergy_nonneg f .score
  have := noiseEnergy_nonneg f .position
  positivity

theorem noise_sum_integrable_product {ι I J : Type*} [Fintype ι] [Fintype I] [Fintype J]
  {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s : I → Finset ι) (t : J → Finset ι) (p : I → ι → NoiseFactor)
    (q : J → ι → NoiseFactor) (u : I → ℝ) (w : J → ℝ) :
    Integrable (fun x : ι → ℝ =>
      (∑i,u i*centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j)) x)*
      (∑i,w i*centeredNoiseTensor f (t i) (fun j => noiseFactor f (q i j)) x))
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply integrable_sum_product
  intro i j
  apply ((noise_centered_integrable_product hf hc (s i) (t j) (p i) (q j)).const_mul (u i*w j)).congr
  filter_upwards with x
  ring

theorem affineNoiseGenerator_energy {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (L : Matrix ι ι ℝ) (v : ι → ℝ) :
    (∫x : ι → ℝ,affineNoiseGenerator f L v x^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        affineNoiseEnergyConstant f*((∑i,∑j,L i j^2)+∑i,v i^2) := by
  let a : (ι → ℝ) → ℝ := fun x => ∑i,L i i*singletonNoise f .diagonal i x
  let b : (ι → ℝ) → ℝ := fun x => ∑i,v i*singletonNoise f .score i x
  let c : (ι → ℝ) → ℝ := fun x => ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x
  have habc : ∀u∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),
      ∀w∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),Integrable (fun x => u x*w x)
        (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    intro u hu w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hw
    rcases hu with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl <;>
      dsimp only [a,b,c,singletonNoise,pairNoise] <;> apply noise_sum_integrable_product hf hc
  have H := integrable_three_energy (Measure.pi (fun _ : ι => (volume : Measure ℝ))) a b c habc
  have ha := singletonNoise_energy_bound hf hc he hn .diagonal (by decide) (fun i => L i i)
  have hb := singletonNoise_energy_bound hf hc he hn .score (by decide) v
  have hc' := pairNoise_energy_bound hf hc he hn (fun p : NoisePair ι => L p.val.1 p.val.2)
  let M := ∑i,∑j,L i j^2
  let V := ∑i,v i^2
  have hM : 0≤M := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hV : 0≤V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiag : (∑i,L i i^2)≤M := Finset.sum_le_sum (fun i _ =>
    Finset.single_le_sum (fun j _ => sq_nonneg (L i j)) (Finset.mem_univ i))
  have hoff : (∑p : NoisePair ι,L p.val.1 p.val.2^2)≤M := by
    change (∑p : {p : ι×ι // p.1≠p.2},L p.val.1 p.val.2^2)≤M
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : ι×ι => p.1≠p.2)) (by simp) (fun p : ι×ι => L p.1 p.2^2),Finset.sum_filter]
    calc
      _ ≤ ∑p : ι×ι,L p.1 p.2^2 := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _
      _ = M := by simp only [Fintype.sum_prod_type,M]
  have hD := noiseEnergy_nonneg f .diagonal
  have hS := noiseEnergy_nonneg f .score
  have hP := noiseEnergy_nonneg f .position
  have hSP : 0≤2*(noiseEnergy f .score*noiseEnergy f .position) := by positivity
  have ha' := ha.trans (mul_le_mul_of_nonneg_left hdiag hD)
  have hc'' := hc'.trans (mul_le_mul_of_nonneg_left hoff hSP)
  change (∫x : ι → ℝ,(a x+b x+c x)^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤_
  apply H.trans
  have hs : (∫x,a x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))+
      (∫x,b x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))+
      (∫x,c x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
      noiseEnergy f .diagonal*M+noiseEnergy f .score*V+2*(noiseEnergy f .score*noiseEnergy f .position)*M :=
    add_le_add (add_le_add ha' hb) hc''
  unfold affineNoiseEnergyConstant
  change 3*_≤3*_*(M+V)
  nlinarith [mul_nonneg hD hV,mul_nonneg hS hM,mul_nonneg hSP hV]

end AffineNoiseEnergy

section ActualNoiseLaw
open Classical MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

noncomputable def smoothNoiseDensity (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (smoothNoiseRoot x^2)

noncomputable def smoothNoiseLaw : Measure ℝ := volume.withDensity smoothNoiseDensity

theorem smoothNoiseDensity_measurable : Measurable smoothNoiseDensity :=
  (smoothNoiseRoot_contDiff.continuous.pow 2).measurable.ennreal_ofReal

instance smoothNoiseLaw_probability : IsProbabilityMeasure smoothNoiseLaw := by
  constructor
  rw [smoothNoiseLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi : Integrable (fun x : ℝ => smoothNoiseRoot x^2) := by
    have hc := smoothNoiseRoot_contDiff.continuous.pow 2
    apply hc.integrable_of_hasCompactSupport
    convert! smoothNoiseRoot_compact.mul_right (f':=smoothNoiseRoot) using 1
    ext x
    simp only [Pi.mul_apply,pow_two]
  change (∫⁻x : ℝ,ENNReal.ofReal (smoothNoiseRoot x^2))=1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _)),
    smoothNoiseRoot_normalized,ENNReal.ofReal_one]

theorem smoothNoiseLaw_bounded : ∀ᵐx ∂smoothNoiseLaw,x∈Set.Icc (-1:ℝ) 1 := by
  rw [smoothNoiseLaw,ae_withDensity_iff smoothNoiseDensity_measurable]
  filter_upwards with x hx
  by_contra h
  have hh : 1≤|x| := by
    have hn : ¬ |x|≤1 := by simpa only [abs_le,Set.mem_Icc] using h
    exact (lt_of_not_ge hn).le
  have hz := smoothNoiseRoot_zero hh
  exact hx (by simp [smoothNoiseDensity,hz])

theorem smoothNoiseLaw_centered : (∫x : ℝ,x ∂smoothNoiseLaw)=0 := by
  rw [smoothNoiseLaw,integral_withDensity_eq_integral_toReal_smul smoothNoiseDensity_measurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smoothNoiseDensity,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
  have h := noiseFactor_centered (smoothNoiseRoot_contDiff.of_le (by norm_num))
    smoothNoiseRoot_compact smoothNoiseRoot_even .position (by decide)
  convert! h using 1
  congr 1
  ext x
  simp only [noiseFactor]
  ring

noncomputable def independentSmoothNoiseLaw (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => smoothNoiseLaw)

instance independentSmoothNoiseLaw_probability (ι : Type*) :
    IsProbabilityMeasure (independentSmoothNoiseLaw ι) := by
  unfold independentSmoothNoiseLaw
  infer_instance

theorem independentSmoothNoiseLaw_independent (ι : Type*) :
    iIndepFun (fun (i : ι) (x : ι → ℝ) => x i) (independentSmoothNoiseLaw ι) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem independentSmoothNoiseLaw_map (ι : Type*) (i : ι) :
    (independentSmoothNoiseLaw ι).map (fun x => x i)=smoothNoiseLaw :=
  Measure.infinitePi_map_eval _ i

theorem independentSmoothNoiseLaw_bounded (ι : Type*) (i : ι) :
    ∀ᵐx ∂independentSmoothNoiseLaw ι,x i∈Set.Icc (-1:ℝ) 1 := by
  have hh := smoothNoiseLaw_bounded
  rw [← independentSmoothNoiseLaw_map ι i] at hh
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable (by measurability)).mp hh

theorem independentSmoothNoiseLaw_centered (ι : Type*) (i : ι) :
    (∫x : ι → ℝ,x i ∂independentSmoothNoiseLaw ι)=0 := by
  have hh := smoothNoiseLaw_centered
  rw [← independentSmoothNoiseLaw_map ι i] at hh
  rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)] at hh
  exact hh

end ActualNoiseLaw

end SimpleAmenable
end
end

end OAI
