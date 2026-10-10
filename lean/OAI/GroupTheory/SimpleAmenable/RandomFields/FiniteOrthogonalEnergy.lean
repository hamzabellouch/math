import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.NoiseTensor

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteOrthogonalEnergy
open Classical MeasureTheory

theorem integral_finite_energy {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (F : I → X → ℝ)
    (h : ∀i j,Integrable (fun x => F i x*F j x) μ) :
    (∫x,(∑i,F i x)^2 ∂μ)=∑i,∑j,∫x,F i x*F j x ∂μ := by
  simp only [pow_two,Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => h i j)]

theorem integral_product_le_half_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable (fun x => f x*f x) μ)
    (hg : Integrable (fun x => g x*g x) μ)
    (hfg : Integrable (fun x => f x*g x) μ) :
    (∫x,f x*g x ∂μ)≤((∫x,(f x)^2 ∂μ)+(∫x,(g x)^2 ∂μ))/2 := by
  have hh : Integrable (fun x => f x*f x+g x*g x) μ := hf.add hg
  have hb : Integrable (fun x => 2*(f x*g x)) μ := hfg.const_mul 2
  have hp : 0 ≤ ∫x,f x*f x+g x*g x-2*(f x*g x) ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ f x*f x+g x*g x-2*(f x*g x)
    nlinarith [sq_nonneg (f x-g x)]
  rw [integral_sub hh hb,integral_add hf hg,integral_const_mul] at hp
  simp only [pow_two]
  linarith

theorem finite_overlap_energy {I X S : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (F : I → X → ℝ) (s : I → S)
    (h : ∀i j,Integrable (fun x => F i x*F j x) μ)
    (ho : ∀i j,s i≠s j → (∫x,F i x*F j x ∂μ)=0)
    (k : ℕ) (hcard : ∀i,(Finset.univ.filter (fun j => s i=s j)).card≤k) :
    (∫x,(∑i,F i x)^2 ∂μ)≤(k:ℝ)*∑i,∫x,F i x^2 ∂μ := by
  let E := fun i => ∫x,F i x^2 ∂μ
  have hE (i : I) : 0≤E i := integral_nonneg (fun _ => sq_nonneg _)
  have hc (i : I) : (∑j,if s i=s j then E i else 0)≤(k:ℝ)*E i := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (hE i)
  have hsum : (∑i,∑j,if s i=s j then E i else 0)≤(k:ℝ)*∑i,E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hc i)
  have hswap : (∑i,∑j,if s i=s j then E j else 0)=(∑i,∑j,if s i=s j then E i else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [eq_comm]
  rw [integral_finite_energy μ F h]
  calc
    _ ≤ ∑i,∑j,((if s i=s j then E i else 0)+(if s i=s j then E j else 0))/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · exact integral_product_le_half_energy μ (F i) (F j) (h i i) (h j j) (h i j)
      · rw [ho i j hij]
        norm_num
    _ = ((∑i,∑j,if s i=s j then E i else 0)+(∑i,∑j,if s i=s j then E j else 0))/2 := by
      simp only [← Finset.sum_div,Finset.sum_add_distrib]
    _ ≤ (k:ℝ)*∑i,E i := by rw [hswap]; linarith

end FiniteOrthogonalEnergy

section SmoothNoise
open Classical MeasureTheory
open scoped ContDiff

noncomputable def rawNoiseBump : ContDiffBump (0 : ℝ) :=
  ⟨1/2,1,by norm_num,by norm_num⟩

noncomputable def rawNoiseMass : ℝ := ∫x : ℝ,(rawNoiseBump x)^2

theorem rawNoiseMass_pos : 0<rawNoiseMass := by
  have hc : Continuous (fun x : ℝ => (rawNoiseBump x)^2) := rawNoiseBump.continuous.pow 2
  have hs : HasCompactSupport (fun x : ℝ => (rawNoiseBump x)^2) := by
    convert! rawNoiseBump.hasCompactSupport.mul_right (f':=rawNoiseBump) using 1
    ext x
    simp only [pow_two,Pi.mul_apply]
  apply integral_pos_of_integrable_nonneg_nonzero (x:=(0:ℝ)) hc (hc.integrable_of_hasCompactSupport hs)
    (fun _ => sq_nonneg _)
  have hh : rawNoiseBump (0 : ℝ)=1 := rawNoiseBump.one_of_mem_closedBall (by
    simp [rawNoiseBump])
  simp [hh]

noncomputable def smoothNoiseRoot (x : ℝ) : ℝ := rawNoiseBump x/Real.sqrt rawNoiseMass

theorem smoothNoiseRoot_nonneg (x : ℝ) : 0 ≤ smoothNoiseRoot x :=
  div_nonneg rawNoiseBump.nonneg (Real.sqrt_nonneg _)

theorem smoothNoiseRoot_even : Function.Even smoothNoiseRoot := by
  intro x
  simp only [smoothNoiseRoot,rawNoiseBump.neg]

theorem smoothNoiseRoot_contDiff : ContDiff ℝ ∞ smoothNoiseRoot :=
  rawNoiseBump.contDiff.div_const _

theorem smoothNoiseRoot_compact : HasCompactSupport smoothNoiseRoot := by
  convert! rawNoiseBump.hasCompactSupport.mul_right (f':=fun _ => (Real.sqrt rawNoiseMass)⁻¹) using 1

theorem smoothNoiseRoot_zero {x : ℝ} (hx : 1≤|x|) : smoothNoiseRoot x=0 := by
  rw [smoothNoiseRoot]
  have hh : rawNoiseBump x=0 := rawNoiseBump.zero_of_le_dist (by
    simpa only [rawNoiseBump,Real.dist_eq,sub_zero] using hx)
  rw [hh,zero_div]

theorem smoothNoiseRoot_pos {x : ℝ} (hx : |x|<1) : 0<smoothNoiseRoot x := by
  apply div_pos _ (Real.sqrt_pos.mpr rawNoiseMass_pos)
  apply rawNoiseBump.pos_of_mem_ball
  simpa only [rawNoiseBump,Metric.mem_ball,Real.dist_eq,sub_zero] using hx

theorem smoothNoiseRoot_normalized : (∫x : ℝ,smoothNoiseRoot x^2)=1 := by
  simp only [smoothNoiseRoot,div_pow]
  rw [integral_div,Real.sq_sqrt rawNoiseMass_pos.le]
  change rawNoiseMass/rawNoiseMass=1
  exact div_self rawNoiseMass_pos.ne'

end SmoothNoise

section NoiseCenteredEnergy
open Classical MeasureTheory

noncomputable def noiseEnergy (f : ℝ → ℝ) (i : NoiseFactor) : ℝ :=
  ∫x : ℝ,noiseFactor f i x^2

theorem noiseEnergy_nonneg (f : ℝ → ℝ) (i : NoiseFactor) : 0≤noiseEnergy f i :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem noise_centered_energy {ι I : Type*} [Fintype ι] [Fintype I]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (s : I → Finset ι) (p : I → ι → NoiseFactor) (c : I → ℝ)
    (hp : ∀i j,j∈s i → p i j≠.base)
    (k : ℕ) (hcard : ∀i,(Finset.univ.filter (fun j => s i=s j)).card≤k) :
    (∫x : ι → ℝ,(∑i,c i*centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j)) x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ)))) ≤
        (k:ℝ)*∑i,c i^2*∏j∈s i,noiseEnergy f (p i j) := by
  let T := fun i => centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j))
  have hT (i j : I) : Integrable (fun x : ι → ℝ => T i x*T j x)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    apply noiseTensor_integrable_inner
    intro l
    split_ifs
    · exact noiseFactor_integrable_product hf hc _ _
    · exact noiseFactor_integrable_product hf hc (p i l) .base
    · exact noiseFactor_integrable_product hf hc .base (p j l)
    · exact noiseFactor_integrable_product hf hc .base .base
  have hF (i j : I) : Integrable (fun x : ι → ℝ => (c i*T i x)*(c j*T j x))
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    apply ((hT i j).const_mul (c i*c j)).congr
    filter_upwards with x
    ring
  have ho (i j : I) (hne : s i≠s j) :
      (∫x : ι → ℝ,(c i*T i x)*(c j*T j x) ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=0 := by
    have hh := centeredNoiseTensor_orthogonal f (s i) (s j)
      (fun l => noiseFactor f (p i l)) (fun l => noiseFactor f (p j l))
      (fun l hl => noiseFactor_centered hf hc he _ (hp i l hl))
      (fun l hl => noiseFactor_centered hf hc he _ (hp j l hl)) hne
    rw [show (fun x : ι → ℝ => (c i*T i x)*(c j*T j x))=
      (fun x : ι → ℝ => (c i*c j)*(T i x*T j x)) by ext x; ring,
      integral_const_mul,hh,mul_zero]
  have hbound := finite_overlap_energy (Measure.pi (fun _ : ι => (volume : Measure ℝ)))
    (fun i x => c i*T i x) s hF ho k (by convert! hcard)
  convert hbound using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun x : ι → ℝ => (c i*T i x)^2)=
    (fun x : ι → ℝ => c i^2*(T i x)^2) by ext x; ring,integral_const_mul]
  rw [centeredNoiseTensor_energy f hn]
  rfl

noncomputable def singletonNoise {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (q : NoiseFactor) (i : ι) : (ι → ℝ) → ℝ := centeredNoiseTensor f {i} (fun _ => noiseFactor f q)

theorem singletonNoise_energy_bound {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (q : NoiseFactor) (hq : q≠.base) (c : ι → ℝ) :
    (∫x : ι → ℝ,(∑i,c i*singletonNoise f q i x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        noiseEnergy f q*∑i,c i^2 := by
  have h := noise_centered_energy hf hc he hn (fun i : ι => {i}) (fun _ _ => q) c
    (fun _ _ _ => hq) 1 (by
      intro i
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.singleton_inj.mp (ha'.symm.trans hb'))
  simpa only [singletonNoise,Finset.prod_singleton,Nat.cast_one,one_mul,Finset.mul_sum,mul_comm] using h

def NoisePair (ι : Type*) := {p : ι×ι // p.1≠p.2}

instance {ι : Type*} [Fintype ι] [DecidableEq ι] : Fintype (NoisePair ι) :=
  inferInstanceAs (Fintype {p : ι×ι // p.1≠p.2})

def noisePairSwap {ι : Type*} (p : NoisePair ι) : NoisePair ι := ⟨(p.val.2,p.val.1),Ne.symm p.property⟩

theorem noisePair_card {ι : Type*} [Fintype ι] (p : NoisePair ι) :
    (Finset.univ.filter (fun q : NoisePair ι => ({p.val.1,p.val.2} : Finset ι)={q.val.1,q.val.2})).card≤2 := by
  have hsub : Finset.univ.filter (fun q : NoisePair ι => ({p.val.1,p.val.2} : Finset ι)={q.val.1,q.val.2})
      ⊆ {p,noisePairSwap p} := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    have h₁ : p.val.1=q.val.1 ∨ p.val.1=q.val.2 := by
      have hh : p.val.1∈({q.val.1,q.val.2} : Finset ι) := by rw [← he]; simp
      simpa using hh
    have h₂ : p.val.2=q.val.1 ∨ p.val.2=q.val.2 := by
      have hh : p.val.2∈({q.val.1,q.val.2} : Finset ι) := by rw [← he]; simp
      simpa using hh
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact (p.property (h₁.trans h₂.symm)).elim
    · have hqp : q=p := Subtype.ext (Prod.ext h₁.symm h₂.symm)
      simp [hqp]
    · have hqp : q=noisePairSwap p := Subtype.ext (Prod.ext h₂.symm h₁.symm)
      simp [hqp]
    · exact (p.property (h₁.trans h₂.symm)).elim
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

noncomputable def pairNoise {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (p : NoisePair ι) : (ι → ℝ) → ℝ := centeredNoiseTensor f {p.val.1,p.val.2}
      (fun i => noiseFactor f (if i=p.val.1 then .score else .position))

theorem pairNoise_energy_bound {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (c : NoisePair ι → ℝ) :
    (∫x : ι → ℝ,(∑i,c i*pairNoise f i x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        2*(noiseEnergy f .score*noiseEnergy f .position)*∑i,c i^2 := by
  have h := noise_centered_energy hf hc he hn (fun p : NoisePair ι => {p.val.1,p.val.2})
    (fun p i => if i=p.val.1 then .score else .position) c
    (by intro i j _; split_ifs <;> decide) 2 noisePair_card
  have he (p : NoisePair ι) :
      (∏j∈({p.val.1,p.val.2} : Finset ι),noiseEnergy f (if j=p.val.1 then .score else .position))=
        noiseEnergy f .score*noiseEnergy f .position := by
    rw [Finset.prod_pair p.property]
    simp only [ite_true,ite_eq_right (Ne.symm p.property)]
  simp_rw [he] at h
  simpa only [pairNoise,Nat.cast_ofNat,← Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm] using h

end NoiseCenteredEnergy

end SimpleAmenable
end
end

end OAI
