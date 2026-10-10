import Mathlib
import OAI.Probability.ParisiFinite.MovingTensorInsertionLimit

namespace OAI

/-! Sine. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
namespace TrigLp
open MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable {κ : Type*} [Fintype κ]

 

def sine (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  Real.lipschitzWith_sin.compLp Real.sin_zero f

omit [Fintype κ] in
theorem sine_ae (f : Lp ℝ 2 μ) : (sine μ f : Ω → ℝ)=ᵐ[μ] fun ω => Real.sin (f ω) :=
  Real.lipschitzWith_sin.coeFn_compLp Real.sin_zero f

omit [Fintype κ] in
theorem sine_norm_sub_le (f g : Lp ℝ 2 μ) : ‖sine μ f-sine μ g‖≤‖f-g‖ := by
  simpa only [sine,NNReal.coe_one,one_mul] using
    Real.lipschitzWith_sin.norm_compLp_sub_le Real.sin_zero f g

omit [Fintype κ] in
theorem sine_continuous : Continuous (sine μ) :=
  Real.lipschitzWith_sin.continuous_compLp Real.sin_zero

omit [Fintype κ] in
theorem sum_ae {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    ((∑i∈s, f i : Lp ℝ 2 μ) : Ω → ℝ)=ᵐ[μ] fun ω => ∑i∈s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Pi.zero_def] using Lp.coeFn_zero ℝ 2 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑j∈s, f j),ih] with ω h1 h2
    rw [h1]
    simp only [Pi.add_apply]
    rw [h2]

def linear (a : κ → ℝ) (f : κ → Lp ℝ 2 μ) : Lp ℝ 2 μ := ∑k, a k • f k

theorem linear_ae (a : κ → ℝ) (f : κ → Lp ℝ 2 μ) :
    (linear μ a f : Ω → ℝ)=ᵐ[μ] fun ω => ∑k, a k*f k ω := by
  have ht : ∀ᵐ ω ∂μ, ∀k, (a k • f k : Lp ℝ 2 μ) ω=a k*f k ω :=
    ae_all_iff.mpr (fun k => by
      filter_upwards [Lp.coeFn_smul (a k) (f k)] with ω h
      simpa only [Pi.smul_apply,smul_eq_mul] using h)
  filter_upwards [sum_ae μ Finset.univ (fun k => a k • f k),ht] with ω h1 h2
  change (∑k, a k • f k : Lp ℝ 2 μ) ω= _
  rw [h1]
  exact Finset.sum_congr rfl (fun k hk => h2 k)

theorem linear_norm_sub_le (a : κ → ℝ) (f g : κ → Lp ℝ 2 μ) :
    ‖linear μ a f-linear μ a g‖≤∑k, |a k| *‖f k-g k‖ := by
  simp only [linear,←Finset.sum_sub_distrib,←smul_sub]
  simpa only [norm_smul,Real.norm_eq_abs] using norm_sum_le Finset.univ (fun k => a k • (f k-g k))

def polynomial (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (f : κ → Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ∑a∈s, b a • sine μ (linear μ a f)

theorem polynomial_ae (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (f : κ → Lp ℝ 2 μ) :
    (polynomial μ s b f : Ω → ℝ)=ᵐ[μ] fun ω => FourierDensity.sinePolynomial s b (fun k => f k ω) := by
  have ht (a : κ → ℝ) :
      ((b a • sine μ (linear μ a f) : Lp ℝ 2 μ) : Ω → ℝ)=ᵐ[μ]
        fun ω => b a*FourierDensity.sine a (fun k => f k ω) := by
    filter_upwards [Lp.coeFn_smul (b a) (sine μ (linear μ a f)),
      sine_ae μ (linear μ a f),linear_ae μ a f] with ω h1 h2 h3
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [h2,h3]
    rfl
  have hts := (Filter.eventually_all_finset s).mpr (fun a ha => ht a)
  filter_upwards [sum_ae μ s (fun a => b a • sine μ (linear μ a f)),hts] with ω h1 h2
  change (∑a∈s, b a • sine μ (linear μ a f) : Lp ℝ 2 μ) ω= _
  rw [h1]
  exact Finset.sum_congr rfl h2

 

theorem polynomial_norm_sub_le (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (f g : κ → Lp ℝ 2 μ) :
    ‖polynomial μ s b f-polynomial μ s b g‖ ≤
      ∑a∈s, |b a| *(∑k, |a k| *‖f k-g k‖) := by
  simp only [polynomial,←Finset.sum_sub_distrib,←smul_sub]
  calc
    _ ≤ ∑a∈s, ‖b a • (sine μ (linear μ a f)-sine μ (linear μ a g))‖ := norm_sum_le _ _
    _ ≤ ∑a∈s, |b a| *(∑k, |a k| *‖f k-g k‖) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_smul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (b a))
      exact (sine_norm_sub_le μ _ _).trans (linear_norm_sub_le μ a f g)

theorem polynomial_continuous (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    Continuous (polynomial μ s b) := by
  unfold polynomial
  apply continuous_finsetSum
  intro a ha
  have hl : Continuous (linear μ a) := by unfold linear; fun_prop
  convert ((sine_continuous μ).comp hl).const_smul (b a) using 1
  ext f
  rfl

end TrigLp

namespace GaussianCoherent
open MeasureTheory ProbabilityTheory Complex CoherentFock
open scoped BigOperators InnerProductSpace ComplexConjugate
variable {κ : Type*} [Fintype κ]

 

def linearField (d : Mode κ) (g : κ → ℝ) : ℂ := ∑k, d k*(g k:ℂ)

theorem memLp_linearField (d : Mode κ) : MemLp (linearField d) 2 (GaussianFourier.law κ) := by
  classical
  unfold linearField
  apply memLp_finsetSum Finset.univ
  intro k hk
  have hm : MemLp (fun g : κ → ℝ => g k) 2 (GaussianFourier.law κ) := by
    simpa only [Function.comp_def,id_eq,GaussianFourier.law,ENNReal.coe_ofNat] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
        (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  exact hm.ofReal.const_mul (d k)

def fieldVector (d : Mode κ) : Hilbert κ := (memLp_linearField d).toLp (linearField d)

theorem fieldVector_ae (d : Mode κ) :
    (fieldVector d : (κ → ℝ) → ℂ)=ᵐ[GaussianFourier.law κ] linearField d :=
  (memLp_linearField d).coeFn_toLp

theorem conj_wave (d : Mode κ) (g : κ → ℝ) :
    conj (wave d g)=Complex.exp (conj (offset d))*
      Complex.exp (∑k, (-I*conj (d k))*(g k:ℂ)) := by
  simp only [wave,map_mul,←Complex.exp_conj,map_sum,Complex.conj_I,Complex.conj_ofReal]

theorem conjugate_exponent (d : Mode κ) :
    conj (offset d)+(∑k, (-I*conj (d k))^2/2)=-((‖d‖^2:ℝ):ℂ)/2 := by
  have hi (z : ℂ) : (-I*conj z)^2= -(conj z)^2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [offset,map_sub,map_div₀,map_sum,map_pow,Complex.conj_ofReal,map_ofNat,hi]
  simp_rw [neg_div]
  rw [Finset.sum_neg_distrib,←Finset.sum_div]
  ring

theorem integrable_wave_coord (e : Mode κ) (k : κ) :
    Integrable (fun g => conj (wave e g)*(g k:ℂ)) (GaussianFourier.law κ) := by
  classical
  convert (GaussianFourier.integrable_coord_exp_sum (fun j => -I*conj (e j)) k).const_mul
    (Complex.exp (conj (offset e))) using 1
  funext g
  rw [conj_wave]
  ring

theorem integral_wave_coord (e : Mode κ) (k : κ) :
    (∫g, conj (wave e g)*(g k:ℂ) ∂GaussianFourier.law κ)=
      (-I*conj (e k))*(Real.exp (-‖e‖^2/2):ℂ) := by
  classical
  calc
    _=Complex.exp (conj (offset e))*(∫g, (g k:ℂ)*
        Complex.exp (∑j, (-I*conj (e j))*(g j:ℂ)) ∂GaussianFourier.law κ) := by
      rw [←integral_const_mul]
      congr 1
      funext g
      rw [conj_wave]
      ring
    _=(-I*conj (e k))*Complex.exp (conj (offset e)+∑j, (-I*conj (e j))^2/2) := by
      rw [GaussianFourier.integral_coord_exp_sum,Complex.exp_add]
      ring
    _=_ := by
      rw [conjugate_exponent]
      congr 1
      norm_cast

theorem inner_vector_fieldVector (e d : Mode κ) :
    ⟪vector e,fieldVector d⟫_ℂ=
      (-I)*(Real.exp (-‖e‖^2/2):ℂ)*⟪e,d⟫_ℂ := by
  classical
  rw [L2.inner_def]
  calc
    _=(∫g, conj (wave e g)*linearField d g ∂GaussianFourier.law κ) := by
      apply integral_congr_ae
      filter_upwards [vector_ae e,fieldVector_ae d] with g he hd
      rw [RCLike.inner_apply',he,hd]
    _=∑k, d k*(∫g, conj (wave e g)*(g k:ℂ) ∂GaussianFourier.law κ) := by
      simp only [linearField,Finset.mul_sum]
      have hi (k : κ) : Integrable (fun g => conj (wave e g)*(d k*(g k:ℂ))) (GaussianFourier.law κ) := by
        convert (integrable_wave_coord e k).const_mul (d k) using 1
        funext g
        ring
      rw [integral_finsetSum Finset.univ (fun k hk => hi k)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [←integral_const_mul]
      congr 1
      funext g
      ring
    _=_ := by
      simp only [integral_wave_coord,PiLp.inner_apply,RCLike.inner_apply',Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

 

theorem gaussianUnitary_creationVacuum (d : Mode κ) :
    (gaussianUnitary (κ := κ)) (creationVacuum (E := Mode κ) d)=fieldVector d := by
  apply (gaussianUnitary (κ := κ)).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  apply CoherentFock.eq_of_inner_coherent
  intro e
  apply (starRingEnd ℂ).injective
  simp only [inner_conj_symm]
  have hm := (gaussianUnitary (κ := κ)).inner_map_map (coherent e)
    ((gaussianUnitary (κ := κ)).symm (fieldVector d))
  simp only [LinearIsometryEquiv.apply_symm_apply,gaussianUnitary_coherent] at hm
  rw [←hm,inner_vector_fieldVector]
  simp only [creationVacuum,inner_smul_right,inner_coherent_oneParticle,mul_assoc]

 

theorem norm_fieldVector (d : Mode κ) : ‖fieldVector d‖=‖d‖ := by
  rw [←gaussianUnitary_creationVacuum]
  exact ((gaussianUnitary (κ := κ)).norm_map _).trans (norm_creationVacuum d)

theorem inner_fieldVector (d e : Mode κ) : ⟪fieldVector d,fieldVector e⟫_ℂ=⟪d,e⟫_ℂ := by
  rw [←gaussianUnitary_creationVacuum,←gaussianUnitary_creationVacuum,
    (gaussianUnitary (κ := κ)).inner_map_map]
  exact creationEmbedding.inner_map_map d e

end GaussianCoherent
namespace BoundedSeed
open MeasureTheory Filter
open scoped Topology

 

def truncate (n : ℕ) (x : ℝ) : ℝ := ((n:ℝ)+1)*Real.sin (x/((n:ℝ)+1))

lemma scale_pos (n : ℕ) : 0<(n:ℝ)+1 := by positivity

@[simp] theorem truncate_neg (n : ℕ) (x : ℝ) : truncate n (-x)= -truncate n x := by
  simp only [truncate,neg_div,Real.sin_neg,mul_neg]

theorem truncate_bounded (n : ℕ) (x : ℝ) : |truncate n x|≤(n:ℝ)+1 := by
  rw [truncate,abs_mul,abs_of_pos (scale_pos n)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (scale_pos n).le).trans_eq (mul_one _)

theorem truncate_dominated (n : ℕ) (x : ℝ) : |truncate n x|≤|x| := by
  rw [truncate,abs_mul,abs_of_pos (scale_pos n)]
  calc
    _≤((n:ℝ)+1)*|x/((n:ℝ)+1)| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (scale_pos n).le
    _=|x| := by rw [abs_div,abs_of_pos (scale_pos n)]; field_simp

theorem truncate_eq_sinc (n : ℕ) (x : ℝ) :
    truncate n x=x*Real.sinc (x/((n:ℝ)+1)) := by
  by_cases hx : x=0
  · simp [hx,truncate]
  rw [Real.sinc_of_ne_zero (div_ne_zero hx (scale_pos n).ne')]
  unfold truncate
  field_simp

theorem tendsto_truncate (x : ℝ) : Tendsto (fun n : ℕ => truncate n x) atTop (𝓝 x) := by
  have ht : Tendsto (fun n : ℕ => x/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => x*(1/((n:ℝ)+1))) atTop (𝓝 (x*0)))
  have hh := (Real.continuous_sinc.continuousAt.tendsto.comp ht).const_mul x
  simpa only [Function.comp_apply,Real.sinc_zero,mul_one,←truncate_eq_sinc] using hh

theorem contDiff_truncate (n : ℕ) : ContDiff ℝ ⊤ (truncate n) := by
  unfold truncate
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_truncate {p : ENNReal} {f : Ω → ℝ} (hf : MemLp f p μ) (n : ℕ) :
    MemLp (fun ω => truncate n (f ω)) p μ := by
  apply hf.mono ((contDiff_truncate n).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using truncate_dominated n (f ω)

 

theorem tendsto_error_moment {k : ℕ} (hk : k≠0) {f : Ω → ℝ} (hf : MemLp f k μ) :
    Tendsto (fun n : ℕ => ∫ω, |truncate n (f ω)-f ω|^k ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω => |truncate n (f ω)-f ω|^k) μ := by
    have hc : Continuous (fun x : ℝ => |truncate n x-x|^k) := by
      exact ((contDiff_truncate n).continuous.sub continuous_id).abs.pow k
    exact hc.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hi : Integrable (fun ω => (2:ℝ)^k*‖f ω‖^k) μ :=
    (hf.integrable_norm_pow hk).const_mul _
  have hb (n : ℕ) : ∀ᵐ ω ∂μ, ‖|truncate n (f ω)-f ω|^k‖≤(2:ℝ)^k*‖f ω‖^k := by
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    calc
      _≤(2*|f ω|)^k := by
        apply pow_le_pow_left₀ (abs_nonneg _)
        calc
          |truncate n (f ω)-f ω|≤|truncate n (f ω)|+|f ω| := abs_sub _ _
          _≤2*|f ω| := by linarith [truncate_dominated n (f ω)]
      _=_ := by rw [mul_pow,Real.norm_eq_abs]
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => |truncate n (f ω)-f ω|^k) atTop (𝓝 (0:ℝ)) := by
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [sub_self,abs_zero,zero_pow hk] using
      (((tendsto_truncate (f ω)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f ω) atTop (𝓝 (f ω)))).abs.pow k)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun ω => (2:ℝ)^k*‖f ω‖^k) hm hi hb hl

 

theorem tendsto_gaussian_error_moment (k : ℕ) (hk : k≠0) :
    Tendsto (fun n : ℕ => ∫x : ℝ, |truncate n x-x|^k ∂ProbabilityTheory.gaussianReal 0 1)
      atTop (𝓝 0) :=
  tendsto_error_moment hk (ProbabilityTheory.memLp_id_gaussianReal' k (by simp))

end BoundedSeed

namespace TrigLp
open MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {κ : Type*} [Fintype κ]
variable (μ : Measure Ω) (ν : Measure (κ → ℝ)) [IsFiniteMeasure ν]
variable (X : Ω → κ → ℝ) (hX : MeasurePreserving X μ ν)
variable (cols : κ → Lp ℝ 2 μ)
variable (hcols : ∀k, (cols k : Ω → ℝ)=ᵐ[μ] fun ω => X ω k)
include hcols

 

theorem pullback_sine (a : κ → ℝ) :
    Lp.compMeasurePreserving X hX (FourierDensity.sineVector ν a)=
      sine μ (linear μ a cols) := by
  apply Lp.ext
  have hc := ae_all_iff.mpr hcols
  have hs := hX.quasiMeasurePreserving.ae (FourierDensity.sineVector_ae ν a)
  filter_upwards [Lp.coeFn_compMeasurePreserving (FourierDensity.sineVector ν a) hX,
    hs,sine_ae μ (linear μ a cols),linear_ae μ a cols,hc] with ω h1 h2 h3 h4 h5
  rw [h1,h3,h4]
  change FourierDensity.sineVector ν a (X ω)=Real.sin (∑k, a k*cols k ω)
  rw [h2]
  unfold FourierDensity.sine
  congr 1
  exact Finset.sum_congr rfl (fun k hk => by rw [h5 k])

 

theorem pullback_polynomial (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    Lp.compMeasurePreservingₗ ℝ X hX (∑a∈s, b a • FourierDensity.sineVector ν a)=
      polynomial μ s b cols := by
  simp only [map_sum,map_smul,polynomial]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact pullback_sine μ ν X hX cols hcols a

 

theorem exists_local_approx
    (hν : MeasurePreserving (fun g : κ → ℝ => -g) ν ν)
    (f : Lp ℝ 2 ν) (hf : ∀ᵐ g ∂ν, f (-g)= -f g) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ,
      ‖polynomial μ s b cols-Lp.compMeasurePreserving X hX f‖<ε := by
  obtain ⟨s,b,hb⟩ := FourierDensity.exists_odd_sine_approx ν hν f hf hε
  refine ⟨s,b,?_⟩
  rw [←pullback_polynomial μ ν X hX cols hcols]
  change ‖Lp.compMeasurePreservingₗ ℝ X hX (∑a∈s, b a • FourierDensity.sineVector ν a)-
      Lp.compMeasurePreservingₗ ℝ X hX f‖<ε
  rw [←map_sub]
  change ‖Lp.compMeasurePreserving X hX ((∑a∈s, b a • FourierDensity.sineVector ν a)-f)‖<ε
  rwa [Lp.norm_compMeasurePreserving]

 

theorem exists_robust_local_approx
    (hν : MeasurePreserving (fun g : κ → ℝ => -g) ν ν)
    (f : Lp ℝ 2 ν) (hf : ∀ᵐ g ∂ν, f (-g)= -f g) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀g : κ → Lp ℝ 2 μ, (∀k, ‖g k-cols k‖<δ) →
        ‖polynomial μ s b g-Lp.compMeasurePreserving X hX f‖<ε := by
  obtain ⟨s,b,hb⟩ := exists_local_approx μ ν X hX cols hcols hν f hf (half_pos hε)
  have hc := (polynomial_continuous μ s b).continuousAt (x := cols)
  obtain ⟨δ,hδ,hdb⟩ := Metric.continuousAt_iff.mp hc (ε/2) (half_pos hε)
  refine ⟨s,b,δ,hδ,?_⟩
  intro g hg
  have hd : dist g cols<δ := (dist_pi_lt_iff hδ).mpr (fun k => by
    simpa only [dist_eq_norm] using hg k)
  have ho := hdb hd
  calc
    _ ≤ ‖polynomial μ s b g-polynomial μ s b cols‖+
        ‖polynomial μ s b cols-Lp.compMeasurePreserving X hX f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [dist_eq_norm] using ho) hb
    _ = ε := add_halves ε

end TrigLp

namespace FourierDensity
variable {κ : Type*} [Fintype κ]

@[simp] theorem sineOutput_odd (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) :
    sineOutput s b (-g)= -sineOutput s b g := by
  simp only [sineOutput,sinePolynomial_odd,mul_neg,Real.sin_neg]

theorem sineOutput_bounded (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → ℝ) :
    |sineOutput s b g|≤1 := Real.abs_sin_le_one _

theorem sineOutput_contDiff (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    ContDiff ℝ ⊤ (sineOutput s b) := by
  unfold sineOutput
  exact Real.contDiff_sin.comp (contDiff_const.mul (sinePolynomial_contDiff s b))
end FourierDensity

namespace TrigLp
open MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {κ : Type*} [Fintype κ] (μ : Measure Ω)

 

def readout (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  sine μ ((2:ℝ) • polynomial μ s b g)

theorem readout_ae (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (g : κ → Lp ℝ 2 μ) :
    (readout μ s b g : Ω → ℝ)=ᵐ[μ]
      fun ω => FourierDensity.sineOutput s b (fun k => g k ω) := by
  filter_upwards [sine_ae μ ((2:ℝ) • polynomial μ s b g),
    Lp.coeFn_smul (2:ℝ) (polynomial μ s b g),polynomial_ae μ s b g] with ω h1 h2 h3
  change sine μ ((2:ℝ) • polynomial μ s b g) ω= _
  rw [h1,h2]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h3]
  rfl

theorem readout_norm_sub_le (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (g h : κ → Lp ℝ 2 μ) :
    ‖readout μ s b g-readout μ s b h‖≤2*‖polynomial μ s b g-polynomial μ s b h‖ := by
  have hh := sine_norm_sub_le μ ((2:ℝ) • polynomial μ s b g) ((2:ℝ) • polynomial μ s b h)
  simpa only [readout,←smul_sub,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] using hh

theorem readout_continuous (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    Continuous (readout μ s b) := by
  exact (sine_continuous μ).comp ((polynomial_continuous μ s b).const_smul (2:ℝ))

variable (ν : Measure (κ → ℝ)) [IsFiniteMeasure ν]
variable (X : Ω → κ → ℝ) (hX : MeasurePreserving X μ ν)
variable (cols : κ → Lp ℝ 2 μ)
variable (hcols : ∀k, (cols k : Ω → ℝ)=ᵐ[μ] fun ω => X ω k)
include hcols

 

theorem pullback_readout (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    Lp.compMeasurePreserving X hX (FourierDensity.sineOutputVector ν s b)=
      readout μ s b cols := by
  apply Lp.ext
  have hc := ae_all_iff.mpr hcols
  have hr := hX.quasiMeasurePreserving.ae (FourierDensity.sineOutputVector_ae ν s b)
  filter_upwards [Lp.coeFn_compMeasurePreserving (FourierDensity.sineOutputVector ν s b) hX,
    hr,readout_ae μ s b cols,hc] with ω h1 h2 h3 h4
  rw [h1,h3]
  change FourierDensity.sineOutputVector ν s b (X ω)= _
  rw [h2]
  congr 1
  exact funext (fun k => (h4 k).symm)

 

theorem exists_robust_readout
    (hν : MeasurePreserving (fun g : κ → ℝ => -g) ν ν)
    (f : Lp ℝ 2 ν) (hf : ∀ᵐ g ∂ν, f (-g)= -f g)
    (hb : ∀ᵐ g ∂ν, |f g|≤1) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀g : κ → Lp ℝ 2 μ, (∀k, ‖g k-cols k‖<δ) →
        ‖readout μ s b g-Lp.compMeasurePreserving X hX f‖<ε := by
  obtain ⟨s,b,ha⟩ := FourierDensity.exists_sine_angle_approx ν hν f hf hb (half_pos hε)
  have ha' : ‖readout μ s b cols-Lp.compMeasurePreserving X hX f‖<ε/2 := by
    rw [←pullback_readout μ ν X hX cols hcols]
    rw [←map_sub,Lp.norm_compMeasurePreserving]
    exact ha
  have hc := (readout_continuous μ s b).continuousAt (x := cols)
  obtain ⟨δ,hδ,hdb⟩ := Metric.continuousAt_iff.mp hc (ε/2) (half_pos hε)
  refine ⟨s,b,δ,hδ,?_⟩
  intro g hg
  have hd : dist g cols<δ := (dist_pi_lt_iff hδ).mpr (fun k => by
    simpa only [dist_eq_norm] using hg k)
  calc
    _ ≤ ‖readout μ s b g-readout μ s b cols‖+
        ‖readout μ s b cols-Lp.compMeasurePreserving X hX f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [dist_eq_norm] using hdb hd) ha'
    _ = ε := add_halves ε

end TrigLp

namespace TrigLp
open MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {κ : Type*} [Fintype κ]
variable (μ : Measure Ω)

 

def inputMap (cols : κ → Lp ℝ 2 μ) (ω : Ω) : κ → ℝ := fun k => cols k ω

omit [Fintype κ] in
theorem measurable_inputMap (cols : κ → Lp ℝ 2 μ) : Measurable (inputMap μ cols) :=
  Measurable.of_eval (fun k => (Lp.stronglyMeasurable (cols k)).measurable)

def inputLaw (cols : κ → Lp ℝ 2 μ) : Measure (κ → ℝ) := μ.map (inputMap μ cols)

instance inputLaw_finite [IsFiniteMeasure μ] (cols : κ → Lp ℝ 2 μ) :
    IsFiniteMeasure (inputLaw μ cols) := inferInstanceAs (IsFiniteMeasure (μ.map _))

omit [Fintype κ] in
theorem inputMap_preserving (cols : κ → Lp ℝ 2 μ) :
    MeasurePreserving (inputMap μ cols) μ (inputLaw μ cols) :=
  (measurable_inputMap μ cols).measurePreserving μ

 

theorem inputLaw_symmetric (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (cols : κ → Lp ℝ 2 μ) (hc : ∀k, ∀ᵐ ω ∂μ, cols k (τ ω)= -cols k ω) :
    MeasurePreserving (fun g : κ → ℝ => -g) (inputLaw μ cols) (inputLaw μ cols) := by
  refine ⟨measurable_neg,?_⟩
  change (μ.map (inputMap μ cols)).map (fun g => -g)=μ.map (inputMap μ cols)
  rw [Measure.map_map measurable_neg (measurable_inputMap μ cols)]
  have he : (fun g : κ → ℝ => -g) ∘ inputMap μ cols =ᵐ[μ] inputMap μ cols ∘ τ := by
    filter_upwards [ae_all_iff.mpr hc] with ω hω
    exact funext fun k => (hω k).symm
  rw [Measure.map_congr he,←Measure.map_map (measurable_inputMap μ cols) hτ.measurable,hτ.map_eq]

 
theorem polynomial_odd (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (cols : κ → Lp ℝ 2 μ)
    (hc : ∀k, ∀ᵐ ω ∂μ, cols k (τ ω)= -cols k ω) :
    ∀ᵐ ω ∂μ, polynomial μ s b cols (τ ω)= -polynomial μ s b cols ω := by
  have ht := hτ.quasiMeasurePreserving.ae (polynomial_ae μ s b cols)
  filter_upwards [polynomial_ae μ s b cols,ht,ae_all_iff.mpr hc] with ω h1 h2 h3
  rw [h1,h2]
  have he : (fun k => cols k (τ ω))= -(fun k => cols k ω) := funext h3
  rw [he,FourierDensity.sinePolynomial_odd]

theorem readout_odd (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) (cols : κ → Lp ℝ 2 μ)
    (hc : ∀k, ∀ᵐ ω ∂μ, cols k (τ ω)= -cols k ω) :
    ∀ᵐ ω ∂μ, readout μ s b cols (τ ω)= -readout μ s b cols ω := by
  have ht := hτ.quasiMeasurePreserving.ae (readout_ae μ s b cols)
  filter_upwards [readout_ae μ s b cols,ht,ae_all_iff.mpr hc] with ω h1 h2 h3
  rw [h1,h2]
  have he : (fun k => cols k (τ ω))= -(fun k => cols k ω) := funext h3
  rw [he,FourierDensity.sineOutput_odd]

variable [IsFiniteMeasure μ]

 

theorem exists_robust_odd_operation (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (cols : κ → Lp ℝ 2 μ) (hc : ∀k, ∀ᵐ ω ∂μ, cols k (τ ω)= -cols k ω)
    (φ : (κ → ℝ) → ℝ) (hφ : MemLp φ 2 (inputLaw μ cols))
    (ho : ∀x, φ (-x)= -φ x) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀g : κ → Lp ℝ 2 μ, (∀k, ‖g k-cols k‖<δ) →
        ‖polynomial μ s b g-(hφ.comp_measurePreserving (inputMap_preserving μ cols)).toLp
          (φ ∘ inputMap μ cols)‖<ε := by
  let ν := inputLaw μ cols
  let f : Lp ℝ 2 ν := hφ.toLp φ
  have hν := inputLaw_symmetric μ τ hτ cols hc
  have hf : ∀ᵐ x ∂ν, f (-x)= -f x := by
    have hn := hν.quasiMeasurePreserving.ae hφ.coeFn_toLp
    filter_upwards [hφ.coeFn_toLp,hn] with x hx hnx
    change f x=φ x at hx
    change f (-x)=φ (-x) at hnx
    rw [hx,hnx,ho]
  have hcols (k : κ) : (cols k : Ω → ℝ)=ᵐ[μ] fun ω => inputMap μ cols ω k :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨s,b,δ,hδ,hd⟩ := exists_robust_local_approx μ ν (inputMap μ cols)
    (inputMap_preserving μ cols) cols hcols hν f hf hε
  refine ⟨s,b,δ,hδ,?_⟩
  intro g hg
  exact hd g hg

end TrigLp

namespace TrigLp
open MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {κ : Type*} [Fintype κ]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

 

theorem exists_robust_odd_readout (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (cols : κ → Lp ℝ 2 μ) (hc : ∀k, ∀ᵐ ω ∂μ, cols k (τ ω)= -cols k ω)
    (φ : (κ → ℝ) → ℝ) (hφ : MemLp φ 2 (inputLaw μ cols))
    (ho : ∀x, φ (-x)= -φ x) (hb : ∀x, |φ x|≤1) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀g : κ → Lp ℝ 2 μ, (∀k, ‖g k-cols k‖<δ) →
        ‖readout μ s b g-(hφ.comp_measurePreserving (inputMap_preserving μ cols)).toLp
          (φ ∘ inputMap μ cols)‖<ε := by
  let ν := inputLaw μ cols
  let f : Lp ℝ 2 ν := hφ.toLp φ
  have hν := inputLaw_symmetric μ τ hτ cols hc
  have hf : ∀ᵐ x ∂ν, f (-x)= -f x := by
    have hn := hν.quasiMeasurePreserving.ae hφ.coeFn_toLp
    filter_upwards [hφ.coeFn_toLp,hn] with x hx hnx
    change f x=φ x at hx
    change f (-x)=φ (-x) at hnx
    rw [hx,hnx,ho]
  have hb' : ∀ᵐ x ∂ν, |f x|≤1 := by
    filter_upwards [hφ.coeFn_toLp] with x hx
    change f x=φ x at hx
    rw [hx]
    exact hb x
  have hcols (k : κ) : (cols k : Ω → ℝ)=ᵐ[μ] fun ω => inputMap μ cols ω k :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨s,b,δ,hδ,hd⟩ := exists_robust_readout μ ν (inputMap μ cols)
    (inputMap_preserving μ cols) cols hcols hν f hf hb' hε
  exact ⟨s,b,δ,hδ,hd⟩

end TrigLp

end

end OAI
