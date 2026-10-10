import Mathlib
import OAI.Probability.IsingPerceptron.GaussianGibbs

namespace OAI

/-! Full Perturbation. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

abbrev FullTensorIndex (N : ℕ) := Σ j : Fin N, Fin (N^(j.val+1)-1+1)

def fullTensorEnumeration (N : ℕ) :
    Fin (Fintype.card (FullTensorIndex N)) ≃ FullTensorIndex N := (Fintype.equivFin _).symm

def tensorAmplitude (s : ℝ) (v : ℕ → ℝ) (j : ℕ) : ℝ := s*(1/2)^j*v j

def fullTensorCoefficient {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (x : Spins N) (i : Fin (Fintype.card (FullTensorIndex N))) : ℝ :=
  let a := fullTensorEnumeration N i
  tensorAmplitude s v (a.1.val+1)*tensorCoefficient hN (a.1.val+1) x a.2

def fullTensorEnergy {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (g : Fin (Fintype.card (FullTensorIndex N)) → ℝ) (x : Spins N) : ℝ :=
  ∑i,g i*fullTensorCoefficient hN s v x i

lemma fullTensorEnergy_eq {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (g : Fin (Fintype.card (FullTensorIndex N)) → ℝ) (x : Spins N) :
    fullTensorEnergy hN s v g x=
    ∑j : Fin N,tensorAmplitude s v (j.val+1)*
      tensorPerturbation hN (j.val+1) (fun a => g ((fullTensorEnumeration N).symm ⟨j,a⟩)) x := by
  unfold fullTensorEnergy fullTensorCoefficient
  conv_lhs =>
    arg 2
    ext i
    rw [show g i=g ((fullTensorEnumeration N).symm (fullTensorEnumeration N i)) from
      congrArg g ((fullTensorEnumeration N).symm_apply_apply i).symm]
  rw [(fullTensorEnumeration N).sum_comp
    (fun a => g ((fullTensorEnumeration N).symm a)*
      (tensorAmplitude s v (a.1.val+1)*tensorCoefficient hN (a.1.val+1) x a.2))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [tensorPerturbation,gaussianLinear,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

def fullTensorBound (N : ℕ) (s : ℝ) (v : ℕ → ℝ)
    (i : Fin (Fintype.card (FullTensorIndex N))) : ℝ :=
  let a := fullTensorEnumeration N i
  |tensorAmplitude s v (a.1.val+1)| * (1/sqrt N)^(a.1.val+1)

lemma fullTensorCoefficient_abs {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (x : Spins N) (i : Fin (Fintype.card (FullTensorIndex N))) :
    |fullTensorCoefficient hN s v x i|=fullTensorBound N s v i := by
  simp only [fullTensorCoefficient,fullTensorBound,abs_mul,tensorCoefficient_abs]

lemma fullTensorBound_squares {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ) :
    (∑i,fullTensorBound N s v i^2)=
    ∑j : Fin N,(tensorAmplitude s v (j.val+1))^2 := by
  unfold fullTensorBound
  rw [(fullTensorEnumeration N).sum_comp
    (fun a => (|tensorAmplitude s v (a.1.val+1)| * (1/sqrt N)^(a.1.val+1))^2)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simpa only using tensor_coordinate_squares hN (j.val+1) (tensorAmplitude s v (j.val+1))

theorem fullTensor_logPartition_variance {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (W : Spins N → ℝ) :
    variance (fun g => finiteLogPartition (fun x => W x+fullTensorEnergy hN s v g x))
      (Measure.pi (fun _ => gaussianReal 0 1))≤
      s^2*∑j : Fin N,(1/4)^(j.val+1)*(v (j.val+1))^2 := by
  have h := linearLogPartition_variance W (fullTensorCoefficient hN s v)
    (c:=fullTensorBound N s v) (fun x i => (fullTensorCoefficient_abs hN s v x i).le)
  rw [fullTensorBound_squares hN s v] at h
  have he : (∑j : Fin N,(tensorAmplitude s v (j.val+1))^2)=
      s^2*∑j : Fin N,(1/4)^(j.val+1)*(v (j.val+1))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [tensorAmplitude,mul_pow,← pow_mul]
    rw [Nat.mul_comm (j.val+1) 2,pow_mul]
    norm_num
    ring
  rw [he] at h
  exact h

variable {S R : Type*} [Fintype S] [Nonempty S] [MeasurableSpace R] [Nonempty R]

lemma linearLogPartition_bound {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    {M : ℝ} (hW : ∀x,|W x|≤M) {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i)
    (g : Fin n → ℝ) : |linearLogPartition W A g|≤M+∑i,c i*|g i| := by
  apply finite_log_average_abs
  intro x
  calc |W x+∑i,g i*A x i|≤|W x|+|∑i,g i*A x i| := abs_add_le _ _
    _ ≤ M+∑i,c i*|g i| := by
      apply add_le_add (hW x)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hc x i) (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem mixed_logPartition_variance {m n : ℕ} (μ : Fin m → Measure R)
    [∀i,IsProbabilityMeasure (μ i)] (W : (Fin m → R) → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (A : S → Fin n → ℝ)
    {M : ℝ} (hW : ∀r x,|W r x|≤M) {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i)
    (d : Fin m → ℝ) (hd : ∀i r r',(∀k,k≠i → r k=r' k) → ∀x,|W r x-W r' x|≤d i) :
    variance (fun p : (Fin n → ℝ) × (Fin m → R) => linearLogPartition (W p.2) A p.1)
      ((Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi μ)) ≤
      (∑i,c i^2)+(∑i,d i^2) := by
  let σ : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let ν : Measure (Fin m → R) := Measure.pi μ
  let F : (Fin n → ℝ) × (Fin m → R) → ℝ := fun p => linearLogPartition (W p.2) A p.1
  let B : (Fin n → ℝ) → ℝ := fun g => M+∑i,c i*|g i|
  have hmF : Measurable F := by
    unfold F linearLogPartition finiteLogPartition
    fun_prop
  have hiB : MemLp B 2 σ := by
    exact (memLp_const M).add (memLp_finsetSum _ (fun i _ =>
      ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).abs.const_mul (c i)))
  have hFB (p) : |F p|≤B p.1 := linearLogPartition_bound (W p.2) A (hW p.2) hc p.1
  have hF : MemLp F 2 (σ.prod ν) := by
    apply (hiB.comp_measurePreserving measurePreserving_fst).mono hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      simp only [Function.comp_apply,Real.norm_eq_abs]
      exact (hFB p).trans (le_abs_self _)
  have hslice (r : Fin m → R) : MemLp (fun g => F (g,r)) 2 σ :=
    linearLogPartition_memLp (W r) A hc
  let G : (Fin m → R) → ℝ := fun r => ∫g,F (g,r) ∂σ
  have hmG : Measurable G := hmF.stronglyMeasurable.integral_prod_left'.measurable
  have hGB (r : Fin m → R) : |G r|≤∫g,B g ∂σ := by
    calc |G r|≤∫g,|F (g,r)| ∂σ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun g => F (g,r))
      _ ≤ ∫g,B g ∂σ := integral_mono ((hslice r).integrable (by norm_num)).abs
        (hiB.integrable (by norm_num)) (fun g => hFB (g,r))
  have hG : MemLp G 2 ν := bounded_memLp ν hmG hGB
  have hCG : ∀i r r',(∀k,k≠i → r k=r' k) → |G r-G r'|≤d i := by
    intro i r r' hrr
    dsimp only [G]
    rw [← integral_sub ((hslice r).integrable (by norm_num)) ((hslice r').integrable (by norm_num))]
    apply bounded_mean σ
    intro g
    apply finite_log_average_difference
    intro x
    simpa only [add_sub_add_right_eq_sub] using hd i r r' hrr x
  have hv := variance_prod_le_of_slices σ ν hF hslice hG
    (fun r => linearLogPartition_variance (W r) A hc)
  have hg := variance_pi_bounded_differences μ hmG hGB d hCG
  exact hv.trans (add_le_add le_rfl hg)

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

abbrev PatternRows (M N : ℕ) := Fin M → Fin N → ℝ

def rowEvaluation {M N : ℕ} (g : PatternRows M N) (a : Fin M) (x : Spins N) : ℝ :=
  (∑i,g a i*spin x i)/sqrt N

def patternEnergy {M N : ℕ} (f : ℝ → ℝ) (g : PatternRows M N) (x : Spins N) : ℝ :=
  ∑a,f (rowEvaluation g a x)

def perturbationScale (N : ℕ) : ℝ := (N:ℝ)^((3:ℝ)/8)

abbrev PerturbedDisorder (M N : ℕ) :=
  (Fin (Fintype.card (FullTensorIndex N)) → ℝ) × PatternRows M N

def perturbedDisorderLaw (M N : ℕ) : Measure (PerturbedDisorder M N) :=
  (Measure.pi (fun _ => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)))

def perturbedLogPartition {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (p : PerturbedDisorder M N) : ℝ :=
  linearLogPartition (patternEnergy f p.2) (fullTensorCoefficient hN s v) p.1

def omittedPressure (α : ℝ) {N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (v : ℕ → ℝ)
    (p : PerturbedDisorder (patternCount α N-2) N) : ℝ :=
  perturbedLogPartition hN f (perturbationScale N) v p/N

lemma patternEnergy_bound {M N : ℕ} {f : ℝ → ℝ} {C : ℝ} (hC : ∀z,|f z|≤C)
    (g : PatternRows M N) (x : Spins N) : |patternEnergy f g x|≤M*C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc (∑a : Fin M,|f (rowEvaluation g a x)|)≤∑_a : Fin M,C :=
      Finset.sum_le_sum (fun a _ => hC _)
    _ = _ := by simp

lemma patternEnergy_row_difference {M N : ℕ} {f : ℝ → ℝ} {C : ℝ} (hC : ∀z,|f z|≤C)
    (a : Fin M) (g g' : PatternRows M N) (heq : ∀b,b≠a → g b=g' b) (x : Spins N) :
    |patternEnergy f g x-patternEnergy f g' x|≤2*C := by
  unfold patternEnergy
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single a]
  · exact (abs_sub _ _).trans (by linarith [hC (rowEvaluation g a x),hC (rowEvaluation g' a x)])
  · intro b _ hba
    have he : rowEvaluation g b x=rowEvaluation g' b x := by unfold rowEvaluation; rw [heq b hba]
    rw [he,sub_self]
  · simp

lemma perturbedLogPartition_variance {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (s : ℝ) (v : ℕ → ℝ) :
    variance (perturbedLogPartition (M:=M) hN f s v) (perturbedDisorderLaw M N) ≤
    (∑j : Fin N,(tensorAmplitude s v (j.val+1))^2)+4*M*C^2 := by
  have h := mixed_logPartition_variance
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (patternEnergy f) (fun x => by unfold patternEnergy rowEvaluation; fun_prop)
    (fullTensorCoefficient hN s v) (patternEnergy_bound hC)
    (fun x i => (fullTensorCoefficient_abs hN s v x i).le)
    (fun _ => 2*C) (fun a g g' heq x => patternEnergy_row_difference hC a g g' heq x)
  rw [fullTensorBound_squares hN s v] at h
  change variance (fun p : PerturbedDisorder M N => linearLogPartition (patternEnergy f p.2) (fullTensorCoefficient hN s v) p.1) (perturbedDisorderLaw M N) ≤ _
  simpa only [perturbedDisorderLaw,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,show (M:ℝ)*(2*C)^2=4*M*C^2 by ring] using h

lemma quarter_sum_le (N : ℕ) : (∑j : Fin N,(1/4:ℝ)^(j.val+1))≤1/3 := by
  have h := geom_sum_mul (1/4:ℝ) N
  have hp : 0≤(1/4:ℝ)^N := by positivity
  have he : (∑j : Fin N,(1/4:ℝ)^(j.val+1))=
      (∑j ∈ Finset.range N,(1/4:ℝ)^j)*(1/4) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (1/4:ℝ)^(j+1)) N]
    simp only [pow_succ,Finset.sum_mul]
  rw [he]
  nlinarith

lemma totalTensor_variance_uniform {N : ℕ} (s : ℝ) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Set.Icc (1/2:ℝ) (5/2)) :
    (∑j : Fin N,(tensorAmplitude s v (j.val+1))^2)≤(25/12)*s^2 := by
  have he (j : Fin N) : (tensorAmplitude s v (j.val+1))^2=
      s^2*(1/4)^(j.val+1)*(v (j.val+1))^2 := by
    simp only [tensorAmplitude,mul_pow,← pow_mul]
    rw [Nat.mul_comm (j.val+1) 2,pow_mul]
    norm_num
  have hb : (∑j : Fin N,(tensorAmplitude s v (j.val+1))^2)≤
      s^2*(25/4)*(∑j : Fin N,(1/4:ℝ)^(j.val+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [he]
    have hv' : (v (j.val+1))^2≤25/4 := by
      have hx := (sq_le_sq₀ (by linarith [(hv j).1] : 0≤v (j.val+1)) (by norm_num : (0:ℝ)≤5/2)).mpr (hv j).2
      norm_num at hx
      exact hx
    calc s^2*(1/4)^(j.val+1)*(v (j.val+1))^2 ≤ s^2*(1/4)^(j.val+1)*(25/4) :=
        mul_le_mul_of_nonneg_left hv' (by positivity)
      _ = _ := by ring
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (quarter_sum_le N) (by positivity : 0 ≤ (s^2*(25/4)))])

lemma perturbationScale_sq_le {N : ℕ} (hN : 0<N) : (perturbationScale N)^2≤N := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  unfold perturbationScale
  rw [← rpow_natCast,← rpow_mul (Nat.cast_nonneg N)]
  norm_num
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNr (by norm_num : (3:ℝ)/4≤1)

theorem omittedPressure_variance (α : ℝ) (hα : 0≤α) {N : ℕ} (hN : 0<N)
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Set.Icc (1/2:ℝ) (5/2)) :
    variance (omittedPressure α hN f v) (perturbedDisorderLaw (patternCount α N-2) N) ≤
      (4*α*C^2+25/12)/N := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hM : (patternCount α N-2:ℕ)≤patternCount α N := Nat.sub_le _ _
  have hMr : ((patternCount α N-2:ℕ):ℝ)≤α*N :=
    (Nat.cast_le.mpr hM).trans (Nat.floor_le (mul_nonneg hα hNr.le))
  have hV := perturbedLogPartition_variance (M:=patternCount α N-2) hN hf hC (perturbationScale N) v
  have hT := totalTensor_variance_uniform (perturbationScale N) v hv
  have hS := perturbationScale_sq_le hN
  have hU : variance (perturbedLogPartition (M:=patternCount α N-2) hN f (perturbationScale N) v)
      (perturbedDisorderLaw (patternCount α N-2) N)≤N*(4*α*C^2+25/12) := by
    have hrow := mul_le_mul_of_nonneg_right hMr (sq_nonneg C)
    nlinarith
  have he : omittedPressure α hN f v=fun p =>
      perturbedLogPartition hN f (perturbationScale N) v p*(N:ℝ)⁻¹ := by
    funext p
    exact div_eq_mul_inv _ _
  rw [he,variance_mul_const]
  calc _ ≤ (N*(4*α*C^2+25/12))*((N:ℝ)⁻¹)^2 :=
      mul_le_mul_of_nonneg_right hU (sq_nonneg _)
    _ = _ := by field_simp

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology
variable {S : Type*} [Fintype S] [Nonempty S]

lemma finiteLogPartition_derivative {H : ℝ → S → ℝ} {HD : S → ℝ} {t : ℝ}
    (hH : ∀x,HasDerivAt (fun u => H u x) (HD x) t) :
    HasDerivAt (fun u => finiteLogPartition (H u)) (finiteGibbs (H t) HD) t := by
  have hz := HasDerivAt.fun_sum (u:=Finset.univ) (fun x _ => (hH x).exp)
  have hc : (Fintype.card S:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply ((hz.div_const (Fintype.card S:ℝ)).log (finite_exp_average_pos (H t)).ne').congr_deriv
  simp only [finiteGibbs]
  field_simp

lemma finiteGibbs_nonneg (H V : S → ℝ) (hV : ∀x,0≤V x) : 0≤finiteGibbs H V := by
  apply div_nonneg _ (finiteGibbs_den_pos H).le
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (exp_pos _).le (hV x))

lemma finiteGibbs_centered_square (H V : S → ℝ) :
    finiteGibbs H (fun x => (V x-finiteGibbs H V)^2)=
      finiteGibbs H (fun x => (V x)^2)-(finiteGibbs H V)^2 := by
  have he (x : S) : (V x-finiteGibbs H V)^2=
      (V x)^2-2*finiteGibbs H V*V x+(finiteGibbs H V)^2 := by ring
  simp only [he,finiteGibbs_add,finiteGibbs_sub,finiteGibbs_const_mul,finiteGibbs_const]
  ring

lemma gaussian_parameter_derivative {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (g : Fin (m+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => finiteLogPartition (gaussianGibbsH W A u g))
      (finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)) t := by
  apply finiteLogPartition_derivative
  intro x
  simpa only [gaussianGibbsH,Pi.add_apply,id_eq,zero_add,one_mul] using
    (hasDerivAt_const t (W x)).fun_add ((hasDerivAt_id t).mul_const (gaussianLinear A g x))

lemma gaussian_parameter_thermal_derivative {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (g : Fin (m+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => finiteGibbs (gaussianGibbsH W A u g) (gaussianLinear A g))
      (finiteGibbs (gaussianGibbsH W A t g) (fun x =>
        (gaussianLinear A g x-finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g))^2)) t := by
  have hd := finiteGibbs_derivative (H:=fun u => gaussianGibbsH W A u g)
    (V:=fun _ => gaussianLinear A g)
    (fun x => (hasDerivAt_const t (W x)).fun_add ((hasDerivAt_id t).mul_const (gaussianLinear A g x)))
    (fun x => hasDerivAt_const t (gaussianLinear A g x))
  rw [finiteGibbs_centered_square]
  convert hd using 1; simp only [zero_add,one_mul,pow_two]

def gaussianLinearBound {n : ℕ} (A : S → Fin n → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑i,|g i| * ∑x,|A x i|

omit [Nonempty S] in
lemma gaussianLinearBound_memLp {n : ℕ} (A : S → Fin n → ℝ) :
    MemLp (gaussianLinearBound A) 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  exact memLp_finsetSum _ (fun i _ =>
    ((memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).abs.mul_const _)

omit [Nonempty S] in
lemma gaussianLinear_abs_bound {m : ℕ} (A : S → Fin (m+1) → ℝ)
    (g : Fin (m+1) → ℝ) (x : S) : |gaussianLinear A g x|≤gaussianLinearBound A g := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (finiteFunction_bound (fun x => A x i) x) (abs_nonneg _)

omit [Nonempty S] in
lemma gaussianLinearBound_nonneg {n : ℕ} (A : S → Fin n → ℝ) (g : Fin n → ℝ) :
    0≤gaussianLinearBound A g := Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

lemma gaussian_logPartition_integrable {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    Integrable (fun g => finiteLogPartition (gaussianGibbsH W A t g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have he : (fun g => finiteLogPartition (gaussianGibbsH W A t g))=
      linearLogPartition W (fun x i => t*A x i) := by
    funext g
    congr 1
    funext x
    simp only [gaussianGibbsH,gaussianLinear,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact (linearLogPartition_memLp W _ (fun x i => finiteFunction_bound (fun x => t*A x i) x)).integrable (by norm_num)

theorem mean_gaussian_parameter_derivative {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∫g,finiteLogPartition (gaussianGibbsH W A u g)
      ∂Measure.pi (fun _ => gaussianReal 0 1))
      (∫g,finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Set.univ)
    (bound:=gaussianLinearBound A) (F':=fun u g =>
      finiteGibbs (gaussianGibbsH W A u g) (gaussianLinear A g)) (Filter.univ_mem)
    (Eventually.of_forall (fun u => (show Measurable (fun g =>
      finiteLogPartition (gaussianGibbsH W A u g)) from by
        unfold finiteLogPartition gaussianGibbsH gaussianLinear; fun_prop).aestronglyMeasurable))
    (gaussian_logPartition_integrable W A t)
    ((show Measurable (fun g => finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)) from by
      unfold finiteGibbs gaussianGibbsH gaussianLinear; fun_prop).aestronglyMeasurable)
    (ae_of_all _ fun g u _ => by
      simpa only [Real.norm_eq_abs] using
        (finiteGibbs_abs (gaussianGibbsH W A u g) (gaussianLinear A g) (gaussianLinear_abs_bound A g)))
    ((gaussianLinearBound_memLp A).integrable (by norm_num))
    (ae_of_all _ fun g u _ => gaussian_parameter_derivative W A g u)).2

def gaussianThermalVariance {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (t : ℝ) (g : Fin (m+1) → ℝ) : ℝ :=
  finiteGibbs (gaussianGibbsH W A t g) (fun x =>
    (gaussianLinear A g x-finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g))^2)

lemma gaussianThermalVariance_nonneg {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (t : ℝ) (g : Fin (m+1) → ℝ) : 0≤gaussianThermalVariance W A t g :=
  finiteGibbs_nonneg _ _ (fun _ => sq_nonneg _)

lemma gaussianThermalVariance_bound {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (t : ℝ) (g : Fin (m+1) → ℝ) :
    |gaussianThermalVariance W A t g|≤(gaussianLinearBound A g)^2 := by
  rw [abs_of_nonneg (gaussianThermalVariance_nonneg W A t g)]
  unfold gaussianThermalVariance
  rw [finiteGibbs_centered_square]
  have hb := finiteGibbs_abs (gaussianGibbsH W A t g) (fun x => (gaussianLinear A g x)^2)
    (C:=(gaussianLinearBound A g)^2) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _),← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (gaussianLinear_abs_bound A g x) 2)
  linarith [le_abs_self (finiteGibbs (gaussianGibbsH W A t g) (fun x => (gaussianLinear A g x)^2)),
    sq_nonneg (finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g))]

omit [Nonempty S] in
lemma gaussianThermalVariance_measurable {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ) :
    Measurable (fun p : ℝ × (Fin (m+1) → ℝ) => gaussianThermalVariance W A p.1 p.2) := by
  unfold gaussianThermalVariance finiteGibbs gaussianGibbsH gaussianLinear
  fun_prop

lemma gaussian_mean_energy_integrable {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    Integrable (fun g => finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  apply ((gaussianLinearBound_memLp A).integrable (by norm_num)).mono'
    (show AEStronglyMeasurable (fun g => finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)) _ from
      (by unfold finiteGibbs gaussianGibbsH gaussianLinear; fun_prop : Measurable _).aestronglyMeasurable)
  exact ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using
    (finiteGibbs_abs _ _ (gaussianLinear_abs_bound A g))

theorem mean_gaussian_thermal_derivative {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∫g,finiteGibbs (gaussianGibbsH W A u g) (gaussianLinear A g)
      ∂Measure.pi (fun _ => gaussianReal 0 1))
      (∫g,gaussianThermalVariance W A t g ∂Measure.pi (fun _ => gaussianReal 0 1)) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Set.univ)
    (bound:=fun g => (gaussianLinearBound A g)^2) (F':=gaussianThermalVariance W A) Filter.univ_mem
    (Eventually.of_forall (fun u => (show Measurable (fun g =>
      finiteGibbs (gaussianGibbsH W A u g) (gaussianLinear A g)) from by
        unfold finiteGibbs gaussianGibbsH gaussianLinear; fun_prop).aestronglyMeasurable))
    (gaussian_mean_energy_integrable W A t)
    (((gaussianThermalVariance_measurable W A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun g u _ => by simpa only [Real.norm_eq_abs] using gaussianThermalVariance_bound W A u g)
    ((gaussianLinearBound_memLp A).integrable_sq)
    (ae_of_all _ fun g u _ => gaussian_parameter_thermal_derivative W A g u)).2

omit [Fintype S] [Nonempty S] in
lemma coefficient_cov_bound {n : ℕ} (A : S → Fin n → ℝ) {c : Fin n → ℝ}
    (hc : ∀x i,|A x i|≤c i) (x y : S) : |∑i,A x i*A y i|≤∑i,c i^2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,pow_two]
  exact mul_le_mul (hc x i) (hc y i) (abs_nonneg _) ((abs_nonneg _).trans (hc x i))

theorem gaussian_mean_energy_bound {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    {c : Fin (m+1) → ℝ} (hc : ∀x i,|A x i|≤c i) (t : ℝ) :
    |∫g,finiteGibbs (gaussianGibbsH W A t g) (gaussianLinear A g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)|≤2*|t| *(∑i,c i^2) := by
  have he := gaussianGibbs_ibp W (fun _ => 1) A A t
  simp only [one_mul] at he
  rw [he]
  apply bounded_mean
  intro g
  rw [abs_mul]
  have hd := finiteGibbs_abs (gaussianGibbsH W A t g) (fun x => ∑i,A x i*A x i)
    (fun x => coefficient_cov_bound A hc x x)
  have hr := finiteGibbs_abs (gaussianGibbsH W A t g)
    (fun x => finiteGibbs (gaussianGibbsH W A t g) (fun y => ∑i,A x i*A y i))
    (fun x => finiteGibbs_abs _ _ (fun y => coefficient_cov_bound A hc x y))
  have hb := (abs_sub _ _).trans (add_le_add hd hr)
  calc |t| * |finiteGibbs (gaussianGibbsH W A t g) (fun x => ∑i,A x i*A x i)-
      finiteGibbsPair (gaussianGibbsH W A t g) (fun x y => ∑i,A x i*A y i)| ≤
      |t| * ((∑i,c i^2)+(∑i,c i^2)) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval
variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma meanThermal_measurable {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ) :
    Measurable (fun t => ∫g,gaussianThermalVariance W A t g
      ∂Measure.pi (fun _ => gaussianReal 0 1)) :=
  (gaussianThermalVariance_measurable W A).stronglyMeasurable.integral_prod_right.measurable

lemma meanThermal_intervalIntegrable {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => ∫g,gaussianThermalVariance W A t g
      ∂Measure.pi (fun _ => gaussianReal 0 1)) volume a b := by
  let μ : Measure (Fin (m+1) → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  apply (intervalIntegrable_const (c:=∫g,(gaussianLinearBound A g)^2 ∂μ)).mono_fun
    (meanThermal_measurable W A).aestronglyMeasurable
  filter_upwards [] with t
  simp only [Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  calc |∫g,gaussianThermalVariance W A t g ∂μ| ≤
      ∫g,|gaussianThermalVariance W A t g| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (gaussianThermalVariance W A t)
    _ ≤ ∫g,(gaussianLinearBound A g)^2 ∂μ := by
      have hi : Integrable (gaussianThermalVariance W A t) μ :=
        ((gaussianLinearBound_memLp A).integrable_sq).mono'
          (((gaussianThermalVariance_measurable W A).comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
          (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using gaussianThermalVariance_bound W A t g)
      exact integral_mono hi.abs (gaussianLinearBound_memLp A).integrable_sq
        (gaussianThermalVariance_bound W A t)

theorem gaussian_thermal_integral {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    {c : Fin (m+1) → ℝ} (hc : ∀x i,|A x i|≤c i) :
    (∫t in (1:ℝ)..2,∫g,gaussianThermalVariance W A t g
      ∂Measure.pi (fun _ => gaussianReal 0 1))≤6*∑i,c i^2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => mean_gaussian_thermal_derivative W A t)
    (meanThermal_intervalIntegrable W A 1 2)]
  have h1 := gaussian_mean_energy_bound W A hc 1
  have h2 := gaussian_mean_energy_bound W A hc 2
  norm_num at h1 h2
  have hsub := abs_sub
    (∫g,finiteGibbs (gaussianGibbsH W A 2 g) (gaussianLinear A g) ∂Measure.pi (fun _ => gaussianReal 0 1))
    (∫g,finiteGibbs (gaussianGibbsH W A 1 g) (gaussianLinear A g) ∂Measure.pi (fun _ => gaussianReal 0 1))
  linarith [le_abs_self
    ((∫g,finiteGibbs (gaussianGibbsH W A 2 g) (gaussianLinear A g) ∂Measure.pi (fun _ => gaussianReal 0 1))-
    (∫g,finiteGibbs (gaussianGibbsH W A 1 g) (gaussianLinear A g) ∂Measure.pi (fun _ => gaussianReal 0 1)))]

theorem tensor_thermal_integral {N : ℕ} (hN : 0<N) (j : ℕ) (W : Spins N → ℝ) :
    (∫t in (1:ℝ)..2,∫g,gaussianThermalVariance W (tensorCoefficient hN j) t g
      ∂Measure.pi (fun _ => gaussianReal 0 1))≤6 := by
  have h := gaussian_thermal_integral W (tensorCoefficient hN j)
    (c:=fun _ => (1/sqrt N)^j) (fun x i => (tensorCoefficient_abs hN j x i).le)
  have hs : (∑_i : Fin (N^j-1+1),((1/sqrt N)^j)^2)=1 := by
    simpa only [abs_one,one_mul,one_pow] using tensor_coordinate_squares hN j 1
  rw [hs,mul_one] at h
  exact h

omit [Nonempty S] in
lemma gaussianThermalVariance_scaled {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (u t : ℝ) (g : Fin (m+1) → ℝ) :
    gaussianThermalVariance W (fun x i => t*A x i) u g=
      t^2*gaussianThermalVariance W A (u*t) g := by
  have he (x : S) : gaussianLinear (fun x i => t*A x i) g x=t*gaussianLinear A g x := by
    unfold gaussianLinear
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hH : gaussianGibbsH W (fun x i => t*A x i) u g=gaussianGibbsH W A (u*t) g := by
    funext x
    change W x+u*gaussianLinear (fun x i => t*A x i) g x=W x+(u*t)*gaussianLinear A g x
    rw [he]
    ring
  unfold gaussianThermalVariance
  rw [hH]
  have hef : gaussianLinear (fun x i => t*A x i) g = fun x => t*gaussianLinear A g x := funext he
  rw [hef,finiteGibbs_const_mul]
  have hs (x : S) : (t*gaussianLinear A g x-t*finiteGibbs (gaussianGibbsH W A (u*t) g) (gaussianLinear A g))^2=
      t^2*(gaussianLinear A g x-finiteGibbs (gaussianGibbsH W A (u*t) g) (gaussianLinear A g))^2 := by ring
  simp only [hs,finiteGibbs_const_mul]

theorem tensor_scaled_thermal_integral {N : ℕ} (hN : 0<N) (j : ℕ) (W : Spins N → ℝ)
    (t : ℝ) (ht : t≠0) :
    (∫u in (1:ℝ)..2,∫g,gaussianThermalVariance W (tensorCoefficient hN j) (u*t) g
      ∂Measure.pi (fun _ => gaussianReal 0 1))≤6 := by
  have h := gaussian_thermal_integral W (fun x i => t*tensorCoefficient hN j x i)
    (c:=fun _ => |t| * (1/sqrt N)^j) (fun x i => by rw [abs_mul,tensorCoefficient_abs])
  simp only [gaussianThermalVariance_scaled,integral_const_mul,intervalIntegral.integral_const_mul,
    tensor_coordinate_squares hN j t] at h
  rw [mul_comm 6 (t^2)] at h
  nlinarith [sq_pos_of_ne_zero ht]

end IsingPerceptron.Main

end

end OAI
