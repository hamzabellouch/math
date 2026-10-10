import Mathlib
import OAI.Probability.IsingPerceptron.ConvexFluctuation

namespace OAI

/-! Actual Quenched. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval

variable {S R : Type*} [Fintype S] [Nonempty S] [MeasurableSpace R] [Nonempty R]

def blockEnergy {k n : ℕ} (W : (Fin n → R) → S → ℝ) (B A : S → Fin k → ℝ)
    (u : ℝ) (p : (Fin k → ℝ) × (Fin n → R)) : ℝ :=
  finiteGibbs (fun x => W p.2 x+∑i,p.1 i*(B x i+u*A x i)) (fun x => ∑i,p.1 i*A x i)

theorem block_quenched_integral {k n : ℕ} (hk : 0<k)
    (ν : Fin n → Measure R) [∀i,IsProbabilityMeasure (ν i)]
    (W : (Fin n → R) → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin k → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {M : ℝ} (hW : ∀r x,|W r x|≤M)
    {a b : Fin k → ℝ} (ha : ∀x i,|A x i|≤a i)
    (hb : ∀u ∈ Icc (1/2:ℝ) (5/2),∀x i,|B x i+u*A x i|≤b i)
    (d : Fin n → ℝ) (hd : ∀i r r',(∀l,l≠i → r l=r' l) → ∀x,|W r x-W r' x|≤d i)
    {η : ℝ} (hη : 0<η) (hη' : η≤1/2) :
    (∫u in (1:ℝ)..2,∫p,|blockEnergy W B A u p-
        ∫q,blockEnergy W B A u q ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi ν)|
        ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi ν))≤
      4*sqrt ((∑i,b i^2)+(∑i,d i^2))/η+20*η*(∑i,a i^2) := by
  cases k with
  | zero => omega
  | succ m =>
    have he (u : ℝ) (p) : blockEnergy W B A u p=affineEnergy W B A u p := by
      unfold blockEnergy affineEnergy
      rw [affineHamiltonian_eq]
      congr 1
      funext x
      change W p.2 x+(∑i,p.1 i*(B x i+u*A x i))=W p.2 x+1*(∑i,p.1 i*(B x i+u*A x i))
      rw [one_mul]
    simp only [he]
    exact orthogonal_block_quenched_integral ν W hmW B A hAB hW ha hb d hd hη hη'

def selectedParameter (j : ℕ) : ℕ → ℝ := fun k => if k=j then 1 else 0

lemma fullTensorCoefficient_update {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (x : Spins N) (i : Fin (Fintype.card (FullTensorIndex N))) :
    fullTensorCoefficient hN s (Function.update v (j.val+1) u) x i=
      fullTensorCoefficient hN s (Function.update v (j.val+1) 0) x i+
      u*fullTensorCoefficient hN s (selectedParameter (j.val+1)) x i := by
  classical
  unfold fullTensorCoefficient tensorAmplitude selectedParameter
  by_cases h : (fullTensorEnumeration N i).1.val+1=j.val+1
  · simp only [h,Function.update_self,ite_true,mul_zero,zero_mul,mul_one,zero_add]; ring
  · simp only [Function.update_of_ne h,ite_eq_right h,mul_zero,zero_mul,add_zero]

lemma fullTensorCoefficient_disjoint {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ) (j : Fin N)
    (x y : Spins N) :
    (∑i,fullTensorCoefficient hN s (selectedParameter (j.val+1)) x i*
      fullTensorCoefficient hN s (Function.update v (j.val+1) 0) y i)=0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  unfold fullTensorCoefficient tensorAmplitude selectedParameter
  by_cases h : (fullTensorEnumeration N i).1.val+1=j.val+1
  · simp only [h,Function.update_self,mul_zero,zero_mul]
  · simp only [ite_eq_right h,mul_zero,zero_mul]

lemma selectedTensorBound_squares {N : ℕ} (hN : 0<N) (s : ℝ) (j : Fin N) :
    (∑i,fullTensorBound N s (selectedParameter (j.val+1)) i^2)=(s*(1/2)^(j.val+1))^2 := by
  classical
  rw [fullTensorBound_squares hN]
  rw [Finset.sum_eq_single j]
  · simp [tensorAmplitude,selectedParameter]
  · intro k _ hkj
    have h : k.val+1≠j.val+1 := by intro he; exact hkj (Fin.ext (by omega))
    simp only [tensorAmplitude,selectedParameter,ite_eq_right h,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · simp

lemma fullTensorCard_pos {N : ℕ} (hN : 0<N) : 0<Fintype.card (FullTensorIndex N) := by
  have hpow : 0<N^(0+1) := pow_pos hN _
  let a : FullTensorIndex N := ⟨⟨0,hN⟩,⟨0,by omega⟩⟩
  exact Fintype.card_pos_iff.mpr ⟨a⟩

def selectedTensorEnergy {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) : ℝ :=
  finiteGibbs (fun x => patternEnergy f p.2 x+fullTensorEnergy hN s (Function.update v (j.val+1) u) p.1 x)
    (fullTensorEnergy hN s (selectedParameter (j.val+1)) p.1)

lemma selectedTensorEnergy_eq_block {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) :
    selectedTensorEnergy hN f s v j u p=blockEnergy (patternEnergy f)
      (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
      (fullTensorCoefficient hN s (selectedParameter (j.val+1))) u p := by
  unfold selectedTensorEnergy blockEnergy fullTensorEnergy
  congr 1
  funext x
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg (p.1 i * ·) (fullTensorCoefficient_update hN s v j u x i))

theorem selectedTensor_quenched_integral {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (s : ℝ) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2)) (j : Fin N)
    {η : ℝ} (hη : 0<η) (hη' : η≤1/2) :
    (∫u in (1:ℝ)..2,∫p,|selectedTensorEnergy hN f s v j u p-
      ∫q,selectedTensorEnergy hN f s v j u q ∂perturbedDisorderLaw M N|
      ∂perturbedDisorderLaw M N)≤
      4*sqrt ((25/12)*s^2+4*M*C^2)/η+20*η*(s*(1/2)^(j.val+1))^2 := by
  classical
  have h := block_quenched_integral (fullTensorCard_pos hN)
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (patternEnergy f) (fun x => by unfold patternEnergy rowEvaluation; fun_prop)
    (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
    (fullTensorCoefficient hN s (selectedParameter (j.val+1)))
    (fullTensorCoefficient_disjoint hN s v j) (patternEnergy_bound hC)
    (a:=fullTensorBound N s (selectedParameter (j.val+1)))
    (fun x i => (fullTensorCoefficient_abs hN s (selectedParameter (j.val+1)) x i).le)
    (b:=fullTensorBound N s (fun _ => 5/2)) ?_
    (fun _ => 2*C) (fun a g g' heq x => patternEnergy_row_difference hC a g g' heq x) hη hη'
  · simp only [← selectedTensorEnergy_eq_block,selectedTensorBound_squares hN,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    apply h.trans
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ hη.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
    apply Real.sqrt_le_sqrt
    rw [fullTensorBound_squares hN]
    have hT := totalTensor_variance_uniform (N:=N) s (fun _ => 5/2) (fun _ => by constructor <;> norm_num)
    nlinarith
  · intro u hu x i
    rw [← fullTensorCoefficient_update,fullTensorCoefficient_abs]
    unfold fullTensorBound tensorAmplitude
    simp only [abs_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have ht : Function.update v (j.val+1) u ((fullTensorEnumeration N i).1.val+1)∈Icc (1/2:ℝ) (5/2) := by
      by_cases hh : (fullTensorEnumeration N i).1.val+1=j.val+1
      · simpa only [hh,Function.update_self] using hu
      · simpa only [Function.update_of_ne hh] using hv (fullTensorEnumeration N i).1
    rw [abs_of_nonneg (by linarith [ht.1] : 0≤Function.update v (j.val+1) u ((fullTensorEnumeration N i).1.val+1))]
    norm_num
    exact ht.2

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval
variable {S R : Type*} [Fintype S] [Nonempty S] [MeasurableSpace R]

lemma affine_mean_thermal_intervalIntegrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    IntervalIntegrable (fun u => ∫p,affineThermal W B A u p ∂affineDisorderLaw m ν) volume 1 2 := by
  let μ := affineDisorderLaw m ν
  have hiL : Integrable (fun p => (gaussianLinearBound A p.1)^2) μ :=
    ((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable_sq
  apply (intervalIntegrable_const (c:=∫p,(gaussianLinearBound A p.1)^2 ∂μ)).mono_fun
    (affineThermal_measurable W hmW B A).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [] with u
  simp only [Real.norm_eq_abs]
  calc _ ≤ ∫p,|affineThermal W B A u p| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (affineThermal W B A u)
    _ ≤ ∫p,(gaussianLinearBound A p.1)^2 ∂μ := integral_mono
      (affineThermal_integrable ν W hmW B A u).abs hiL (affineThermal_bound W B A u)
    _ ≤ _ := le_abs_self _

theorem affine_mean_thermal_integral {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin (m+1) → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {c : Fin (m+1) → ℝ} (hc : ∀x i,|A x i|≤c i) :
    (∫u in (1:ℝ)..2,∫p,affineThermal W B A u p ∂affineDisorderLaw m ν)≤6*∑i,c i^2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => mean_affineEnergy_derivative ν W hmW B A u)
    (affine_mean_thermal_intervalIntegrable ν W hmW B A)]
  have h1 := affine_mean_energy_bound ν W hmW B A hAB hc 1
  have h2 := affine_mean_energy_bound ν W hmW B A hAB hc 2
  norm_num at h1 h2
  linarith [le_abs_self (∫p,affineEnergy W B A 2 p ∂affineDisorderLaw m ν),
    neg_le_abs (∫p,affineEnergy W B A 1 p ∂affineDisorderLaw m ν)]

def blockThermal {k n : ℕ} (W : (Fin n → R) → S → ℝ) (B A : S → Fin k → ℝ)
    (u : ℝ) (p : (Fin k → ℝ) × (Fin n → R)) : ℝ :=
  finiteGibbs (fun x => W p.2 x+∑i,p.1 i*(B x i+u*A x i))
    (fun x => ((∑i,p.1 i*A x i)-blockEnergy W B A u p)^2)

theorem block_thermal_integral {k n : ℕ} (hk : 0<k)
    (ν : Fin n → Measure R) [∀i,IsProbabilityMeasure (ν i)]
    (W : (Fin n → R) → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin k → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {a : Fin k → ℝ} (ha : ∀x i,|A x i|≤a i) :
    (∫u in (1:ℝ)..2,∫p,blockThermal W B A u p
        ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi ν))≤6*∑i,a i^2 := by
  cases k with
  | zero => omega
  | succ m =>
    have he (u : ℝ) (p) : (fun x => W p.2 x+∑i,p.1 i*(B x i+u*A x i))=
        affineHamiltonian W B A u p := by
      rw [affineHamiltonian_eq]
      funext x
      change W p.2 x+(∑i,p.1 i*(B x i+u*A x i))=W p.2 x+1*(∑i,p.1 i*(B x i+u*A x i))
      rw [one_mul]
    have ht (u) (p) : blockThermal W B A u p=affineThermal W B A u p := by
      unfold blockThermal blockEnergy affineThermal affineEnergy
      rw [he]
      rfl
    simp only [ht]
    exact affine_mean_thermal_integral (Measure.pi ν) W hmW B A hAB ha

def selectedTensorThermal {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) : ℝ :=
  finiteGibbs (fun x => patternEnergy f p.2 x+fullTensorEnergy hN s (Function.update v (j.val+1) u) p.1 x)
    (fun x => (fullTensorEnergy hN s (selectedParameter (j.val+1)) p.1 x-selectedTensorEnergy hN f s v j u p)^2)

lemma selectedTensorThermal_eq_block {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) :
    selectedTensorThermal hN f s v j u p=blockThermal (patternEnergy f)
      (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
      (fullTensorCoefficient hN s (selectedParameter (j.val+1))) u p := by
  unfold selectedTensorThermal blockThermal
  rw [selectedTensorEnergy_eq_block]
  congr 1
  funext x
  unfold fullTensorEnergy
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg (p.1 i * ·) (fullTensorCoefficient_update hN s v j u x i))

theorem selectedTensor_thermal_integral {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (v : ℕ → ℝ) (j : Fin N) :
    (∫u in (1:ℝ)..2,∫p,selectedTensorThermal hN f s v j u p ∂perturbedDisorderLaw M N)
      ≤6*(s*(1/2)^(j.val+1))^2 := by
  have h := block_thermal_integral (fullTensorCard_pos hN)
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (patternEnergy f) (fun x => by unfold patternEnergy rowEvaluation; fun_prop)
    (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
    (fullTensorCoefficient hN s (selectedParameter (j.val+1)))
    (fullTensorCoefficient_disjoint hN s v j)
    (fun x i => (fullTensorCoefficient_abs hN s (selectedParameter (j.val+1)) x i).le)
  simpa only [perturbedDisorderLaw,← selectedTensorThermal_eq_block,selectedTensorBound_squares hN] using h

lemma finiteGibbs_mono (H V Z : S → ℝ) (h : ∀x,V x≤Z x) : finiteGibbs H V≤finiteGibbs H Z := by
  apply div_le_div_of_nonneg_right _ (finiteGibbs_den_pos H).le
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (exp_pos _).le)

lemma finiteGibbs_abs_young (H V : S → ℝ) {δ : ℝ} (hδ : 0<δ) :
    finiteGibbs H (fun x => |V x|)≤finiteGibbs H (fun x => (V x)^2)/(2*δ)+δ/2 := by
  have h : ∀x,|V x|≤(V x)^2/(2*δ)+δ/2 := by
    intro x
    rw [← sub_le_iff_le_add,le_div_iff₀ (by positivity : 0<2*δ)]
    nlinarith [sq_nonneg (|V x|-δ),sq_abs (V x)]
  simpa only [finiteGibbs_add,finiteGibbs_div_const,finiteGibbs_const] using finiteGibbs_mono H _ _ h

lemma mean_uniform_intervalIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {X : ℝ → Ω → ℝ} {b : Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => X p.1 p.2)) (hb : Integrable b μ)
    (hX : ∀u ω,|X u ω|≤b ω) :
    IntervalIntegrable (fun u => ∫ω,X u ω ∂μ) volume 1 2 := by
  apply (intervalIntegrable_const (c:=∫ω,b ω ∂μ)).mono_fun
    hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [] with u
  simp only [Real.norm_eq_abs]
  calc |∫ω,X u ω ∂μ|≤∫ω,|X u ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (X u)
    _ ≤ ∫ω,b ω ∂μ := integral_mono
      (hb.mono' ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hX u ω)).abs hb (hX u)
    _ ≤ _ := le_abs_self _

def affineThermalAbs {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : ℝ :=
  finiteGibbs (affineHamiltonian W B A u p)
    (fun x => |gaussianLinear A p.1 x-affineEnergy W B A u p|)

omit [Nonempty S] in
lemma affineThermalAbs_measurable {m : ℕ} (W : R → S → ℝ)
    (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) => affineThermalAbs W B A p.1 p.2) := by
  unfold affineThermalAbs affineEnergy finiteGibbs affineHamiltonian gaussianLinear
  fun_prop

omit [MeasurableSpace R] in
lemma affineThermalAbs_bound {m : ℕ} (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : |affineThermalAbs W B A u p|≤2*gaussianLinearBound A p.1 := by
  apply finiteGibbs_abs
  intro x
  rw [abs_abs,two_mul]
  exact (abs_sub _ _).trans (add_le_add (gaussianLinear_abs_bound A p.1 x) (affineEnergy_bound W B A u p))

lemma affineThermalAbs_integrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) (u : ℝ) :
    Integrable (affineThermalAbs W B A u) (affineDisorderLaw m ν) := by
  apply (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num) |>.const_mul 2).mono'
      (((affineThermalAbs_measurable W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using affineThermalAbs_bound W B A u p

theorem affine_thermal_abs_integral {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin (m+1) → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {c : Fin (m+1) → ℝ} (hc : ∀x i,|A x i|≤c i) {δ : ℝ} (hδ : 0<δ) :
    (∫u in (1:ℝ)..2,∫p,affineThermalAbs W B A u p ∂affineDisorderLaw m ν)≤
      3*(∑i,c i^2)/δ+δ/2 := by
  let μ := affineDisorderLaw m ν
  have hp (u : ℝ) : (∫p,affineThermalAbs W B A u p ∂μ)≤
      (∫p,affineThermal W B A u p ∂μ)/(2*δ)+δ/2 := by
    have h := integral_mono (affineThermalAbs_integrable ν W hmW B A u)
      ((affineThermal_integrable ν W hmW B A u).div_const (2*δ) |>.add (integrable_const (δ/2)))
      (fun p => finiteGibbs_abs_young (affineHamiltonian W B A u p)
        (fun x => gaussianLinear A p.1 x-affineEnergy W B A u p) hδ)
    simp only [Pi.add_apply] at h
    rw [integral_add (f:=fun p => affineThermal W B A u p/(2*δ)) (g:=fun _ => δ/2)
      ((affineThermal_integrable ν W hmW B A u).div_const (2*δ)) (integrable_const _),integral_div,integral_const] at h
    simpa only [probReal_univ,one_smul] using h
  have hi := mean_uniform_intervalIntegrable μ (affineThermalAbs_measurable W hmW B A)
    (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable (by norm_num) |>.const_mul 2)
    (affineThermalAbs_bound W B A)
  have ht := affine_mean_thermal_intervalIntegrable ν W hmW B A
  have h := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)≤2) hi
    (ht.div_const (2*δ) |>.add intervalIntegrable_const) (fun u _ => hp u)
  rw [intervalIntegral.integral_add (ht.div_const (2*δ)) intervalIntegrable_const,
    intervalIntegral.integral_div,intervalIntegral.integral_const] at h
  norm_num at h
  apply h.trans
  have hb := div_le_div_of_nonneg_right (affine_mean_thermal_integral ν W hmW B A hAB hc)
    (show 0≤2*δ by positivity)
  convert add_le_add hb (le_refl (δ/2)) using 1; ring

def affineDeviation {m : ℕ} (ν : Measure R) (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) : ℝ :=
  finiteGibbs (affineHamiltonian W B A u p)
    (fun x => |gaussianLinear A p.1 x-∫q,affineEnergy W B A u q ∂affineDisorderLaw m ν|)

omit [Nonempty S] in
lemma affineDeviation_measurable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) :
    Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) => affineDeviation ν W B A p.1 p.2) := by
  have hmE : Measurable (fun u => ∫q,affineEnergy W B A u q ∂affineDisorderLaw m ν) :=
    (affineEnergy_measurable W hmW B A).stronglyMeasurable.integral_prod_right.measurable
  apply finiteGibbs_measurable
  · intro x
    unfold affineHamiltonian gaussianLinear
    fun_prop
  · intro x
    exact ((show Measurable (fun p : ℝ × ((Fin (m+1) → ℝ) × R) => gaussianLinear A p.2.1 x) from by
      unfold gaussianLinear; fun_prop).sub (hmE.comp measurable_fst)).abs

lemma affineDeviation_bound {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) :
    |affineDeviation ν W B A u p|≤gaussianLinearBound A p.1+
      ∫q,gaussianLinearBound A q.1 ∂affineDisorderLaw m ν := by
  apply finiteGibbs_abs
  intro x
  rw [abs_abs]
  apply (abs_sub _ _).trans
  apply add_le_add (gaussianLinear_abs_bound A p.1 x)
  calc _ ≤ ∫q,|affineEnergy W B A u q| ∂affineDisorderLaw m ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (affineEnergy W B A u)
    _ ≤ _ := integral_mono (affineEnergy_integrable ν W hmW B A u).abs
      (((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable (by norm_num))
      (affineEnergy_bound W B A u)

lemma affineDeviation_integrable {m : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (W : R → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x)) (B A : S → Fin (m+1) → ℝ) (u : ℝ) :
    Integrable (affineDeviation ν W B A u) (affineDisorderLaw m ν) := by
  apply ((((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num)).add (integrable_const _)).mono'
      (((affineDeviation_measurable ν W hmW B A).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply,id_eq] using affineDeviation_bound ν W hmW B A u p

lemma affineDeviation_split {m : ℕ} (ν : Measure R) (W : R → S → ℝ) (B A : S → Fin (m+1) → ℝ)
    (u : ℝ) (p : (Fin (m+1) → ℝ) × R) :
    affineDeviation ν W B A u p≤affineThermalAbs W B A u p+
      |affineEnergy W B A u p-∫q,affineEnergy W B A u q ∂affineDisorderLaw m ν| := by
  unfold affineDeviation affineThermalAbs
  rw [← finiteGibbs_const (affineHamiltonian W B A u p)
    |affineEnergy W B A u p-∫q,affineEnergy W B A u q ∂affineDisorderLaw m ν|,← finiteGibbs_add]
  apply finiteGibbs_mono
  intro x
  exact abs_sub_le _ _ _

theorem orthogonal_block_deviation_integral {m n : ℕ} [Nonempty R]
    (ν : Fin n → Measure R) [∀i,IsProbabilityMeasure (ν i)]
    (W : (Fin n → R) → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin (m+1) → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {M : ℝ} (hW : ∀r x,|W r x|≤M)
    {a b : Fin (m+1) → ℝ} (ha : ∀x i,|A x i|≤a i)
    (hb : ∀u ∈ Icc (1/2:ℝ) (5/2),∀x i,|B x i+u*A x i|≤b i)
    (d : Fin n → ℝ) (hd : ∀i r r',(∀k,k≠i → r k=r' k) → ∀x,|W r x-W r' x|≤d i)
    {η δ : ℝ} (hη : 0<η) (hη' : η≤1/2) (hδ : 0<δ) :
    (∫u in (1:ℝ)..2,∫p,affineDeviation (Measure.pi ν) W B A u p ∂affineDisorderLaw m (Measure.pi ν))≤
      3*(∑i,a i^2)/δ+δ/2+4*sqrt ((∑i,b i^2)+(∑i,d i^2))/η+20*η*(∑i,a i^2) := by
  let σ := Measure.pi ν
  let μ := affineDisorderLaw m σ
  have hiL : Integrable (fun p => gaussianLinearBound A p.1) μ :=
    ((gaussianLinearBound_memLp A).comp_measurePreserving measurePreserving_fst).integrable (by norm_num)
  have hi := mean_uniform_intervalIntegrable μ (affineDeviation_measurable σ W hmW B A)
    (hiL.add (integrable_const _)) (affineDeviation_bound σ W hmW B A)
  have ht := mean_uniform_intervalIntegrable μ (affineThermalAbs_measurable W hmW B A)
    (hiL.const_mul 2) (affineThermalAbs_bound W B A)
  have hq := affine_centeredEnergy_intervalIntegrable σ W hmW B A
  have hp (u : ℝ) : (∫p,affineDeviation σ W B A u p ∂μ)≤
      (∫p,affineThermalAbs W B A u p ∂μ)+
      ∫p,|affineEnergy W B A u p-∫q,affineEnergy W B A u q ∂μ| ∂μ := by
    have h := integral_mono (affineDeviation_integrable σ W hmW B A u)
      ((affineThermalAbs_integrable σ W hmW B A u).add
        ((affineEnergy_integrable σ W hmW B A u).sub (integrable_const _)).abs)
      (affineDeviation_split σ W B A u)
    simp only [Pi.add_apply,Pi.sub_apply] at h
    rw [integral_add (f:=affineThermalAbs W B A u)
      (g:=fun p => |affineEnergy W B A u p-∫q,affineEnergy W B A u q ∂μ|)
      (affineThermalAbs_integrable σ W hmW B A u)
      ((affineEnergy_integrable σ W hmW B A u).sub (integrable_const _)).abs] at h
    exact h
  have h := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)≤2) hi (ht.add hq) (fun u _ => hp u)
  rw [intervalIntegral.integral_add ht hq] at h
  have hbnd := add_le_add (affine_thermal_abs_integral σ W hmW B A hAB ha hδ)
    (orthogonal_block_quenched_integral ν W hmW B A hAB hW ha hb d hd hη hη')
  exact h.trans (by convert hbnd using 1; ring)

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval
variable {S R : Type*} [Fintype S] [Nonempty S] [MeasurableSpace R] [Nonempty R]

def blockDeviation {k n : ℕ} (ν : Fin n → Measure R) (W : (Fin n → R) → S → ℝ)
    (B A : S → Fin k → ℝ) (u : ℝ) (p : (Fin k → ℝ) × (Fin n → R)) : ℝ :=
  finiteGibbs (fun x => W p.2 x+∑i,p.1 i*(B x i+u*A x i))
    (fun x => |(∑i,p.1 i*A x i)-∫q,blockEnergy W B A u q
      ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi ν)|)

theorem block_deviation_integral {k n : ℕ} (hk : 0<k)
    (ν : Fin n → Measure R) [∀i,IsProbabilityMeasure (ν i)]
    (W : (Fin n → R) → S → ℝ) (hmW : ∀x,Measurable (fun r => W r x))
    (B A : S → Fin k → ℝ) (hAB : ∀x y,∑i,A x i*B y i=0)
    {M : ℝ} (hW : ∀r x,|W r x|≤M)
    {a b : Fin k → ℝ} (ha : ∀x i,|A x i|≤a i)
    (hb : ∀u ∈ Icc (1/2:ℝ) (5/2),∀x i,|B x i+u*A x i|≤b i)
    (d : Fin n → ℝ) (hd : ∀i r r',(∀l,l≠i → r l=r' l) → ∀x,|W r x-W r' x|≤d i)
    {η δ : ℝ} (hη : 0<η) (hη' : η≤1/2) (hδ : 0<δ) :
    (∫u in (1:ℝ)..2,∫p,blockDeviation ν W B A u p
        ∂(Measure.pi (fun _ => gaussianReal 0 1)).prod (Measure.pi ν))≤
      3*(∑i,a i^2)/δ+δ/2+4*sqrt ((∑i,b i^2)+(∑i,d i^2))/η+20*η*(∑i,a i^2) := by
  cases k with
  | zero => omega
  | succ m =>
    have he (u : ℝ) (p) : (fun x => W p.2 x+∑i,p.1 i*(B x i+u*A x i))=
        affineHamiltonian W B A u p := by
      rw [affineHamiltonian_eq]
      funext x
      change W p.2 x+(∑i,p.1 i*(B x i+u*A x i))=W p.2 x+1*(∑i,p.1 i*(B x i+u*A x i))
      rw [one_mul]
    have ht (u) (p) : blockDeviation ν W B A u p=affineDeviation (Measure.pi ν) W B A u p := by
      unfold blockDeviation blockEnergy affineDeviation affineEnergy
      simp only [he]
      rfl
    simp only [ht]
    exact orthogonal_block_deviation_integral ν W hmW B A hAB hW ha hb d hd hη hη' hδ

def selectedTensorDeviation {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) : ℝ :=
  finiteGibbs (fun x => patternEnergy f p.2 x+fullTensorEnergy hN s (Function.update v (j.val+1) u) p.1 x)
    (fun x => |fullTensorEnergy hN s (selectedParameter (j.val+1)) p.1 x-
      ∫q,selectedTensorEnergy hN f s v j u q ∂perturbedDisorderLaw M N|)

lemma selectedTensorDeviation_eq_block {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) :
    selectedTensorDeviation hN f s v j u p=blockDeviation
      (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) (patternEnergy f)
      (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
      (fullTensorCoefficient hN s (selectedParameter (j.val+1))) u p := by
  unfold selectedTensorDeviation blockDeviation
  simp only [selectedTensorEnergy_eq_block]
  congr 1
  funext x
  unfold fullTensorEnergy
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg (p.1 i * ·) (fullTensorCoefficient_update hN s v j u x i))

lemma selectedTensor_update_bound {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2)) (j : Fin N)
    (u : ℝ) (hu : u∈Icc (1/2:ℝ) (5/2)) (x : Spins N) (i : Fin (Fintype.card (FullTensorIndex N))) :
    |fullTensorCoefficient hN s (Function.update v (j.val+1) 0) x i+
      u*fullTensorCoefficient hN s (selectedParameter (j.val+1)) x i|≤fullTensorBound N s (fun _ => 5/2) i := by
  classical
  rw [← fullTensorCoefficient_update,fullTensorCoefficient_abs]
  unfold fullTensorBound tensorAmplitude
  simp only [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ht : Function.update v (j.val+1) u ((fullTensorEnumeration N i).1.val+1)∈Icc (1/2:ℝ) (5/2) := by
    by_cases hh : (fullTensorEnumeration N i).1.val+1=j.val+1
    · simpa only [hh,Function.update_self] using hu
    · simpa only [Function.update_of_ne hh] using hv (fullTensorEnumeration N i).1
  rw [abs_of_nonneg (by linarith [ht.1] : 0≤Function.update v (j.val+1) u ((fullTensorEnumeration N i).1.val+1))]
  norm_num
  exact ht.2

theorem selectedTensor_deviation_integral {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (s : ℝ) (hs : s≠0) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2)) (j : Fin N)
    {η : ℝ} (hη : 0<η) (hη' : η≤1/2) :
    (∫u in (1:ℝ)..2,∫p,selectedTensorDeviation hN f s v j u p ∂perturbedDisorderLaw M N)≤
      (7/2)*|s*(1/2)^(j.val+1)|+4*sqrt ((25/12)*s^2+4*M*C^2)/η+
      20*η*(s*(1/2)^(j.val+1))^2 := by
  classical
  have ht : s*(1/2)^(j.val+1)≠0 := mul_ne_zero hs (pow_ne_zero _ (by norm_num))
  have h := block_deviation_integral (fullTensorCard_pos hN)
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (patternEnergy f) (fun x => by unfold patternEnergy rowEvaluation; fun_prop)
    (fullTensorCoefficient hN s (Function.update v (j.val+1) 0))
    (fullTensorCoefficient hN s (selectedParameter (j.val+1)))
    (fullTensorCoefficient_disjoint hN s v j) (patternEnergy_bound hC)
    (fun x i => (fullTensorCoefficient_abs hN s (selectedParameter (j.val+1)) x i).le)
    (selectedTensor_update_bound hN s v hv j)
    (fun _ => 2*C) (fun a g g' heq x => patternEnergy_row_difference hC a g g' heq x) hη hη' (abs_pos.mpr ht)
  simp only [← selectedTensorDeviation_eq_block,selectedTensorBound_squares hN,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hδ : 3*(s*(1/2)^(j.val+1))^2/|s*(1/2)^(j.val+1)|+|s*(1/2)^(j.val+1)|/2=
      (7/2)*|s*(1/2)^(j.val+1)| := by
    rw [← sq_abs (s*(1/2)^(j.val+1))]
    field_simp [(abs_pos.mpr ht).ne']
    ring
  rw [hδ] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hη.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
  apply Real.sqrt_le_sqrt
  rw [fullTensorBound_squares hN]
  have hT := totalTensor_variance_uniform (N:=N) s (fun _ => 5/2) (fun _ => by constructor <;> norm_num)
  nlinarith

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology Interval

def selectedTensorObservable {N : ℕ} (hN : 0<N) (j : Fin N)
    (g : Fin (Fintype.card (FullTensorIndex N)) → ℝ) (x : Spins N) : ℝ :=
  tensorPerturbation hN (j.val+1) (fun a => g ((fullTensorEnumeration N).symm ⟨j,a⟩)) x

lemma fullTensorEnergy_selected {N : ℕ} (hN : 0<N) (s : ℝ) (j : Fin N)
    (g : Fin (Fintype.card (FullTensorIndex N)) → ℝ) (x : Spins N) :
    fullTensorEnergy hN s (selectedParameter (j.val+1)) g x=
      (s*(1/2)^(j.val+1))*selectedTensorObservable hN j g x := by
  classical
  rw [fullTensorEnergy_eq,Finset.sum_eq_single j]
  · simp only [tensorAmplitude,selectedParameter,ite_true,mul_one,selectedTensorObservable]
  · intro k _ hkj
    have hk : k.val+1≠j.val+1 := by intro he; exact hkj (Fin.ext (by omega))
    simp only [tensorAmplitude,selectedParameter,ite_eq_right hk,mul_zero,zero_mul]
  · simp

def rawTensorMean {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) : ℝ :=
  finiteGibbs (fun x => patternEnergy f p.2 x+fullTensorEnergy hN s (Function.update v (j.val+1) u) p.1 x)
    (selectedTensorObservable hN j p.1)

def rawTensorDeviation {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) : ℝ :=
  finiteGibbs (fun x => patternEnergy f p.2 x+fullTensorEnergy hN s (Function.update v (j.val+1) u) p.1 x)
    (fun x => |selectedTensorObservable hN j p.1 x-
      ∫q,rawTensorMean hN f s v j u q ∂perturbedDisorderLaw M N|)

lemma selectedTensorEnergy_scale {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) :
    selectedTensorEnergy hN f s v j u p=(s*(1/2)^(j.val+1))*rawTensorMean hN f s v j u p := by
  unfold selectedTensorEnergy rawTensorMean
  have he : fullTensorEnergy hN s (selectedParameter (j.val+1)) p.1=
      fun x => (s*(1/2)^(j.val+1))*selectedTensorObservable hN j p.1 x :=
    funext (fullTensorEnergy_selected hN s j p.1)
  rw [he,finiteGibbs_const_mul]

lemma selectedTensorDeviation_scale {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (u : ℝ) (p : PerturbedDisorder M N) :
    selectedTensorDeviation hN f s v j u p=|s*(1/2)^(j.val+1)| *rawTensorDeviation hN f s v j u p := by
  unfold selectedTensorDeviation rawTensorDeviation
  simp only [fullTensorEnergy_selected,selectedTensorEnergy_scale,integral_const_mul,← mul_sub,abs_mul]
  rw [finiteGibbs_const_mul]

theorem rawTensor_deviation_integral {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤C) (s : ℝ) (hs : 0<s) (v : ℕ → ℝ)
    (hv : ∀j : Fin N,v (j.val+1)∈Icc (1/2:ℝ) (5/2)) (j : Fin N)
    {η : ℝ} (hη : 0<η) (hη' : η≤1/2) :
    (∫u in (1:ℝ)..2,∫p,rawTensorDeviation hN f s v j u p ∂perturbedDisorderLaw M N)/s≤
      (7/2)/s+4*sqrt ((25/12)*s^2+4*M*C^2)/(η*s^2*(1/2)^(j.val+1))+
      20*η*(1/2)^(j.val+1) := by
  have ht : 0<s*(1/2)^(j.val+1) := by positivity
  have h := selectedTensor_deviation_integral (M:=M) hN hf hC s hs.ne' v hv j hη hη'
  simp only [selectedTensorDeviation_scale,integral_const_mul,intervalIntegral.integral_const_mul,
    abs_of_pos ht] at h
  have h' := div_le_div_of_nonneg_right h (mul_pos ht hs).le
  convert h' using 1 <;> try field_simp [hs.ne',ht.ne',hη.ne']

end IsingPerceptron.Main

end

end OAI
