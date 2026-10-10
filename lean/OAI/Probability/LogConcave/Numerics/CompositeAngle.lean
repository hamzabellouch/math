import Mathlib
import OAI.Probability.LogConcave.Numerics.ChainTaylor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def compositeAngle {N : ℕ} (u : I → ℝ) (i : Fin N × I) (c : Fin N) : ℝ :=
  if c < i.1 then 1 else if c = i.1 then u i.2 else 0

omit [Fintype I] [DecidableEq I] in
lemma compositeAngle_mem {N : ℕ} {u : I → ℝ} (hu : ∀i,u i∈Icc (0:ℝ) 1)
    (i : Fin N × I) (c : Fin N) : compositeAngle u i c∈Icc (0:ℝ) 1 := by
  unfold compositeAngle
  split_ifs <;> simp_all

def compositeWeight {N : ℕ} (u : I → ℝ) (ℓ : Fin N → ℝ)
    (i j : Fin N × I) : ℝ := ℓ j.1*weight u j.2 0 (compositeAngle u i j.1)

lemma compositeWeight_budget {N : ℕ} {u : I → ℝ} (hu : ∀i,u i∈Icc (0:ℝ) 1)
    {ℓ : Fin N → ℝ} (hℓ : ∀c,0≤ℓ c) (hsum : (∑c,ℓ c)≤1)
    {C : ℝ} (hC : 0≤C) (hbasis : ∀t∈Icc (0:ℝ) 1,∑j,|basis u j t|≤C)
    (i : Fin N × I) : ∑j,|compositeWeight u ℓ i j|≤(Fintype.card I:ℝ)*C := by
  rw [Fintype.sum_prod_type]
  have hc (c : Fin N) : ∑j,|compositeWeight u ℓ i (c,j)|≤ℓ c*((Fintype.card I:ℝ)*C) := by
    simp only [compositeWeight,abs_mul,abs_of_nonneg (hℓ c),←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hℓ c)
    have ht := compositeAngle_mem hu i c
    exact (weights_abs_bound u ht.1 ht.2 hbasis).trans
      (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hC) ht.2)
  calc
    _ ≤ ∑c,ℓ c*((Fintype.card I:ℝ)*C) := Finset.sum_le_sum (fun c _ => hc c)
    _ = (∑c,ℓ c)*((Fintype.card I:ℝ)*C) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hC) hsum

lemma compositeWeight_sum {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : I → ℝ) (ℓ : Fin N → ℝ) (v : Fin N × I → E) (i : Fin N × I) :
    (∑j,compositeWeight u ℓ i j • v j)=
      ∑c,cellQuadrature u (fun j => v (c,j)) (ℓ c) (compositeAngle u i c) := by
  rw [Fintype.sum_prod_type]
  rfl

lemma composite_error_rms {N : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
    (ℓ : Fin N → ℝ) (R : Fin N → Ω → E) {B : ℝ}
    (hℓ : ∀c,0≤ℓ c) (hsum : (∑c,ℓ c)≤1) (hB : 0≤B)
    (hm : ∀c,AEStronglyMeasurable (R c) ν)
    (hi : ∀c,Integrable (fun z => ‖R c z‖^2) ν)
    (hb : ∀c,(∫z,‖R c z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∑c,ℓ c • R c z‖^2) ν ∧
      (∫z,‖∑c,ℓ c • R c z‖^2 ∂ν)≤B := by
  have he := RMSIntegral.weighted_sum_sq ℓ R hm hi hb
  simp only [abs_of_nonneg (hℓ _)] at he
  refine ⟨he.1,he.2.trans ?_⟩
  have hn : 0≤∑c,ℓ c := Finset.sum_nonneg (fun c _ => hℓ c)
  exact mul_le_of_le_one_left hB (by nlinarith)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [Fintype I] [DecidableEq I] [CompleteSpace E] in
lemma compositeIntegral_sum {N : ℕ} (u : I → ℝ) (t : ℕ → ℝ)
    (f : ℝ → E) (hf : Continuous f) (i : Fin N × I) :
    (∑c : Fin N,(t (c.val+1)-t c.val) •
      ∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s))=
      ∫s in t 0..(t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2),f s := by
  let v := t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2
  let τ : ℕ → ℝ := fun k => if k≤ i.1.val then t k else v
  have hc (c : Fin N) : (t (c.val+1)-t c.val) •
      (∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s))=
        ∫s in τ c.val..τ (c.val+1),f s := by
    rw [intervalIntegral.smul_integral_comp_add_mul]
    simp only [mul_zero,add_zero]
    rcases lt_trichotomy c i.1 with hlt | heq | hgt
    · have hnat : c.val< i.1.val := hlt
      have hnext : c.val+1≤ i.1.val := by omega
      simp only [compositeAngle,ite_eq_left hlt,τ,ite_eq_left hnat.le,
        ite_eq_left hnext,mul_one,add_sub_cancel]
    · subst c
      have hnot : ¬i.1.val+1≤ i.1.val := by omega
      simp only [compositeAngle,lt_self_iff_false,ite_false,τ,le_refl,ite_true,ite_eq_right hnot,v]
    · have hnot : ¬c< i.1 := not_lt_of_gt hgt
      have hne : c≠i.1 := ne_of_gt hgt
      have hnat : ¬c.val≤ i.1.val := not_le_of_gt hgt
      have hnext : ¬c.val+1≤ i.1.val := by omega
      simp only [compositeAngle,ite_eq_right hnot,ite_eq_right hne,τ,
        ite_eq_right hnat,ite_eq_right hnext,mul_zero,add_zero,
        intervalIntegral.integral_same]
  simp_rw [hc]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫s in τ k..τ (k+1),f s),
    intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hf.intervalIntegrable _ _)]
  have hnot : ¬N≤ i.1.val := not_le_of_gt i.1.2
  simp only [τ,Nat.zero_le,ite_true,ite_eq_right hnot,v]

lemma compositeQuadrature_defect {N : ℕ} (u : I → ℝ) (t : ℕ → ℝ)
    (f : ℝ → E) (hf : Continuous f) (i : Fin N × I) :
    (∫s in t 0..(t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2),f s)-
      (∑j : Fin N × I,compositeWeight u (fun c => t (c.val+1)-t c.val) i j •
        f (t j.1.val+(t (j.1.val+1)-t j.1.val)*u j.2))=
      ∑c : Fin N,(t (c.val+1)-t c.val) •
        (∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s)-
          interpolation u (fun j => f (t c.val+(t (c.val+1)-t c.val)*u j)) s) := by
  rw [←compositeIntegral_sum u t f hf i,compositeWeight_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  rw [cellQuadrature_eq_integral,←smul_sub,intervalIntegral.integral_sub]
  · exact (hf.comp (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (interpolation_continuous _ _).intervalIntegrable _ _
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

def derivativeWeight (u : I → ℝ) (i : I) : ℝ :=
  (Lagrange.basis Finset.univ u i).derivative.eval 0

def derivativeStencil (u : I → ℝ) (ψ : ℝ) (v : I → E) : E :=
  ∑i,(derivativeWeight u i/ψ) • v i

lemma derivative_reproduces_scalar (u : I → ℝ) (hu : Function.Injective u)
    (p : ℝ[X]) (hp : p.degree<Fintype.card I) :
    (∑i,derivativeWeight u i*p.eval (u i))=p.derivative.eval 0 := by
  have he := congrArg (fun q : ℝ[X] => q.derivative.eval 0)
    (Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn (by simpa using hp))
  simpa only [Lagrange.interpolate_apply,derivative_sum,derivative_mul,
    derivative_C,zero_mul,mul_zero,zero_add,add_zero,eval_finsetSum,eval_mul,eval_C,derivativeWeight,mul_comm] using he.symm

lemma derivative_reproduces_power (u : I → ℝ) (hu : Function.Injective u) (k : ℕ)
    (hk : k<Fintype.card I) :
    (∑i,derivativeWeight u i*(u i)^k)=if k=1 then 1 else 0 := by
  have hh := derivative_reproduces_scalar u hu (X^k) (by simpa using hk)
  simp only [eval_pow,eval_X,derivative_X_pow,eval_mul,eval_C] at hh
  rw [hh]
  by_cases h0 : k=0
  · simp [h0]
  by_cases h1 : k=1
  · simp [h1]
  have hk1 : k-1≠0 := by omega
  simp [h1,hk1]

lemma derivative_weights_norm (u : I → ℝ) {ψ : ℝ} (hψ : 0<ψ) :
    (∑i,|derivativeWeight u i/ψ|)=(∑i,|derivativeWeight u i|)/ψ := by
  simp only [abs_div,abs_of_pos hψ,Finset.sum_div]

omit [CompleteSpace E] in
lemma derivative_reproduces_vector (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : 1≤n) (hm : n+1≤Fintype.card I) {ψ : ℝ} (hψ : ψ≠0)
    (v : Fin (n+1) → E) :
    derivativeStencil u ψ (fun i => ∑k : Fin (n+1),(ψ*u i)^(k:ℕ) • v k)=v ⟨1,by omega⟩ := by
  unfold derivativeStencil
  simp_rw [Finset.smul_sum,smul_smul,mul_pow]
  rw [Finset.sum_comm]
  have he (k : Fin (n+1)) :
      (∑i,((derivativeWeight u i/ψ)*(ψ^(k:ℕ)*(u i)^(k:ℕ))) • v k)=
        (if (k:ℕ)=1 then 1 else 0) • v k := by
    rw [←Finset.sum_smul]
    have hc : (∑i,(derivativeWeight u i/ψ)*(ψ^(k:ℕ)*(u i)^(k:ℕ)))=
        (ψ^(k:ℕ)/ψ)*∑i,derivativeWeight u i*(u i)^(k:ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    rw [hc,derivative_reproduces_power u hu k (lt_of_lt_of_le k.2 hm)]
    by_cases hk : (k:ℕ)=1
    · simp [hk,hψ]
    · simp [hk]
  simp_rw [he]
  simp only [ite_smul,one_smul,zero_smul]
  rw [Finset.sum_eq_single ⟨1,by omega⟩]
  · simp
  · intro b _ hne
    have h : (b:ℕ)≠1 := fun h => hne (Fin.ext h)
    simp [h]
  · simp

omit [CompleteSpace E] in
theorem derivative_stencil_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : 1≤n) (hcard : n+1≤Fintype.card I) {ψ B : ℝ}
    (hψ : 0<ψ) (J : ℕ → ℝ → Ω → E)
    (hm : ∀i,AEStronglyMeasurable (fun z => J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)) ν)
    (hi : ∀i,Integrable (fun z => ‖J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)‖^2) ν)
    (hB : ∀i,(∫z,‖J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z‖^2) ν ∧
    (∫z,‖derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z‖^2 ∂ν)≤
      ((∑i,|derivativeWeight u i|)/ψ)^2*B := by
  have he (z : Ω) : derivativeStencil u ψ (fun i =>
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i))=J 1 0 z := by
    have hh := derivative_reproduces_vector u hu n hn hcard hψ.ne'
      (fun k => ((k:ℕ).factorial:ℝ)⁻¹ • J k 0 z)
    have ht (i : I) : chainTaylor (fun k t => J k t z) n 0 (ψ*u i)=
        ∑k : Fin (n+1),(ψ*u i)^(k:ℕ) • (((k:ℕ).factorial:ℝ)⁻¹ • J k 0 z) := by
      unfold chainTaylor
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro _ _
      simp only [sub_zero,mul_smul]
      exact smul_comm _ _ _
    simp_rw [ht]
    simpa only [Nat.factorial_one,Nat.cast_one,inv_one,one_smul] using hh
  have hc (z : Ω) : derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z=
      ∑i,(derivativeWeight u i/ψ) • (J 0 (ψ*u i) z-
        chainTaylor (fun k t => J k t z) n 0 (ψ*u i)) := by
    rw [←he z]
    simp only [derivativeStencil,smul_sub,Finset.sum_sub_distrib]
  simp_rw [hc]
  have hh := RMSIntegral.weighted_sum_sq (fun i => derivativeWeight u i/ψ) _ hm hi hB
  rw [derivative_weights_norm u hψ] at hh
  exact hh
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β} [SFinite ν]

theorem endpoint_quotient_rms {J : ℕ → ℝ → β → E} {s : Set ℝ} {x B : ℝ}
    (hx : 0<x) (hB0 : 0≤B) (hsub : uIcc (0:ℝ) x⊆s)
    (hf : ∀z n t,t∈s → HasDerivWithinAt (fun t => J n t z) (J (n+1) t z) s t)
    (hzero : ∀z,J 1 0 z=0)
    (hm : AEStronglyMeasurable (fun p : ℝ × β => J 2 p.1 p.2)
      ((volume.restrict (Ioc 0 x)).prod ν))
    (hi : ∀t∈Ioc 0 x,Integrable (fun z => ‖J 2 t z‖^2) ν)
    (hB : ∀t∈Ioc 0 x,(∫z,‖J 2 t z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖x⁻¹ • J 1 x z‖^2) ν ∧
      (∫z,‖x⁻¹ • J 1 x z‖^2 ∂ν)≤B := by
  have hchain : ∀z n t,t∈s → HasDerivWithinAt (fun t => J (n+1) t z) (J (n+1+1) t z) s t :=
    fun z n t ht => hf z (n+1) t ht
  have he := chainTaylor_remainder_rms (J:=fun n => J (n+1)) (n:=0)
    hx.le hB0 hsub hchain hm hi hB
  simp only [chainTaylor,Finset.sum_range_one,Nat.factorial_zero,Nat.cast_one,
    inv_one,pow_zero,mul_one,one_smul,hzero,sub_zero,zero_add,pow_one,div_one] at he
  have hnorm (z : β) : ‖x⁻¹ • J 1 x z‖^2=(x⁻¹)^2*‖J 1 x z‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp_rw [hnorm]
  refine ⟨he.1.const_mul _,?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (x⁻¹)^2*(x^2*B) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
    _ = B := by field_simp

theorem endpoint_integral_rms {J : ℕ → ℝ → β → E} {s : Set ℝ} {b B : ℝ}
    (hb : 0≤b) (hB0 : 0≤B) (hsub : Icc (0:ℝ) b⊆s)
    (hf : ∀z n t,t∈s → HasDerivWithinAt (fun t => J n t z) (J (n+1) t z) s t)
    (hzero : ∀z,J 1 0 z=0)
    (hm1 : AEStronglyMeasurable (fun p : ℝ × β => J 1 p.1 p.2)
      ((volume.restrict (Ioc 0 b)).prod ν))
    (hm2 : AEStronglyMeasurable (fun p : ℝ × β => J 2 p.1 p.2)
      ((volume.restrict (Ioc 0 b)).prod ν))
    (hi : ∀t∈Ioc 0 b,Integrable (fun z => ‖J 2 t z‖^2) ν)
    (hB : ∀t∈Ioc 0 b,(∫z,‖J 2 t z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t in (0:ℝ)..b,t⁻¹ • J 1 t z‖^2) ν ∧
      (∫z,‖∫t in (0:ℝ)..b,t⁻¹ • J 1 t z‖^2 ∂ν)≤b^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 b)
  have hout (t : ℝ) (ht : t∈Ioc 0 b) :
      Integrable (fun z => ‖t⁻¹ • J 1 t z‖^2) ν ∧
        (∫z,‖t⁻¹ • J 1 t z‖^2 ∂ν)≤B := by
    have htb : Ioc (0:ℝ) t⊆Ioc 0 b := Ioc_subset_Ioc_right ht.2
    apply endpoint_quotient_rms ht.1 hB0
      (by rw [uIcc_of_le ht.1.le]; exact (Icc_subset_Icc_right ht.2).trans hsub)
      hf hzero
    · exact hm2.mono_measure (Measure.prod_mono (Measure.restrict_mono htb le_rfl) le_rfl)
    · exact fun u hu => hi u (htb hu)
    · exact fun u hu => hB u (htb hu)
  have hm : AEStronglyMeasurable (fun p : ℝ × β => p.1⁻¹ • J 1 p.1 p.2) (μ.prod ν) :=
    measurable_fst.inv.aestronglyMeasurable.smul hm1
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖t⁻¹ • J 1 t z‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hout t ht).1
  have hbound : ∀ᵐ t ∂μ,(∫z,‖t⁻¹ • J 1 t z‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hout t ht).2
  have he := RMSIntegral.time_seed_uniform hm hs hbound
  have hμ : μ.real univ=b := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact (Real.volume_real_Ioc_of_le hb).trans (sub_zero b)
  simpa only [intervalIntegral.integral_of_le hb,hμ] using he
end LogConcaveSampling.Quadrature

end

end

end

end OAI
