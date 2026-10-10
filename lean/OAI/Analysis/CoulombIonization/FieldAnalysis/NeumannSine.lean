import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CubeTranslationAverage

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma integral_unitInterval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ x : I, f (x:ℝ)) = ∫ x in (0:ℝ)..1, f x := by
  rw [unitInterval.volume_def]
  change (∫ x : Set.Icc (0:ℝ) 1, f (x:ℝ) ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc f,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

def sineMode (n : ℕ) : C(I,ℂ) where
  toFun x := (Real.sqrt 2*Real.sin (Real.pi*(n+1)*(x:ℝ)) : ℝ)
  continuous_toFun := by fun_prop

lemma sineMode_inner (m n : ℕ) :
    (∫ x : I, conj (sineMode m x)*sineMode n x) = if m=n then 1 else 0 := by
  have he (x : I) : conj (sineMode m x)*sineMode n x =
      ((Real.cos (Real.pi*((((m:ℤ)+1)-((n:ℤ)+1):ℤ):ℝ)*(x:ℝ)) -
      Real.cos (Real.pi*((((m:ℤ)+1)+((n:ℤ)+1):ℤ):ℝ)*(x:ℝ))) : ℝ) := by
    simp only [sineMode,ContinuousMap.coe_mk,Complex.conj_ofReal,← Complex.ofReal_mul]
    congr 1
    push_cast
    rw [show Real.pi*((m:ℝ)+1-((n:ℝ)+1))*(x:ℝ) =
        Real.pi*(m+1)*(x:ℝ)-Real.pi*(n+1)*(x:ℝ) by ring,
      show Real.pi*((m:ℝ)+1+((n:ℝ)+1))*(x:ℝ) =
        Real.pi*(m+1)*(x:ℝ)+Real.pi*(n+1)*(x:ℝ) by ring]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ = (Real.sqrt 2)^2 * Real.sin (Real.pi*(m+1)*(x:ℝ)) *
          Real.sin (Real.pi*(n+1)*(x:ℝ)) := by ring
      _ = _ := by rw [hs,Real.two_mul_sin_mul_sin]
  simp_rw [he]
  rw [integral_complex_ofReal]
  have hcm (k : ℤ) : Integrable (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) :=
    (by fun_prop : Continuous (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (hcm (((m:ℤ)+1)-((n:ℤ)+1))) (hcm (((m:ℤ)+1)+((n:ℤ)+1))),
    integral_interval_cos_int,integral_interval_cos_int]
  have hsum : ((m:ℤ)+1)+((n:ℤ)+1) ≠ 0 := by omega
  have hdiff : ((m:ℤ)+1)-((n:ℤ)+1) = 0 ↔ m=n := by omega
  simp only [ite_eq_right hsum,sub_zero,hdiff]
  split_ifs <;> norm_num

lemma sine_derivative_pairing {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    (∫ x : I, (Real.sin (Real.pi*n*(x:ℝ)) : ℂ)*deriv f (x:ℝ)) =
      -(Real.pi*n:ℝ)*(∫ x : I, (Real.cos (Real.pi*n*(x:ℝ)) : ℂ)*f (x:ℝ)) := by
  have hu (x : ℝ) : HasDerivAt (fun t : ℝ => (Real.sin (Real.pi*n*t):ℂ))
      ((Real.pi*n*Real.cos (Real.pi*n*x):ℝ):ℂ) x := by
    simpa only [id_eq,mul_one,mul_comm] using (((hasDerivAt_id x).const_mul (Real.pi*n)).sin).ofReal_comp
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x (_ : x ∈ uIcc (0:ℝ) 1) => hu x)
    (fun x (_ : x ∈ uIcc (0:ℝ) 1) => (hf.differentiable (by norm_num) x).hasDerivAt)
    ((by fun_prop : Continuous (fun x : ℝ => ((Real.pi*n*Real.cos (Real.pi*n*x):ℝ):ℂ))).intervalIntegrable 0 1)
    (hd.intervalIntegrable 0 1)
  have h0 : Real.sin (Real.pi*n*(0:ℝ)) = 0 := by simp
  have h1 : Real.sin (Real.pi*n*(1:ℝ)) = 0 := by simpa [mul_comm] using Real.sin_nat_mul_pi n
  simp only [h0,h1,Complex.ofReal_zero,zero_mul,sub_zero,zero_sub] at hi
  simp only [Complex.ofReal_mul,mul_assoc,intervalIntegral.integral_const_mul] at hi
  rw [integral_unitInterval (fun x => (Real.sin (Real.pi*n*x):ℂ)*deriv f x),
    integral_unitInterval (fun x => (Real.cos (Real.pi*n*x):ℂ)*f x)]
  simpa only [Complex.ofReal_mul,Complex.ofReal_natCast,neg_mul,mul_assoc] using hi

lemma normalized_sine_derivative_pairing {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ x : I, conj (sineMode (n-1) x)*deriv f (x:ℝ)) =
      -(Real.pi*n:ℝ)*(∫ x : I, conj (neumannMode n x)*f (x:ℝ)) := by
  have hnat : n-1+1=n := by omega
  simp only [sineMode,neumannMode,cosNormalization,ite_eq_right hn,cosMode,
    ContinuousMap.coe_mk,Complex.ofReal_mul,map_mul,Complex.conj_ofReal]
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hnat
  simp only [hreal,mul_assoc,integral_const_mul]
  have hp := sine_derivative_pairing hf n
  simp only [mul_assoc] at hp
  rw [hp]
  push_cast
  ring

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma integral_cube_split {d : ℕ} (i : Fin (d+1)) (f : (Fin (d+1) → I) → ℂ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ y : Fin d → I, ∫ t : I, f (i.insertNth t y) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => I) i).symm
  rw [← hp.integral_comp' f]
  change (∫ x : I × (Fin d → I), f ((MeasurableEquiv.piFinSuccAbove (fun _ => I) i).symm x)
    ∂volume.prod volume) = _
  exact integral_prod_symm _ (hp.integrable_comp_of_integrable hf)

variable {d : Type*} [Fintype d] [DecidableEq d]

def cubeSineMode (i : d) (n : {n : d → ℕ // n i ≠ 0}) : C(d → I,ℂ) where
  toFun x := ∏ j, if j=i then sineMode (n.1 j-1) (x j) else neumannMode (n.1 j) (x j)
  continuous_toFun := by
    apply continuous_finsetProd
    intro j _
    by_cases hj : j=i <;> simp only [hj,ite_true,ite_false] <;> fun_prop

lemma cubeSineMode_inner (i : d) (m n : {n : d → ℕ // n i ≠ 0}) :
    (∫ x : d → I, conj (cubeSineMode i m x)*cubeSineMode i n x) =
      if m=n then 1 else 0 := by
  classical
  simp only [cubeSineMode,ContinuousMap.coe_mk,map_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun j (x : I) => conj (if j=i then sineMode (m.1 j-1) x else neumannMode (m.1 j) x)*
      (if j=i then sineMode (n.1 j-1) x else neumannMode (n.1 j) x))]
  have he (j : d) : (∫ x : I,
      conj (if j=i then sineMode (m.1 j-1) x else neumannMode (m.1 j) x)*
      (if j=i then sineMode (n.1 j-1) x else neumannMode (n.1 j) x)) =
      if m.1 j=n.1 j then 1 else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [ite_true,sineMode_inner]
      have hm := m.2
      have hn := n.2
      have hh : m.1 i-1=n.1 i-1 ↔ m.1 i=n.1 i := by omega
      simp only [hh]
    · simp only [ite_eq_right hj,neumannMode_inner]
  simp_rw [he]
  by_cases h : m=n
  · simp [h]
  · rw [ite_eq_right h]
    have hh : m.1 ≠ n.1 := fun hh => h (Subtype.ext hh)
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

abbrev cubeSineLp (i : d) (n : {n : d → ℕ // n i ≠ 0}) :
    Lp ℂ 2 (volume : Measure (d → I)) := ContinuousMap.toLp 2 volume ℂ (cubeSineMode i n)

lemma orthonormal_cubeSine (i : d) : Orthonormal ℂ (cubeSineLp i) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [ContinuousMap.inner_toLp]
  simpa only [mul_comm] using cubeSineMode_inner i m n

end CoulombNeumann

end

end OAI
