import Mathlib
import OAI.Probability.SphericalField.Poisson.DistinctMoments

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
lemma gamma_stable_product {a b : ℝ} (hb : 0 < b) (ha : a < b) (k : ℕ) :
    b^k * Real.Gamma (((k+1:ℕ):ℝ)-a/b) =
      Real.Gamma (1-a/b) * ∏ ℓ ∈ Finset.range k, (((ℓ:ℝ)+1)*b-a) := by
  have hab : a/b < 1 := (div_lt_one hb).mpr ha
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < ((k+1:ℕ):ℝ)-a/b := by
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      linarith
    rw [show ((k+1+1:ℕ):ℝ)-a/b = (((k+1:ℕ):ℝ)-a/b)+1 by push_cast; ring,
      Real.Gamma_add_one hp.ne',pow_succ,Finset.prod_range_succ]
    calc
      _ = (b^k*Real.Gamma (((k+1:ℕ):ℝ)-a/b))*(((k:ℝ)+1)*b-a) := by
        push_cast
        field_simp
      _ = _ := by rw [ih]; ring

lemma stable_eppf_scalar {a b c n G : ℝ} (hb : 0 < b) (ha : a < b)
    (hc : 0 < c) (hn : 0 < n-a) (ha1 : a < 1) (k : ℕ) :
    (b^(k+1)*G*(c^(a/b-((k+1:ℕ):ℝ))*(1/b)*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) /
      Real.Gamma (n-a))/(Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a)) =
    Real.Gamma (1-a)/Real.Gamma (n-a)*
      (∏ ℓ ∈ Finset.range k, (((ℓ:ℝ)+1)*b-a))*(G/c^(k+1)) := by
  have hγ : Real.Gamma (1-a/b) ≠ 0 := (Real.Gamma_pos_of_pos (by
    have := (div_lt_one hb).mpr ha
    linarith)).ne'
  have hγn : Real.Gamma (n-a) ≠ 0 := (Real.Gamma_pos_of_pos hn).ne'
  have hpow : c^(a/b) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hg := gamma_stable_product hb ha k
  rw [Real.rpow_sub hc, Real.rpow_natCast]
  have hga : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'
  have hcpow : c^(k+1) ≠ 0 := pow_ne_zero _ hc.ne'
  have hN : b^(k+1)*G*(c^(a/b)/c^(k+1)*(1/b)*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) =
      G*(c^(a/b)/c^(k+1))*(b^k*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) := by
    rw [pow_succ]
    field_simp
  rw [hN,hg]
  have hγ' : Real.Gamma ((b-a)/b) ≠ 0 := by simpa [sub_div, hb.ne'] using hγ
  field_simp

lemma list_prod_map_const_mul (c : ℝ) (f : ℝ → ℝ) (rs : List ℝ) :
    (rs.map (fun r => c*f r)).prod = c^rs.length*(rs.map f).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]; ring

lemma list_prod_map_div_const (c : ℝ) (f : ℝ → ℝ) (rs : List ℝ) :
    (rs.map (fun r => f r/c)).prod = (rs.map f).prod/c^rs.length := by
  simp [div_eq_mul_inv,mul_comm,inv_pow]

lemma list_prod_ofReal (rs : List ℝ) (hr : ∀ r ∈ rs, 0 ≤ r) :
    (rs.map ENNReal.ofReal).prod = ENNReal.ofReal rs.prod := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.map_cons,List.prod_cons,List.prod_cons,ih (fun x hx => hr x (by simp [hx])),
      ENNReal.ofReal_mul (hr r (by simp))]

theorem stableDistinctMoment_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))/
      (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod) := by
  let c := Real.Gamma (1-b)
  let G := (rs.map (fun r => Real.Gamma (r-b))).prod
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hga : 0 < Real.Gamma (1-a) := Real.Gamma_pos_of_pos (by linarith)
  have hgab : 0 < Real.Gamma (1-a/b) := Real.Gamma_pos_of_pos (by
    have := (div_lt_one hb).mpr ha
    linarith)
  have hj : 1 ≤ rs.length := by cases rs <;> simp_all
  have hjR : (1:ℝ) ≤ rs.length := by exact_mod_cast hj
  have hj1 : rs.length-1+1 = rs.length := Nat.sub_add_cancel hj
  have hsum : 0 < rs.sum-a := by
    have := list_length_mul_le_sum (fun r hr' => (hr r hr').le)
    nlinarith
  have hgn : 0 < Real.Gamma (rs.sum-a) := Real.Gamma_pos_of_pos hsum
  have hG : 0 ≤ G := List.prod_nonneg (by
    intro x hx
    obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hx
    exact (Real.Gamma_pos_of_pos (sub_pos.mpr (hr r hr'))).le)
  have hA : (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod =
      ENNReal.ofReal (b^rs.length*G) := by
    rw [show (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))) =
      (rs.map (fun r => b*Real.Gamma (r-b))).map ENNReal.ofReal by simp only [List.map_map,Function.comp_def],
      list_prod_ofReal _ (by
        intro x hx
        obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr (hr r hr'))).le),
      list_prod_map_const_mul]
  have hMpos : 0 < Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a) :=
    div_pos (mul_pos hgab (Real.rpow_pos_of_pos hc _)) hga
  have hM : (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (stablePoissonTotal_rpow_integrable hb hb1 ha)
      (ae_of_all _ (fun η => Real.rpow_nonneg ENNReal.toReal_nonneg _)),
      stablePoissonTotal_rpow_integral hb hb1 ha]
  have he := stableDistinctMoment_palm_mellin_mul hb hb1 ha rs hne hr z
  have hI : (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ((rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal ((Real.Gamma (1-b))^(a/b-(rs.length:ℝ))*(1/b)*
          Real.Gamma ((rs.length:ℝ)-a/b)))/ENNReal.ofReal (Real.Gamma (rs.sum-a)) := by
    apply (ENNReal.eq_div_iff (ENNReal.ofReal_ne_zero_iff.mpr hgn) ENNReal.ofReal_ne_top).mpr
    rw [mul_comm]
    exact he
  rw [hI,hA,hM,← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hb.le _) hG),
    ← ENNReal.ofReal_div_of_pos hgn,← ENNReal.ofReal_div_of_pos hMpos]
  congr 1
  rw [list_prod_map_div_const]
  exact (by simpa only [hj1,c,G] using stable_eppf_scalar hb ha hc hsum (by linarith) (rs.length-1))

def stableEppfValue (a b : ℝ) (rs : List ℝ) : ℝ :=
  Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
    (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
    (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod

lemma stableEppfValue_singleton_one {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    stableEppfValue a b [1] = 1 := by
  have hga : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha)).ne'
  have hgb : Real.Gamma (1-b) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  simp [stableEppfValue,hga,hgb]

lemma stableEppfValue_join {a b r : ℝ} (hr : b < r) (rs : List ℝ)
    (hn : 0 < r+rs.sum-a) :
    stableEppfValue a b ((r+1)::rs) =
      (r-b)/(r+rs.sum-a)*stableEppfValue a b (r::rs) := by
  unfold stableEppfValue
  simp only [List.sum_cons,List.length_cons,List.map_cons,List.prod_cons,Nat.add_sub_cancel]
  rw [show r+1+rs.sum-a = (r+rs.sum-a)+1 by ring,
    show r+1-b = (r-b)+1 by ring,
    Real.Gamma_add_one hn.ne',Real.Gamma_add_one (sub_pos.mpr hr).ne']
  field_simp
  simp only [mul_comm b]
  ring

lemma stableEppfValue_new {a b : ℝ} (hb : b < 1) (rs : List ℝ) (hne : rs ≠ [])
    (hn : 0 < rs.sum-a) :
    stableEppfValue a b (1::rs) =
      ((rs.length:ℝ)*b-a)/(rs.sum-a)*stableEppfValue a b rs := by
  have hj : 1 ≤ rs.length := by cases rs <;> simp_all
  have hj1 : rs.length-1+1 = rs.length := Nat.sub_add_cancel hj
  have hgb : Real.Gamma (1-b) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  unfold stableEppfValue
  simp only [List.sum_cons,List.length_cons,List.map_cons,List.prod_cons,Nat.add_sub_cancel,div_self hgb,one_mul]
  rw [show 1+rs.sum-a = (rs.sum-a)+1 by ring,Real.Gamma_add_one hn.ne',
    ← hj1,Finset.prod_range_succ]
  have hcast : ((rs.length-1:ℕ):ℝ)+1 = (rs.length:ℝ) := by exact_mod_cast hj1
  rw [hcast,hj1]
  field_simp
  simp only [mul_comm b]
  ring

end SphericalPerceptron
end
end
end

end OAI
