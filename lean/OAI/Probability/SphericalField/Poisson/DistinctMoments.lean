import Mathlib
import OAI.Probability.SphericalField.Poisson.LogMoments

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
lemma cascadeMeasurableSet_exists {A I : Type*} [MeasurableSpace A] [Countable I]
    {p : I → A → Prop} (h : ∀ i, MeasurableSet {a | p i a}) :
    MeasurableSet {a | ∃ i, p i a} := by
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion h

@[fun_prop] lemma measurable_fin_cons {A : Type*} [MeasurableSpace A] {n : ℕ}
    {f : A → ℝ} {g : A → Fin n → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.cons (f a) (g a) : Fin (n+1) → ℝ)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp hg

def stableDistinctMoment : List ℝ → {m : ℕ} → Measure ℝ → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | r::rs, _, η, z => ∫⁻ x, if ∃ i, z i = x then 0 else
      ENNReal.ofReal (Real.exp (r*x))*stableDistinctMoment rs η (Fin.cons x z) ∂stableCountKernel η

lemma stableDistinctMoment_measurable (rs : List ℝ) (m : ℕ) :
    Measurable (fun p : Measure ℝ × (Fin m → ℝ) => stableDistinctMoment rs p.1 p.2) := by
  induction rs generalizing m with
  | nil => exact measurable_const
  | cons r rs ih =>
    let κ : Kernel (Measure ℝ × (Fin m → ℝ)) ℝ := stableCountKernel.comap (Prod.fst : Measure ℝ × (Fin m → ℝ) → Measure ℝ) measurable_fst
    have hD : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableDistinctMoment rs p.1.1 (Fin.cons p.2 p.1.2)) := by
      exact (ih (m+1)).comp (measurable_fst.fst.prodMk
        (measurable_fin_cons measurable_snd measurable_fst.snd))
    have hset : MeasurableSet {p : (Measure ℝ × (Fin m → ℝ)) × ℝ | ∃ i, p.1.2 i = p.2} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd
    exact (measurable_const.ite hset ((by fun_prop : Measurable (fun p :
      (Measure ℝ × (Fin m → ℝ)) × ℝ => ENNReal.ofReal (Real.exp (r*p.2)))).mul hD)).lintegral_kernel_prod_right'
      (κ := κ)

lemma stableDistinctMoment_add_dirac (rs : List ℝ) (η : Measure ℝ) (x : ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    {m : ℕ} (z : Fin m → ℝ) (hz : ∃ i, z i = x) :
    stableDistinctMoment rs (Measure.dirac x+η) z = stableDistinctMoment rs η z := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    simp only [stableDistinctMoment,stableCountKernel_add_dirac η x hf hp,
      stableCountKernel_eq η hf hp,lintegral_add_measure,lintegral_dirac,ite_eq_left hz,zero_add]
    apply lintegral_congr
    intro y
    split_ifs
    · rfl
    · rw [ih (Fin.cons y z) (by obtain ⟨i,hi⟩ := hz; exact ⟨i.succ,hi⟩)]

instance stableLogIntensity_noAtoms (b : ℝ) : NullSingletonClass (stableLogIntensity b) := by
  unfold stableLogIntensity
  infer_instance

lemma stableDistinctMoment_palm_laplace {b t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ht : 0 < t) (rs : List ℝ) (hr : ∀ r ∈ rs, b < r) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ((rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod)*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  induction rs generalizing m with
  | nil => simpa [stableDistinctMoment] using stablePoissonTotal_laplace_lintegral hb hb1 ht
  | cons r rs ih =>
    let P := poissonRandomMeasureLaw (stableLogIntensity b)
    let L := ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b))
    let C := (rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod
    let H : Measure ℝ × ℝ → ℝ≥0∞ := fun p => if ∃ i, z i = p.2 then 0 else
      ENNReal.ofReal (Real.exp (r*p.2))*stableDistinctMoment rs p.1 (Fin.cons p.2 z)*
        ENNReal.ofReal (Real.exp (-t*stablePoissonTotal p.1))
    have hH : Measurable H := by
      have hD : Measurable (fun p : Measure ℝ × ℝ => stableDistinctMoment rs p.1 (Fin.cons p.2 z)) :=
        (stableDistinctMoment_measurable rs (m+1)).comp (measurable_fst.prodMk
          (measurable_fin_cons measurable_snd measurable_const))
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_snd) (by fun_prop)
    have hstart : (∫⁻ η, stableDistinctMoment (r::rs) η z*
        ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η)) ∂P) =
        ∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂P := by
      apply lintegral_congr_ae
      filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
      rw [stableDistinctMoment,stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp,
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      dsimp [H]
      split_ifs <;> simp
    have hinner (x : ℝ) : (∫⁻ η, H (Measure.dirac x+η,x) ∂P) =
        (if ∃ i, z i = x then 0 else ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)))*(C*L) := by
      by_cases hx : ∃ i, z i = x
      · simp [H,hx]
      have he : (fun η => H (Measure.dirac x+η,x)) =ᵐ[P]
          (fun η => ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
            (stableDistinctMoment rs η (Fin.cons x z)*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η)))) := by
        filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
        dsimp [H]
        rw [ite_eq_right hx,stableDistinctMoment_add_dirac rs η x (by simpa [stableJumpMomentE] using hf) hp
          (Fin.cons x z) ⟨0,rfl⟩,stablePoissonTotal_add_dirac x η hf,mul_add,Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      rw [lintegral_congr_ae he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ih (fun s hs => hr s (List.mem_cons_of_mem r hs)) (Fin.cons x z),ite_eq_right hx]
    rw [hstart,poissonRandomMeasureLaw_mecke _ hH]
    change (∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x) ∂P ∂stableLogIntensity b) = _
    simp_rw [hinner]
    rw [lintegral_mul_const]
    · have hx : ∀ᵐ x ∂stableLogIntensity b, ¬ ∃ i, z i = x := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin m => (stableLogIntensity b).ae_ne (z i))] with x hx
        exact fun h => by obtain ⟨i,hi⟩ := h; exact hx i hi.symm
      rw [lintegral_congr_ae (hx.mono fun x hx => ite_eq_right hx),
        stableLogIntensity_laplace_moment hb.le (hr r (by simp)) ht]
      simp only [List.map_cons,List.prod_cons]
      dsimp [C,L]
      ring
    · exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_id) (by fun_prop)

lemma stableLaplaceProduct_shape {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (rs : List ℝ) (hr : ∀ r ∈ rs, b < r) :
    (rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod =
      (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum)) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hrr : b < r := hr r (by simp)
    have hc : 0 ≤ b*Real.Gamma (r-b) := mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hrr)).le
    have he : ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)) =
        ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-r)) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    simp only [List.map_cons,List.prod_cons,List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    rw [he,ih (fun v hv => hr v (List.mem_cons_of_mem r hv))]
    calc
      _ = (ENNReal.ofReal (b*Real.Gamma (r-b))*(rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod)*
          (ENNReal.ofReal (t^(b-r))*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum))) := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),← Real.rpow_add ht]
        congr 3
        ring

lemma list_length_mul_le_sum {rs : List ℝ} {b : ℝ} (hr : ∀ r ∈ rs, b ≤ r) :
    (rs.length:ℝ)*b ≤ rs.sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hrr := hr r (by simp)
    have hi := ih (fun s hs => hr s (List.mem_cons_of_mem r hs))
    simp only [List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma stableDistinctMoment_palm_mellin_mul {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (rs.sum-a)) =
      (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal ((Real.Gamma (1-b))^(a/b-(rs.length:ℝ))*(1/b)*
          Real.Gamma ((rs.length:ℝ)-a/b)) := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let c := Real.Gamma (1-b)
  let A := (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hj : (1:ℝ) ≤ rs.length := by
    have hj : 1 ≤ rs.length := by cases rs <;> simp_all
    exact_mod_cast hj
  have hjb : 0 < (rs.length:ℝ)*b-a := by nlinarith
  have hsum : 0 < rs.sum-a := by
    have hsum := list_length_mul_le_sum (fun r hr' => (hr r hr').le)
    linarith
  have hD : Measurable (fun η => stableDistinctMoment rs η z) :=
    (stableDistinctMoment_measurable rs m).comp (measurable_id.prodMk measurable_const)
  let K := fun (η : Measure ℝ) (t : ℝ) => stableDistinctMoment rs η z*
    ENNReal.ofReal (t^(rs.sum-a-1)*Real.exp (-t*stablePoissonTotal η))
  have hm : Measurable (Function.uncurry K) := by
    exact (hD.comp measurable_fst).mul (by fun_prop)
  have hgamma : ∀ᵐ η ∂P,
      stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))*
        ENNReal.ofReal (Real.Gamma (rs.sum-a)) = ∫⁻ t : ℝ in Ioi 0, K η t := by
    filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
    dsimp [K]
    rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hsum hη,
      show -(rs.sum-a) = a-rs.sum by ring,ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),mul_assoc]
  have hinner (t : ℝ) (ht : 0 < t) : (∫⁻ η, K η t ∂P) =
      A*ENNReal.ofReal (t^((rs.length:ℝ)*b-a-1)*Real.exp (-c*t^b)) := by
    have hfac (η : Measure ℝ) : K η t = ENNReal.ofReal (t^(rs.sum-a-1))*
        (stableDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      ring
    simp_rw [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      stableDistinctMoment_palm_laplace hb hb1 ht rs hr z,stableLaplaceProduct_shape hb ht rs hr]
    change ENNReal.ofReal (t^(rs.sum-a-1))*(A*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum))*
      ENNReal.ofReal (Real.exp (-c*t^b))) = _
    calc
      _ = A*(ENNReal.ofReal (t^(rs.sum-a-1))*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum)))*
          ENNReal.ofReal (Real.exp (-c*t^b)) := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),← Real.rpow_add ht,
          show rs.sum-a-1+((rs.length:ℝ)*b-rs.sum) = (rs.length:ℝ)*b-a-1 by ring,
          mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  calc
    _ = ∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))*
        ENNReal.ofReal (Real.Gamma (rs.sum-a)) ∂P :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ η, (∫⁻ t : ℝ in Ioi 0, K η t) ∂P := lintegral_congr_ae hgamma
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ η, K η t ∂P := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0,
        A*ENNReal.ofReal (t^((rs.length:ℝ)*b-a-1)*Real.exp (-c*t^b)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    _ = A*ENNReal.ofReal (c^(-(((rs.length:ℝ)*b-a-1)+1)/b)*(1/b)*
        Real.Gamma ((((rs.length:ℝ)*b-a-1)+1)/b)) := by
      rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_rpow_scale (by linarith) hb hc]
    _ = _ := by
      rw [show -(((rs.length:ℝ)*b-a-1)+1)/b = a/b-(rs.length:ℝ) by field_simp; ring,
        show (((rs.length:ℝ)*b-a-1)+1)/b = (rs.length:ℝ)-a/b by field_simp; ring]

end SphericalPerceptron
end
end
end

end OAI
