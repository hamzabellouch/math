import Mathlib
import OAI.Probability.Perceptron.Cascade.StableCascade

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable

def stableMassKernel : Kernel (Measure ℝ) ℝ where
  toFun η := normalizedMeasure (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

instance stableMassKernel_finite : IsFiniteKernel stableMassKernel := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹ *
    (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def stableCountKernel : Kernel (Measure ℝ) ℝ :=
  stableMassKernel.withDensity (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))

instance stableCountKernel_sFinite : IsSFiniteKernel stableCountKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma stableCountKernel_eq (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel η = η := by
  rw [stableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))))]
  change (((η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹) •
    η.withDensity (fun x => ENNReal.ofReal (Real.exp x))).withDensity
      (fun x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  have hmass : η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ =
      ENNReal.ofReal (stablePoissonTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun x => ENNReal.ofReal (Real.exp x)*
      ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) =
      (fun _ : ℝ => ENNReal.ofReal (stablePoissonTotal η)) := by
    funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (stablePoissonTotal η))⁻¹ • η.withDensity
    (fun x => ENNReal.ofReal (Real.exp x)*ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

lemma stableJumpMomentE_one_add_dirac (x : ℝ) (η : Measure ℝ) :
    stableJumpMomentE 1 (Measure.dirac x+η) = ENNReal.ofReal (Real.exp x)+stableJumpMomentE 1 η := by
  simp [stableJumpMomentE,lintegral_add_measure]

lemma stableCountKernel_add_dirac (η : Measure ℝ) (x : ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel (Measure.dirac x+η) = Measure.dirac x+η := by
  apply stableCountKernel_eq
  · rw [stableJumpMomentE_one_add_dirac]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [stablePoissonTotal_add_dirac x η (by simpa [stableJumpMomentE] using hf)]
    positivity

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

end SphericalPerceptronFreeEnergy

end

end OAI
