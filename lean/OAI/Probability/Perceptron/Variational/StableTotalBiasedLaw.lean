import Mathlib
import OAI.Probability.Perceptron.Variational.StableMassKernel

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

def stableTotalBiasedLaw (a b : ℝ) : Measure (Measure ℝ) :=
  normalizedMeasure ((poissonRandomMeasureLaw (stableLogIntensity b)).withDensity
    (fun η => ENNReal.ofReal (stablePoissonTotal η^a)))

lemma stableTotalBias_mass {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b) :
    ((poissonRandomMeasureLaw (stableLogIntensity b)).withDensity
      (fun η => ENNReal.ofReal (stablePoissonTotal η^a))) univ =
      ENNReal.ofReal (Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a)) := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (stablePoissonTotal_rpow_integrable hb hb1 ha)
      (ae_of_all _ (fun η => Real.rpow_nonneg ENNReal.toReal_nonneg _)),
    stablePoissonTotal_rpow_integral hb hb1 ha]

lemma stableTotalBiasedLaw_probability {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b) :
    IsProbabilityMeasure (stableTotalBiasedLaw a b) := by
  have hp : 0 < Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a) := by
    apply div_pos (mul_pos (Real.Gamma_pos_of_pos ?_) (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _))
      (Real.Gamma_pos_of_pos (by linarith))
    have := (div_lt_one hb).mpr ha
    linarith
  apply normalizedMeasure_probability
  · rw [stableTotalBias_mass hb hb1 ha]; exact ENNReal.ofReal_ne_zero_iff.mpr hp
  · rw [stableTotalBias_mass hb hb1 ha]; exact ENNReal.ofReal_ne_top

def stableOrderedDistinctMass (rs : List ℝ) (η : Measure ℝ) {m : ℕ} (z : Fin m → ℝ) : ℝ≥0∞ :=
  stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(-rs.sum))

lemma stableOrderedDistinctMass_measurable (rs : List ℝ) {m : ℕ} (z : Fin m → ℝ) :
    Measurable (fun η => stableOrderedDistinctMass rs η z) :=
  ((stableDistinctMoment_measurable rs m).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)

lemma stableOrderedDistinctMass_biased {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (_ha : a < b) (rs : List ℝ) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableOrderedDistinctMass rs η z ∂stableTotalBiasedLaw a b) =
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))/
      (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  unfold stableTotalBiasedLaw normalizedMeasure
  rw [lintegral_smul_measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (stableOrderedDistinctMass_measurable rs z)]
  simp only [smul_eq_mul,Pi.mul_apply]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [stablePoissonTotal_pos hb hb1] with η hp
  unfold stableOrderedDistinctMass
  calc
    _ = stableDistinctMoment rs η z*(ENNReal.ofReal (stablePoissonTotal η^a)*
      ENNReal.ofReal (stablePoissonTotal η^(-rs.sum))) := by ring
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _),← Real.rpow_add hp,sub_eq_add_neg]

lemma stableOrderedDistinctMass_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableOrderedDistinctMass rs η z ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod) := by
  rw [stableOrderedDistinctMass_biased hb hb1 ha,stableDistinctMoment_eppf hb hb1 ha rs hne hr]

lemma stableCountAtom_measurable :
    Measurable (fun p : Measure ℝ × ℝ => stableCountKernel p.1 {p.2}) := by
  let κ : Kernel (Measure ℝ × ℝ) ℝ := stableCountKernel.comap (Prod.fst : Measure ℝ × ℝ → Measure ℝ) measurable_fst
  have hm : Measurable (fun p : (Measure ℝ × ℝ) × ℝ => if p.2 = p.1.2 then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd) measurable_const
  have hh := hm.lintegral_kernel_prod_right' (κ := κ)
  convert hh using 1
  funext p
  change _ = ∫⁻ y, if y = p.2 then (1:ℝ≥0∞) else 0 ∂stableCountKernel p.1
  rw [show (fun y : ℝ => if y = p.2 then (1:ℝ≥0∞) else 0) =
    ({p.2}:Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) by rfl,
    lintegral_indicator (measurableSet_singleton _),lintegral_one,Measure.restrict_apply_univ]

lemma stablePoissonCount_simple {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), ∀ᵐ x ∂η, η {x} = 1 := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let H := fun p : Measure ℝ × ℝ => if stableCountKernel p.1 {p.2} = 1 then (0:ℝ≥0∞) else 1
  have hm : Measurable H := measurable_const.ite (measurableSet_eq_fun stableCountAtom_measurable measurable_const) measurable_const
  have hright (x : ℝ) : (∫⁻ η, H (Measure.dirac x+η,x) ∂P) = 0 := by
    apply (lintegral_eq_zero_iff (hm.comp ((measurable_const.add measurable_id).prodMk measurable_const))).mpr
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1,
      poissonRandomMeasureLaw_ae_null (stableLogIntensity b) (measurableSet_singleton x) (measure_singleton x)] with η hf hp hnull
    have hf' : stableJumpMomentE 1 η ≠ ⊤ := by simpa [stableJumpMomentE] using hf
    simp [H,stableCountKernel_add_dirac η x hf' hp,hnull]
  have he : (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂P) = 0 := by
    rw [poissonRandomMeasureLaw_mecke (stableLogIntensity b) hm]
    change (∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x) ∂P ∂stableLogIntensity b) = 0
    simp_rw [hright]
    exact lintegral_zero
  have hkernel : Measurable (fun η => ∫⁻ x, H (η,x) ∂stableCountKernel η) :=
    hm.lintegral_kernel_prod_right'
  have he' : (∫⁻ η, ∫⁻ x, H (η,x) ∂stableCountKernel η ∂P) = 0 := by
    rw [← he]
    apply lintegral_congr_ae
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
    rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp]
  have hae := (lintegral_eq_zero_iff hkernel).mp he'
  filter_upwards [hae,stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hzero hf hp
  rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp] at hzero
  have hz := (lintegral_eq_zero_iff (hm.comp (measurable_const.prodMk measurable_id))).mp hzero
  filter_upwards [hz] with x hx
  dsimp [H] at hx
  rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp] at hx
  by_contra h
  simp [h] at hx

lemma stableMassKernel_atom_eq (η : Measure ℝ) {x : ℝ}
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) (hx : η {x} = 1) :
    stableMassKernel η {x} = ENNReal.ofReal (Real.exp x/stablePoissonTotal η) := by
  change ((η.withDensity (fun y => ENNReal.ofReal (Real.exp y)) univ)⁻¹ •
    η.withDensity (fun y => ENNReal.ofReal (Real.exp y))) {x} = _
  rw [Measure.smul_apply,smul_eq_mul,withDensity_apply _ (measurableSet_singleton x),lintegral_singleton,hx,mul_one,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have htotal : (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂η) = ENNReal.ofReal (stablePoissonTotal η) := by
    exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
  rw [htotal,ENNReal.ofReal_div_of_pos hp,div_eq_mul_inv,mul_comm]

lemma stableMassAtom_measurable :
    Measurable (fun p : Measure ℝ × ℝ => stableMassKernel p.1 {p.2}) := by
  let κ : Kernel (Measure ℝ × ℝ) ℝ := stableMassKernel.comap (Prod.fst : Measure ℝ × ℝ → Measure ℝ) measurable_fst
  have hm : Measurable (fun p : (Measure ℝ × ℝ) × ℝ => if p.2 = p.1.2 then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd) measurable_const
  have hh := hm.lintegral_kernel_prod_right' (κ := κ)
  convert hh using 1
  funext p
  change _ = ∫⁻ y, if y = p.2 then (1:ℝ≥0∞) else 0 ∂stableMassKernel p.1
  rw [show (fun y : ℝ => if y = p.2 then (1:ℝ≥0∞) else 0) =
    ({p.2}:Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) by rfl,
    lintegral_indicator (measurableSet_singleton _),lintegral_one,Measure.restrict_apply_univ]

lemma stableMassAtom_measurable_comp {A : Type*} [MeasurableSpace A]
    {f : A → Measure ℝ} {g : A → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => stableMassKernel (f a) {g a}) := by
  exact Measurable.comp (g := (fun p : Measure ℝ × ℝ => stableMassKernel p.1 {p.2}))
    (f := (fun a => (f a,g a))) stableMassAtom_measurable (hf.prodMk hg)

def stableBlockProbability : List ℕ → {m : ℕ} → Measure ℝ → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | n::ns, _, η, z => ∫⁻ x, if ∃ i, z i = x then 0 else
      (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z) ∂stableMassKernel η

lemma stableBlockProbability_measurable (ns : List ℕ) (m : ℕ) :
    Measurable (fun p : Measure ℝ × (Fin m → ℝ) => stableBlockProbability ns p.1 p.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons n ns ih =>
    let κ : Kernel (Measure ℝ × (Fin m → ℝ)) ℝ := stableMassKernel.comap (Prod.fst : Measure ℝ × (Fin m → ℝ) → Measure ℝ) measurable_fst
    have hD : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableBlockProbability ns p.1.1 (Fin.cons p.2 p.1.2)) := by
      exact (ih (m+1)).comp (measurable_fst.fst.prodMk
        (measurable_fin_cons measurable_snd measurable_fst.snd))
    have ha : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableMassKernel p.1.1 {p.2}) :=
      stableMassAtom_measurable_comp (f := fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ => p.1.1)
        (g := fun p => p.2) measurable_fst.fst measurable_snd
    have hset : MeasurableSet {p : (Measure ℝ × (Fin m → ℝ)) × ℝ | ∃ i, p.1.2 i = p.2} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd
    exact (measurable_const.ite hset ((ha.pow_const _).mul hD)).lintegral_kernel_prod_right' (κ := κ)

lemma stableBlockProbability_moment (ns : List ℕ) (hn : ∀ n ∈ ns, 1 ≤ n) (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    (hs : ∀ᵐ x ∂η, η {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    stableBlockProbability ns η z = stableDistinctMoment (ns.map (fun n : ℕ => (n:ℝ))) η z*
      ((ENNReal.ofReal (stablePoissonTotal η))⁻¹)^ns.sum := by
  induction ns generalizing m with
  | nil => simp [stableBlockProbability,stableDistinctMoment]
  | cons n ns ih =>
    have hn0 : 1 ≤ n := hn n (by simp)
    have hn' : n-1+1 = n := Nat.sub_add_cancel hn0
    have hns : ∀ k ∈ ns, 1 ≤ k := fun k hk => hn k (by simp [hk])
    have hm : Measurable (fun x => if ∃ i, z i = x then (0:ℝ≥0∞) else
        (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z)) := by
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_id)
        (((stableMassAtom_measurable.comp (measurable_const.prodMk measurable_id)).pow_const _).mul
          ((stableBlockProbability_measurable ns (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_id measurable_const))))
    have htotal : (η.withDensity (fun x => ENNReal.ofReal (Real.exp x))) univ =
        ENNReal.ofReal (stablePoissonTotal η) := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
    unfold stableBlockProbability
    change (∫⁻ x, (if ∃ i, z i = x then 0 else (stableMassKernel η {x})^(n-1)*
      stableBlockProbability ns η (Fin.cons x z)) ∂normalizedMeasure
        (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)))) = _
    rw [normalizedMeasure,lintegral_smul_measure,htotal,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
    simp only [smul_eq_mul,Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))]
    have hpoint : (fun x => (ENNReal.ofReal (stablePoissonTotal η))⁻¹ *
        (ENNReal.ofReal (Real.exp x)*(if ∃ i, z i = x then 0 else
          (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z)))) =ᵐ[η]
        (fun x => (if ∃ i, z i = x then 0 else ENNReal.ofReal (Real.exp ((n:ℝ)*x))*
          stableDistinctMoment (ns.map (fun n : ℕ => (n:ℝ))) η (Fin.cons x z))*
          ((ENNReal.ofReal (stablePoissonTotal η))⁻¹)^(n+ns.sum)) := by
      filter_upwards [hs] with x hx
      split_ifs
      · simp
      · rw [stableMassKernel_atom_eq η hf hp hx,ENNReal.ofReal_div_of_pos hp,
          ih hns (Fin.cons x z),div_eq_mul_inv,mul_pow,Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le,
          pow_add,← hn',pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
    rw [lintegral_congr_ae hpoint,lintegral_mul_const' _ _ (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)))]
    simp only [List.map_cons,List.sum_cons]
    rw [stableDistinctMoment,stableCountKernel_eq η hf hp]

lemma stableTotalBiasedLaw_absolutelyContinuous (a b : ℝ) :
    stableTotalBiasedLaw a b ≪ poissonRandomMeasureLaw (stableLogIntensity b) := by
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma stableBlockProbability_ordered (ns : List ℕ) (hn : ∀ n ∈ ns, 1 ≤ n) (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    (hs : ∀ᵐ x ∂η, η {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    stableBlockProbability ns η z = stableOrderedDistinctMass (ns.map (fun n : ℕ => (n:ℝ))) η z := by
  rw [stableBlockProbability_moment ns hn η hf hp hs]
  unfold stableOrderedDistinctMass
  congr 1
  rw [Real.rpow_neg hp.le,ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hp _)]
  have hsum : (ns.map (fun n : ℕ => (n:ℝ))).sum = (ns.sum:ℝ) := by
    induction ns with
    | nil => simp
    | cons n ns ih => simp
  rw [hsum,Real.rpow_natCast,ENNReal.ofReal_pow hp.le,ENNReal.inv_pow]

lemma stableBlockProbability_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List ℕ) (hne : ns ≠ []) (hn : ∀ n ∈ ns, 1 ≤ n) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableBlockProbability ns η z ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma ((ns.map (fun n : ℕ => (n:ℝ))).sum-a)*
        (∏ ℓ ∈ Finset.range (ns.length-1), (((ℓ:ℝ)+1)*b-a))*
        (ns.map (fun n : ℕ => Real.Gamma ((n:ℝ)-b)/Real.Gamma (1-b))).prod) := by
  have hr : ∀ r ∈ ns.map (fun n : ℕ => (n:ℝ)), b < r := by
    intro r hr
    obtain ⟨n,hnn,rfl⟩ := List.mem_map.mp hr
    exact hb1.trans_le (by exact_mod_cast hn n hnn)
  have he := stableOrderedDistinctMass_eppf hb hb1 ha (ns.map (fun n : ℕ => (n:ℝ)))
    (by simpa using hne) hr z
  have hae : (fun η => stableBlockProbability ns η z) =ᵐ[stableTotalBiasedLaw a b]
      (fun η => stableOrderedDistinctMass (ns.map (fun n : ℕ => (n:ℝ))) η z) := by
    apply (stableTotalBiasedLaw_absolutelyContinuous a b).ae_eq
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1,
      stablePoissonCount_simple hb hb1] with η hf hp hs
    exact stableBlockProbability_ordered ns hn η (by simpa [stableJumpMomentE] using hf) hp hs z
  rw [lintegral_congr_ae hae]
  simpa only [List.length_map,List.map_map,Function.comp_def] using he

variable {S : Type*} [MeasurableSpace S]

def markedStableTotalE (η : Measure (ℝ × S)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂η

@[fun_prop] lemma markedStableTotalE_measurable : Measurable (markedStableTotalE (S := S)) :=
  Measure.measurable_lintegral (by fun_prop)

def markedStableTotal (η : Measure (ℝ × S)) : ℝ := (markedStableTotalE η).toReal

@[fun_prop] lemma markedStableTotal_measurable : Measurable (markedStableTotal (S := S)) :=
  markedStableTotalE_measurable.ennreal_toReal

lemma markedStableTotalE_projection (η : Measure (ℝ × S)) :
    markedStableTotalE η = stableJumpMomentE 1 (η.map Prod.fst) := by
  simp only [markedStableTotalE,stableJumpMomentE,one_mul]
  rw [lintegral_map (by fun_prop) measurable_fst]

lemma markedStableTotal_projection (η : Measure (ℝ × S)) :
    markedStableTotal η = stablePoissonTotal (η.map Prod.fst) := by
  simp only [markedStableTotal,markedStableTotalE_projection,stableJumpMomentE,one_mul,stablePoissonTotal]

def markedStableMassKernel : Kernel (Measure (ℝ × S)) (ℝ × S) where
  toFun η := normalizedMeasure (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

instance markedStableMassKernel_finite : IsFiniteKernel (markedStableMassKernel (S := S)) := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹ *
    (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def markedStableCountKernel : Kernel (Measure (ℝ × S)) (ℝ × S) :=
  markedStableMassKernel.withDensity (fun η p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))

instance markedStableCountKernel_sfinite : IsSFiniteKernel (markedStableCountKernel (S := S)) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma markedStableCountKernel_eq (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel η = η := by
  rw [markedStableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun (η : Measure (ℝ × S)) (p : ℝ × S) => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))))]
  change (((η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹) •
    η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1))).withDensity
      (fun p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  have hmass : η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ =
      ENNReal.ofReal (markedStableTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal hf).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)*
      ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) =
      (fun _ : ℝ × S => ENNReal.ofReal (markedStableTotal η)) := by
    funext p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (markedStableTotal η))⁻¹ • η.withDensity
    (fun p => ENNReal.ofReal (Real.exp p.1)*ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

lemma markedStableTotalE_add_dirac (p : ℝ × S) (η : Measure (ℝ × S)) :
    markedStableTotalE (Measure.dirac p+η) = ENNReal.ofReal (Real.exp p.1)+markedStableTotalE η := by
  simp only [markedStableTotalE,lintegral_add_measure]
  rw [lintegral_dirac' _ (by fun_prop)]

lemma markedStableTotal_add_dirac (p : ℝ × S) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) :
    markedStableTotal (Measure.dirac p+η) = Real.exp p.1+markedStableTotal η := by
  rw [markedStableTotal,markedStableTotalE_add_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hf,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

lemma markedStableCountKernel_add_dirac (η : Measure (ℝ × S)) (p : ℝ × S)
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel (Measure.dirac p+η) = Measure.dirac p+η := by
  apply markedStableCountKernel_eq
  · rw [markedStableTotalE_add_dirac]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [markedStableTotal_add_dirac p η hf]; linarith [Real.exp_pos p.1]

variable [Nonempty S]
lemma markedStable_project_law (ν : Measure S) [IsProbabilityMeasure ν] (b : ℝ) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map Prod.fst) =
      poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [poissonRandomMeasureLaw_map _ measurable_fst]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

lemma markedStable_regular (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      markedStableTotalE η ≠ ⊤ ∧ 0 < markedStableTotal η := by
  have hpres : MeasurePreserving (Measure.map (Prod.fst : ℝ × S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law ν b⟩
  have he := hpres.quasiMeasurePreserving.ae ((stablePoisson_total_finite hb hb1).and (stablePoissonTotal_pos hb hb1))
  simpa only [markedStableTotalE_projection,markedStableTotal_projection,stableJumpMomentE,one_mul] using he

lemma markedStable_laplace (ν : Measure S) [IsProbabilityMeasure ν] {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have he := stablePoissonTotal_laplace_lintegral hb hb1 ht
  rw [← markedStable_project_law ν b] at he
  rw [lintegral_map (by fun_prop) (Measure.measurable_map _ measurable_fst)] at he
  simpa only [markedStableTotal_projection] using he

def markedDistinctMoment : List (ℝ × (S → ℝ≥0∞)) → {m : ℕ} → Measure (ℝ × S) → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | rf::rs, _, η, z => ∫⁻ p, if ∃ i, z i = p.1 then 0 else
      ENNReal.ofReal (Real.exp (rf.1*p.1))*rf.2 p.2*
        markedDistinctMoment rs η (Fin.cons p.1 z) ∂markedStableCountKernel η

omit [Nonempty S] in
lemma markedDistinctMoment_measurable (rs : List (ℝ × (S → ℝ≥0∞)))
    (hr : ∀ rf ∈ rs, Measurable rf.2) (m : ℕ) :
    Measurable (fun p : Measure (ℝ × S) × (Fin m → ℝ) => markedDistinctMoment rs p.1 p.2) := by
  induction rs generalizing m with
  | nil => exact measurable_const
  | cons rf rs ih =>
    let κ : Kernel (Measure (ℝ × S) × (Fin m → ℝ)) (ℝ × S) := markedStableCountKernel.comap
      (Prod.fst : Measure (ℝ × S) × (Fin m → ℝ) → Measure (ℝ × S)) measurable_fst
    have hD : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        markedDistinctMoment rs p.1.1 (Fin.cons p.2.1 p.1.2)) := by
      exact (ih (fun r hr' => hr r (List.mem_cons_of_mem rf hr')) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fin_cons measurable_snd.fst measurable_fst.snd))
    have hset : MeasurableSet {p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) |
        ∃ i, p.1.2 i = p.2.1} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    exact (measurable_const.ite hset (((by fun_prop : Measurable (fun p :
      (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) => ENNReal.ofReal (Real.exp (rf.1*p.2.1)))).mul
      ((hr rf (by simp)).comp measurable_snd.snd)).mul hD)).lintegral_kernel_prod_right' (κ := κ)

end SphericalPerceptronFreeEnergy

end

end OAI
