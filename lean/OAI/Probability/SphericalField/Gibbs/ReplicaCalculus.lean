import Mathlib
import OAI.Probability.SphericalField.Gibbs.GaussianField

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
section ReplicaCalculus
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_integral {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ)
    (F : (Fin n → S) → ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  rw [← tilt_law_pi μ hv hC hvC n t,tilt_law_integral _
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n)]

lemma tilt_replica_coordinate {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (j : Fin n) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (fun x => F (x j)) t =
      tiltMean μ v F t := by
  have := tilt_law_probability μ hv hC hvC t
  rw [tilt_replica_integral μ hv hC hvC,← tilt_law_integral μ hv hC hvC t]
  have he := measurePreserving_eval (fun _ : Fin n => tiltLaw μ v t) j
  conv_rhs => rw [← he.map_eq,integral_map he.measurable.aemeasurable hF.aestronglyMeasurable]

lemma tilt_mean_sum {ι : Type*} (s : Finset ι) {v : S → ℝ} {F : ι → S → ℝ}
    (hv : Measurable v) (hF : ∀ i ∈ s, Measurable (F i))
    {C : ℝ} {D : ι → ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ i ∈ s, ∀ x, |F i x| ≤ D i) (t : ℝ) :
    tiltMean μ v (fun x => ∑ i ∈ s, F i x) t = ∑ i ∈ s, tiltMean μ v (F i) t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [← tilt_law_integral μ hv hC hvC t]
  exact integral_finsetSum s fun i hi => Integrable.of_bound (hF i hi).aestronglyMeasurable
    (D i) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD i hi x)

lemma tilt_replica_sum {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D)
    (n : ℕ) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (replicaPotential F n) t =
      n * tiltMean μ v F t := by
  change tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n)
    (fun x => ∑ i, F (x i)) t = _
  rw [tilt_mean_sum (Measure.pi fun _ : Fin n => μ) Finset.univ
    (F := fun i (x : Fin n → S) => F (x i)) (replicaPotential_measurable hv n)
    (fun i _ => hF.comp (measurable_pi_apply i)) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n) (fun i _ x => hFD (x i))]
  simp_rw [tilt_replica_coordinate μ hv hF hC hvC]
  simp

lemma tilt_replica_new_product {replicaCount : ℕ} {v F : S → ℝ}
    {G : (Fin replicaCount → S) → ℝ}
    (hv : Measurable v) (hF : Measurable F) (hG : Measurable G)
    {C D B : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin (replicaCount+1) => μ) (replicaPotential v (replicaCount+1))
      (fun x => F (x 0) * G (fun j => x j.succ)) t =
      tiltMean μ v F t * tiltMean (Measure.pi fun _ : Fin replicaCount => μ)
        (replicaPotential v replicaCount) G t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [tilt_replica_integral μ hv hC hvC]
  rw [← tilt_law_integral μ hv hC hvC t]
  let ν := tiltLaw μ v t
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (replicaCount+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0) * G (fun j => x j.succ))]
  change (∫ p : S × (Fin replicaCount → S),
    F ((Fin.insertNth 0 p.1 p.2 : Fin (replicaCount+1) → S) 0) *
    G (fun j => (Fin.insertNth 0 p.1 p.2 : Fin (replicaCount+1) → S) j.succ)
      ∂ν.prod (Measure.pi fun _ => ν)) = _
  simp only [Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable D
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD x)
  have hGi : Integrable G (Measure.pi fun _ : Fin replicaCount => ν) := Integrable.of_bound
    hG.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGB x)
  rw [integral_prod _ (hFi.mul_prod hGi)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

omit [MeasurableSpace S] in
lemma gaussianField_replica (m n : ℕ) (v : Fin m → S → ℝ) (g : Fin m → ℝ)
    (x : Fin n → S) :
    replicaPotential (gaussianField m v g) n x =
      gaussianField m (fun i => replicaPotential (v i) n) g x := by
  simp only [gaussianField,replicaPotential,Finset.mul_sum]
  exact Finset.sum_comm

omit [MeasurableSpace S] in
lemma replicaPotential_add_field (m n : ℕ) (v : Fin m → S → ℝ) (h : S → ℝ)
    (s : ℝ) (g : Fin m → ℝ) :
    replicaPotential (fun x => h x+s*gaussianField m v g x) n =
      fun x => replicaPotential h n x +
        s*gaussianField m (fun i => replicaPotential (v i) n) g x := by
  funext x
  simp only [replicaPotential,Finset.sum_add_distrib,Finset.mul_sum,gaussianField]
  congr 1
  exact Finset.sum_comm

end ReplicaCalculus

section ReplicaField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma gaussian_replica_coordinate_ibp (m n : ℕ) (i : Fin (m+1)) (j : Fin n)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {G : (Fin n → S) → ℝ}
    (hv : ∀ l, Measurable (v l)) (hh : Measurable h) (hG : Measurable G)
    {C A D : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hvC : ∀ l x, |v l x| ≤ C) (hhA : ∀ x, |h x| ≤ A) (hGD : ∀ x, |G x| ≤ D)
    (s : ℝ) :
    let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
    (∫ g, g i * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential (H g) n)
      (fun x => v i (x j)*G x) 1 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    s * ∫ g,
      tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential (H g) n)
        (fun x => replicaPotential (v i) n x * (v i (x j)*G x)) 1 -
      n * tiltMean (Measure.pi fun _ : Fin (n+1) => μ) (replicaPotential (H g) (n+1))
        (fun x => v i (x 0) * (v i (x j.succ)*G (fun l => x l.succ))) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
  have hFi : Measurable (fun x : Fin n → S => v i (x j)*G x) :=
    ((hv i).comp (measurable_pi_apply j)).mul hG
  have hFB (x : Fin n → S) : |v i (x j)*G x| ≤ C*D := by
    rw [abs_mul]; exact mul_le_mul (hvC i (x j)) (hGD x) (abs_nonneg _) hC
  have hi := gaussian_field_coordinate_ibp (Measure.pi fun _ : Fin n => μ) (n := m) i
    (fun l => replicaPotential_measurable (hv l) n) (replicaPotential_measurable hh n) hFi
    (mul_nonneg (Nat.cast_nonneg n) hC) (mul_nonneg (Nat.cast_nonneg n) hA)
    (mul_nonneg hC hD) (fun l => replicaPotential_bound (hvC l) n)
    (replicaPotential_bound hhA n) hFB s
  simp_rw [← replicaPotential_add_field] at hi
  refine hi.trans ?_
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun g => ?_
  have hHm : Measurable (H g) := hh.add (((gaussianField_measurable hv).comp
    (measurable_const.prodMk measurable_id)).const_mul s)
  have hHb (x : S) : |H g x| ≤ A+|s| *((∑ l, |g l|)*C) := by
    exact (abs_add_le _ _).trans (add_le_add (hhA x) (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (gaussianField_bound hvC g x) (abs_nonneg s)))
  change _ - _ * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential (H g) n)
    (replicaPotential (v i) n) 1 = _
  rw [tilt_replica_sum μ hHm (hv i) (by positivity) hHb (hvC i)]
  change _ = _ - (n : ℝ) * tiltMean (Measure.pi fun _ : Fin (n+1) => μ)
    (replicaPotential (H g) (n+1))
    (fun x => v i (x 0) * ((fun y : Fin n → S => v i (y j)*G y) (fun l => x l.succ))) 1
  rw [tilt_replica_new_product μ hHm (hv i) hFi (by positivity) hHb (hvC i) hFB]
  ring

end ReplicaField

lemma gamma_lintegral_positive_scale {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(a-1) * Real.exp (-t*r))) =
      ENNReal.ofReal (r^(-a) * Real.Gamma a) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1) * Real.exp (-t*r)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a-1)
      (b := r) (by linarith) (by norm_num) hr using 1
    funext t
    simp only [Real.rpow_one]
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  congr 1
  calc
    (∫ t : ℝ in Ioi 0, t^(a-1)*Real.exp (-t*r)) =
      ∫ t : ℝ in Ioi 0, t^(a-1)*Real.exp (-(r*t)) := by
        congr 1; funext t; congr 2; ring
    _ = (1/r)^a * Real.Gamma a := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
    _ = r^(-a) * Real.Gamma a := by
      rw [one_div,Real.inv_rpow hr.le,Real.rpow_neg hr.le]

lemma integrable_rpow_neg_of_laplace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {S : Ω → ℝ}
    (hS : Measurable S) (hpos : ∀ᵐ ω ∂P, 0 < S ω)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hLap : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t*S ω) ∂P) = Real.exp (-c*t^b))
    {a : ℝ} (ha : 0 < a) : Integrable (fun ω => S ω ^ (-a)) P := by
  let K := fun (ω : Ω) (t : ℝ) => ENNReal.ofReal (t^(a-1)*Real.exp (-t*S ω))
  have hm : Measurable (Function.uncurry K) := by dsimp [K]; fun_prop
  have hexp (t : ℝ) (ht : 0 < t) : Integrable (fun ω => Real.exp (-t*S ω)) P := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hpos] with ω hω
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hinner (t : ℝ) (ht : 0 < t) :
      (∫⁻ ω, K ω t ∂P) = ENNReal.ofReal (t^(a-1)*Real.exp (-c*t^b)) := by
    dsimp [K]
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hexp t ht) (ae_of_all _ fun _ => (Real.exp_pos _).le),
      hLap t ht]
  have hi : (∫⁻ t : ℝ in Ioi 0, ∫⁻ ω, K ω t ∂P) ≠ ⊤ := by
    have hfinite := (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := a-1) (p := b) (b := c) (by linarith) hb hc).hasFiniteIntegral
    have hfinite' : (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (t^(a-1)*Real.exp (-c*t^b))) < ⊤ := by
      apply (hasFiniteIntegral_iff_ofReal _).mp hfinite
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    apply ne_top_of_le_ne_top hfinite'.ne
    apply le_of_eq
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hinner t ht
  have hi' : (∫⁻ ω, ENNReal.ofReal (S ω^(-a)*Real.Gamma a) ∂P) ≠ ⊤ := by
    rw [← lintegral_congr_ae (hpos.mono fun ω hω => gamma_lintegral_positive_scale ha hω)]
    change (∫⁻ ω, (∫⁻ t : ℝ in Ioi 0, K ω t) ∂P) ≠ ⊤
    rw [lintegral_lintegral_swap hm.aemeasurable]
    exact hi
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ S ω^(-a)*Real.Gamma a :=
    hpos.mono fun ω hω => mul_nonneg (Real.rpow_nonneg hω.le _) (Real.Gamma_pos_of_pos ha).le
  have hprod : Integrable (fun ω => S ω^(-a)*Real.Gamma a) P :=
    ⟨(hS.pow_const (-a) |>.mul_const (Real.Gamma a)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnonneg).mpr hi'.lt_top⟩
  have hh := hprod.div_const (Real.Gamma a)
  simpa only [mul_div_assoc, div_self (Real.Gamma_pos_of_pos ha).ne', mul_one] using hh

lemma stablePoissonTotal_negative_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (ha : 0 < a) : Integrable (fun η => stablePoissonTotal η ^ (-a))
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  exact integrable_rpow_neg_of_laplace _ stablePoissonTotal_measurable
    (stablePoissonTotal_pos hb0 hb1) hb0
    (ENNReal.toReal_pos (stableLaplaceConstant_positive hb0).ne' (stableLaplaceConstant_finite hb0 hb1))
    (fun _ ht => stablePoissonTotal_laplace hb0 hb1 ht) ha

end SphericalPerceptron
end
end

end OAI
