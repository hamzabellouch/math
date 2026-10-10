import Mathlib
import OAI.Probability.SKRatio.Calculus.RowControl

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def gauge (x : Spin n) (g : Disorder n) : Disorder n :=
  fun e => spinValue (x e.1.1)*g e*spinValue (x e.1.2)

lemma coupling_gauge (x : Spin n) (g : Disorder n) :
    coupling (gauge x g) = signConjugate x (coupling g) := by
  funext i j
  change coupling (gauge x g) i j = spinValue (x i)*coupling g i j*spinValue (x j)
  simp only [coupling, gauge]
  split_ifs <;> ring

lemma gauge_twice (x : Spin n) (g : Disorder n) : gauge x (gauge x g) = g := by
  funext e
  unfold gauge
  have h₁ := spin_sq x e.1.1
  have h₂ := spin_sq x e.1.2
  change spinValue (x e.1.1)^2 = 1 at h₁
  change spinValue (x e.1.2)^2 = 1 at h₂
  calc
    _ = (spinValue (x e.1.1))^2*(spinValue (x e.1.2))^2*g e := by ring
    _ = _ := by rw [h₁,h₂,one_mul,one_mul]

lemma gauge_continuous (x : Spin n) : Continuous (gauge x) := by
  apply continuous_pi
  intro e
  exact (continuous_apply e |>.const_mul _).mul_const _

lemma hamiltonian_gauge (x y : Spin n) (g : Disorder n) :
    hamiltonian (gauge x g) 0 y = hamiltonian g 0 (signProduct x y) := by
  simp only [hamiltonian,coupling_gauge,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change spin y i*(spin x i*coupling g i j*spin x j)*spin y j =
    spin (signProduct x y) i*coupling g i j*spin (signProduct x y) j
  rw [spin_signProduct,spin_signProduct]
  ring

lemma hamiltonian_edges (g : Disorder n) (x : Spin n) :
    hamiltonian g 0 x = ∑ e : Edge n, spinValue (x e.1.1)*g e*spinValue (x e.1.2) := by
  let f : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then spinValue (x p.1)*g ⟨p,h⟩*spinValue (x p.2) else 0
  have hh (i j : Fin n) : spinValue (x i)*coupling g i j*spinValue (x j) = f (i,j)+f (j,i) := by
    dsimp [f,coupling]
    split_ifs with h₁ h₂ h₂ <;> try omega
    all_goals ring
  have hs : ∑ p, f p = ∑ e : Edge n, spinValue (x e.1.1)*g e*spinValue (x e.1.2) := by
    apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1 < p.2})
    · intro p hp
      simp [f,show p.1 < p.2 from hp]
    · intro p hp
      simp [f,show ¬p.1 < p.2 from hp]
  have he : (∑ i : Fin n, ∑ j : Fin n, f (j,i)) = ∑ i : Fin n, ∑ j : Fin n, f (i,j) :=
    Finset.sum_comm
  simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,hh,
    Finset.sum_add_distrib]
  rw [he,←Fintype.sum_prod_type,hs]
  ring

lemma gaussianReal_tilt (μ : ℝ) (v : ℝ≥0) (a : ℝ) :
    (gaussianReal μ v).withDensity
      (fun z => ENNReal.ofReal (exp (a*z-(a*μ+(v:ℝ)*a^2/2)))) =
      gaussianReal (μ+(v:ℝ)*a) v := by
  by_cases hv : v=0
  · subst v
    simp [dirac_withDensity]
  have hvr : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  rw [gaussianReal_of_var_ne_zero _ hv,gaussianReal_of_var_ne_zero _ hv,
    ←withDensity_mul volume (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext z
  simp only [Pi.mul_apply,gaussianPDF_def,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def,mul_assoc,←exp_add]
  congr 2
  field_simp
  ring

lemma lintegral_fin_nat_prod_eq_prod {k : ℕ} {E : Fin k → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin k) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin k) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin k) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin k) → E i.succ),
          f 0 x.1 * ∏ i : Fin k, f i.succ (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        let e : E 0 × ((i : Fin k) → E i.succ) ≃ᵐ ((i : Fin (k+1)) → E i) :=
          (MeasurableEquiv.piFinSuccAbove E 0).symm
        have he : MeasurePreserving e
            ((μ 0).prod (Measure.pi (fun i => μ i.succ))) (Measure.pi μ) :=
          (measurePreserving_piFinSuccAbove μ 0).symm
        rw [← he.lintegral_comp_emb e.measurableEmbedding]
        congr 1
        funext x
        change (∏ i, f i (Fin.insertNthEquiv E 0 x i)) = _
        rw [Fin.insertNthEquiv_zero]
        change (∏ i, f i (Fin.cons x.1 x.2 i)) = _
        rw [Fin.prod_univ_succ]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin k, ∫⁻ x, f i.succ x ∂μ i.succ := by
        rw [lintegral_prod_mul (hf 0).aemeasurable
          (g := fun x : (i : Fin k) → E i.succ => ∏ i, f i.succ (x i))
          ((Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))).aemeasurable)]
        rw [ih _ (fun i => hf _)]
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod _ (fun i => hf _)

lemma product_tilt {ι : Type*} [Fintype ι] (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    (Measure.pi (fun i => gaussianReal (μ i) (v i))).withDensity
      (fun z : ι → ℝ => ENNReal.ofReal (exp (∑ i : ι, (a i*z i-(a i*μ i+(v i:ℝ)*(a i)^2/2))))) =
      Measure.pi (fun i => gaussianReal (μ i+(v i:ℝ)*a i) (v i)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  simp only [exp_sum,ENNReal.ofReal_prod_of_nonneg (fun _ _ => (exp_pos _).le)]
  rw [lintegral_fintype_prod_eq_prod
    (fun i (z : ℝ) => ENNReal.ofReal (exp (a i*z-(a i*μ i+(v i:ℝ)*(a i)^2/2))))
    (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro i _
  rw [←gaussianReal_tilt (μ i) (v i) (a i),withDensity_apply _ (hs i)]

def law (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal (β^2/(n:ℝ)) (Real.toNNReal (β^2/n)))

instance law_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (law β n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

def normalizingExponent (β : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (Edge n) : ℝ)*(β^2/n)/2

lemma law_density (β : ℝ) (n : ℕ) :
    (disorderLaw β n).withDensity
      (fun g => ENNReal.ofReal (exp (hamiltonian g 0 (plusSpin n)-normalizingExponent β n))) =
      law β n := by
  have hv : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have ht := product_tilt (ι := Edge n) (fun _ => 0) (fun _ => Real.toNNReal (β^2/n)) (fun _ => 1)
  simpa only [law,disorderLaw,hamiltonian_edges,plusSpin,spinValue,↓reduceIte,
    one_mul,mul_one,one_pow,zero_mul,zero_add,hv,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,normalizingExponent,mul_div_assoc] using ht

lemma gauge_preserving (β : ℝ) (x : Spin n) :
    MeasurePreserving (gauge x) (disorderLaw β n) (disorderLaw β n) := by
  refine ⟨(gauge_continuous x).measurable,?_⟩
  unfold disorderLaw gauge
  rw [Measure.pi_map_pi (f := fun (e : Edge n) (z : ℝ) => spinValue (x e.1.1)*z*spinValue (x e.1.2))
    (by intro e; fun_prop)]
  congr 1
  funext e
  cases x e.1.1 <;> cases x e.1.2 <;>
    simp [spinValue,gaussianReal_map_neg]

lemma integrable_exp_linear {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z : ι → ℝ => exp (∑ i, a i*z i))
      (Measure.pi (fun i => gaussianReal (μ i) (v i))) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

lemma integral_exp_linear {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (v : ι → ℝ≥0) (a : ι → ℝ) :
    (∫ z : ι → ℝ, exp (∑ i, a i*z i) ∂Measure.pi (fun i => gaussianReal (μ i) (v i))) =
      exp (∑ i, (a i*μ i+(v i:ℝ)*(a i)^2/2)) := by
  simp_rw [exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mgf,id_eq,mul_comm (μ i) (a i)] using
    mgf_gaussianReal (μ := μ i) (v := v i) (X := id) (p := gaussianReal (μ i) (v i))
    (by simp) (a i)

lemma weight_linear (g : Disorder n) (x : Spin n) :
    weight g 0 x = exp (∑ e : Edge n, (spinValue (x e.1.1)*spinValue (x e.1.2))*g e) := by
  rw [weight,hamiltonian_edges]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma weight_integrable (β : ℝ) (x : Spin n) :
    Integrable (fun g => weight g 0 x) (disorderLaw β n) := by
  simp_rw [weight_linear]
  exact integrable_exp_linear _ _ _

lemma integral_weight (β : ℝ) (x : Spin n) :
    (∫ g, weight g 0 x ∂disorderLaw β n) = exp (normalizingExponent β n) := by
  simp_rw [weight_linear]
  rw [disorderLaw,integral_exp_linear]
  have hs (e : Edge n) : (spinValue (x e.1.1)*spinValue (x e.1.2))^2 = 1 := by
    change (spin x e.1.1*spin x e.1.2)^2 = 1
    rw [mul_pow,spin_sq,spin_sq,mul_one]
  simp only [mul_zero,zero_add,hs,mul_one,Real.coe_toNNReal _
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)),Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,normalizingExponent,mul_div_assoc]

lemma partition_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => partition g 0) (disorderLaw β n) :=
  integrable_finsetSum _ (fun x _ => weight_integrable β x)

lemma integral_partition (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, partition g 0 ∂disorderLaw β n) =
      (2:ℝ)^n*exp (normalizingExponent β n) := by
  change (∫ g, ∑ x : Spin n, weight g 0 x ∂disorderLaw β n) = _
  rw [integral_finsetSum _ (fun x _ => weight_integrable β x)]
  simp only [integral_weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

def badWeight (B : Set (Disorder n)) (g : Disorder n) : ℝ :=
  ∑ x : Spin n, if gauge x g ∈ B then weight g 0 x else 0

lemma badWeight_nonneg (B : Set (Disorder n)) (g : Disorder n) : 0 ≤ badWeight B g := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact (weight_pos g 0 x).le
  · rfl

lemma badWeight_le_partition (B : Set (Disorder n)) (g : Disorder n) :
    badWeight B g ≤ partition g 0 := by
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · rfl
  · exact (weight_pos g 0 x).le

lemma badWeight_integrable (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    Integrable (badWeight B) (disorderLaw β n) := by
  apply integrable_finsetSum
  intro x _
  exact (weight_integrable β x).indicator (hB.preimage (gauge_continuous x).measurable)

lemma integral_planted_weight (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    (∫ g, if g ∈ B then weight g 0 (plusSpin n) else 0 ∂disorderLaw β n) =
      exp (normalizingExponent β n)*(law β n).real B := by
  have hn := law_density β n
  have he := congrArg (fun μ : Measure (Disorder n) => μ B) hn
  rw [withDensity_apply _ hB] at he
  have hi : Integrable (fun g : Disorder n => exp (hamiltonian g 0 (plusSpin n)-
      normalizingExponent β n)) (disorderLaw β n) := by
    simp only [exp_sub]
    exact (weight_integrable β (plusSpin n)).div_const _
  have he' := congrArg ENNReal.toReal he
  rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun g => (exp_pos _).le))
    (hi.restrict).aestronglyMeasurable] at he'
  simp only [exp_sub,integral_div] at he'
  change (∫ g, B.indicator (fun g => weight g 0 (plusSpin n)) g ∂disorderLaw β n) = _
  rw [integral_indicator hB]
  exact (div_eq_iff (exp_ne_zero _)).mp he' |>.trans (mul_comm _ _)

lemma integral_badWeight (β : ℝ) {B : Set (Disorder n)} (hB : MeasurableSet B) :
    (∫ g, badWeight B g ∂disorderLaw β n) =
      ((2:ℝ)^n*exp (normalizingExponent β n))*(law β n).real B := by
  unfold badWeight
  rw [integral_finsetSum _ (fun x _ => show
    Integrable (fun g => if gauge x g ∈ B then weight g 0 x else 0) (disorderLaw β n) from by
      change Integrable ((gauge x ⁻¹' B).indicator (fun g => weight g 0 x)) (disorderLaw β n)
      exact (weight_integrable β x).indicator (hB.preimage (gauge_continuous x).measurable))]
  have he (x : Spin n) :
      (∫ g, if gauge x g ∈ B then weight g 0 x else 0 ∂disorderLaw β n) =
        exp (normalizingExponent β n)*(law β n).real B := by
    have hw (g : Disorder n) : weight (gauge x g) 0 (plusSpin n) = weight g 0 x := by
      rw [weight,hamiltonian_gauge,signProduct_plus,←weight]
    rw [←integral_planted_weight β hB]
    let e : Disorder n ≃ᵐ Disorder n :=
      { toFun := gauge x
        invFun := gauge x
        left_inv := gauge_twice x
        right_inv := gauge_twice x
        measurable_toFun := (gauge_continuous x).measurable
        measurable_invFun := (gauge_continuous x).measurable }
    have hh := (gauge_preserving β x).integral_comp e.measurableEmbedding
      (fun g => if g ∈ B then weight g 0 (plusSpin n) else 0)
    simpa only [hw] using hh
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,mul_assoc]

end SKRatio.Planted

end

end OAI
