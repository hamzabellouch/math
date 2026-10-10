import Mathlib
import OAI.Probability.SKGap.Matrix.NormalLogDensityCentered

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def scalarEmpirical (y : ι → ℝ) (t σ : ℝ) : ScalarPoint := (empiricalLaw y,(t,σ))

def scalarIntegrand (j t σ : ℝ) (y : ι → ℝ) : ℝ :=
  exp ((Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ))*
    productNormal (scalarD j (scalarEmpirical y t σ)) (scalarS j (scalarEmpirical y t σ)) y

lemma scalarA_empirical (y : ι → ℝ) (j t σ : ℝ) :
    scalarA j (scalarEmpirical y t σ) = (Fintype.card ι:ℝ)⁻¹ *
      ∑ i, (y i-scalarD j (scalarEmpirical y t σ))*tanh (y i) := by
  unfold scalarA scalarM scalarEmpirical
  simp only [integral_empiricalLaw, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma empirical_scalar_cauchy (y : ι → ℝ) (j t σ : ℝ) :
    (scalarA j (scalarEmpirical y t σ))^2 ≤ scalarQMoment (empiricalLaw y)*
      ((Fintype.card ι:ℝ)⁻¹ * ∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => y i-scalarD j (scalarEmpirical y t σ)) (fun i => tanh (y i))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (Fintype.card ι:ℝ)⁻¹)
  rw [scalarA_empirical, scalarQMoment, integral_empiricalLaw]
  nlinarith only [hh]

lemma scalar_empirical_quadratic_envelope (y : ι → ℝ) {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hs : 0 < scalarS j (scalarEmpirical y t σ)) :
    (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤
      3/(8*scalarS j (scalarEmpirical y t σ)) *
        (∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2)+3*(Fintype.card ι:ℝ)*j/2 := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have h := scalar_quadratic_envelope hj (scalarQMoment_bounds (empiricalLaw y)).1
    (scalarQMoment_bounds (empiricalLaw y)).2 hs (scalar_consistency (p := scalarEmpirical y t σ) ht)
    (show 0 ≤ (Fintype.card ι:ℝ)⁻¹*∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2 by positivity)
    (empirical_scalar_cauchy y j t σ)
  have hh := mul_le_mul_of_nonneg_left h hn.le
  change (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤ _ at hh
  convert hh using 1
  field_simp

lemma scalar_empirical_parameter_bounds (y : ι → ℝ) {j t σ T : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |scalarD j (scalarEmpirical y t σ)| ≤ T+j ∧ scalarS j (scalarEmpirical y t σ) ≤ T+1+j := by
  have hM := scalarM_bounds (empiricalLaw y)
  have hq := (scalarQMoment_bounds (empiricalLaw y)).2
  constructor
  · unfold scalarD scalarEmpirical
    dsimp only
    calc
      |t+j*scalarM (empiricalLaw y)| ≤ |t|+|j*scalarM (empiricalLaw y)| := abs_add_le _ _
      _ ≤ T+j := by
        rw [abs_of_nonneg ht, abs_mul, abs_of_nonneg hj]
        nlinarith
  · unfold scalarS scalarEmpirical
    dsimp only
    have hsq : σ^2 ≤ 1 := by nlinarith
    nlinarith

theorem scalar_integrand_envelope {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (y : ι → ℝ) {t σ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hsl : smin ≤ scalarS j (scalarEmpirical y t σ)) :
    scalarIntegrand j t σ y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin))-
        (1/(16*(T+1+j)))*∑ i, (y i)^2) := by
  have hb := scalar_empirical_parameter_bounds y hj ht htT hσ hσ1
  have hd : (scalarD j (scalarEmpirical y t σ))^2 ≤ (T+j)^2 := by
    have hD : 0 ≤ T+j := add_nonneg hT hj
    have hsq := (sq_le_sq₀ (abs_nonneg _) hD).mpr hb.1
    simpa only [sq_abs] using hsq
  exact gaussian_pointwise_envelope y hsmin hsl hb.2 hd
    (scalar_empirical_quadratic_envelope y hj ht (hsmin.trans_le hsl))

theorem scalar_integrand_tail {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (L : ℝ) : ∃ R > 0, ∀ t ∈ Icc 0 T, ∀ σ ∈ Icc 0 1,
      ∀ E : Set (ι → ℝ), MeasurableSet E →
      (∀ y ∈ E, smin ≤ scalarS j (scalarEmpirical y t σ)) →
      (∀ y ∈ E, (Fintype.card ι:ℝ)*R ≤ ∑ i, (y i)^2) →
      (∫⁻ y in E, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
        ENNReal.ofReal (exp (-L*(Fintype.card ι:ℝ))) := by
  let c := 1/(16*(T+1+j))
  let C := |log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨R,hR,hrate⟩ := choose_quadratic_tail_radius (C := C) hc L
  refine ⟨R,hR,?_⟩
  intro t ht σ hσ E hE hs htE
  have he := quadratic_envelope_tail (C := C) hc hE (scalarIntegrand j t σ)
    (fun y hy => scalar_integrand_envelope hj hT hsmin y ht.1 ht.2 hσ.1 hσ.2 (hs y hy)) htE
  refine he.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  have h := mul_le_mul_of_nonneg_left hrate (show (0:ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _)
  nlinarith only [h]

end SKGap

namespace SKGap

lemma empirical_momentBall {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) {R : ℝ} (_hR : 0 ≤ R)
    (h : ∑ i, (y i)^2 ≤ (Fintype.card ι:ℝ)*R) : empiricalLaw y ∈ momentBall R := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂empiricalLaw y) ≤ ENNReal.ofReal R
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_empiricalLaw y _) (ae_of_all _ sq_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_empiricalLaw]
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hh

def scalarBox (j R T smin : ℝ) : Set ScalarPoint :=
  (momentBall R ×ˢ (Icc 0 T ×ˢ Icc 0 1)) ∩ {p | smin ≤ scalarS j p}

lemma isCompact_scalarBox (j R T smin : ℝ) : IsCompact (scalarBox j R T smin) :=
  ((isCompact_momentBall R).prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_le continuous_const (continuous_scalarS j))

lemma scalar_compact_nonpositive {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K) (hmom : K ⊆ scalarMomentDomain R)
    (ht : ∀ p ∈ K, 0 ≤ p.2.1) (hs : ∀ p ∈ K, 0 < scalarS j p)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ z : (Fin n → ℝ) → ScalarPoint, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, (z y).1 = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*scalarPsi j (z y))*
        productNormal (scalarD j (z y)) (scalarS j (z y)) y)) ≤ ENNReal.ofReal (exp (ε*(n:ℝ))) := by
  obtain ⟨N,hN⟩ := gaussian_compact_rate hK (P := fun p : ScalarPoint => p.1)
    continuous_fst.continuousOn (continuous_scalarD j).continuousOn (continuous_scalarS j).continuousOn
    (continuousOn_scalarPsi_of_pos hj.le hR hmom hs) hs R (ε/2)
    (fun p hp => scalar_weak_test (hmom hp) hj hj1 (ht p hp) (hs p hp) (half_pos hε)) (half_pos hε)
  refine ⟨N,?_⟩
  intro n hn hn' z E hE hz hemp hsum
  convert hN n hn hn' z E hE hz hemp hsum using 1
  congr 1
  ring_nf

theorem scalar_uniform_tail {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (L : ℝ) : ∃ R > 0, ∀ n : ℕ, ∀ hn : 0 < n,
      ∀ t ∈ Icc 0 T, ∀ σ ∈ Icc 0 1, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∀ y ∈ E, (n:ℝ)*R ≤ ∑ i, (y i)^2) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-L*(n:ℝ))) := by
  let c := 1/(16*(T+1+j))
  let C := |log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨R,hR,hrate⟩ := choose_quadratic_tail_radius (C := C) hc L
  refine ⟨R,hR,?_⟩
  intro n hn t ht σ hσ E hE hs htE
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he := quadratic_envelope_tail (C := C) hc hE (scalarIntegrand j t σ)
    (fun y hy => scalar_integrand_envelope hj hT hsmin y ht.1 ht.2 hσ.1 hσ.2 (hs y hy))
    (by simpa only [Fintype.card_fin] using htE)
  simp only [Fintype.card_fin] at he
  refine he.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  have h := mul_le_mul_of_nonneg_left hrate (show (0:ℝ) ≤ n from Nat.cast_nonneg _)
  nlinarith only [h]

lemma lintegral_split_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) (E B : Set α) :
    (∫⁻ x in E, f x ∂μ) ≤ (∫⁻ x in E ∩ B, f x ∂μ)+(∫⁻ x in E ∩ Bᶜ, f x ∂μ) := by
  have h : E = (E ∩ B) ∪ (E ∩ Bᶜ) := by aesop
  conv_lhs => rw [h]
  exact lintegral_union_le _ _ _

theorem scalar_unrestricted_rate {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 ≤ T) (hsmin : 0 < smin) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T, ∀ σ ∈ Icc 0 1,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (ε*(n:ℝ))) := by
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT hsmin 1
  have hbox : scalarBox j R T smin ⊆ scalarMomentDomain R := fun p hp => ⟨hp.1.1,mem_univ _⟩
  obtain ⟨N,hN⟩ := scalar_compact_nonpositive hj hj1 hR.le (isCompact_scalarBox j R T smin)
    hbox (fun p hp => hp.1.2.1.1) (fun p hp => hsmin.trans_le hp.2) (half_pos hε)
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 2 (half_pos hε)
  refine ⟨max N M,?_⟩
  intro n hn hn' t ht σ hσ E hE hs
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  let B : Set (Fin n → ℝ) := {y | ∑ i, (y i)^2 ≤ (n:ℝ)*R}
  have hB : MeasurableSet B := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hc := hN n (le_trans (le_max_left _ _) hn) hn' (fun y => scalarEmpirical y t σ)
    (E ∩ B) (hE.inter hB) (fun y hy => ⟨⟨empirical_momentBall y hR.le
      (by simpa only [Fintype.card_fin] using (show ∑ i, (y i)^2 ≤ (n:ℝ)*R from hy.2)),ht,hσ⟩,hs y hy.1⟩)
    (fun _ _ => rfl) (fun _ hy => hy.2)
  have hc' : (∫⁻ y in E ∩ B, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
      ENNReal.ofReal (exp ((ε/2)*(n:ℝ))) := by
    simpa only [scalarIntegrand, Fintype.card_fin] using hc
  have htail := hTail n hn' t ht σ hσ (E ∩ Bᶜ) (hE.inter hB.compl)
    (fun y hy => hs y hy.1) (fun y hy => le_of_lt (not_le.mp hy.2))
  have he : exp (-(1:ℝ)*(n:ℝ)) ≤ exp ((ε/2)*(n:ℝ)) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have htotal := (lintegral_split_le volume (fun y => ENNReal.ofReal (scalarIntegrand j t σ y)) E B).trans
    (add_le_add hc' (htail.trans (ENNReal.ofReal_le_ofReal he)))
  have hadd : ENNReal.ofReal (exp ((ε/2)*(n:ℝ)))+ENNReal.ofReal (exp ((ε/2)*(n:ℝ))) =
      ENNReal.ofReal (2*exp ((n:ℝ)*(ε/2))) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
    congr 1
    ring_nf
  rw [hadd] at htotal
  refine htotal.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hM n (le_trans (le_max_right _ _) hn) (ε/2) using 1
  congr 1
  ring

end SKGap

end
end
end
end
end
end
end
end

end OAI
