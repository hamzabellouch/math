import Mathlib
import OAI.Probability.SKGap.Localization.ScalarConsistency
import OAI.Probability.SKGap.Gaussian.GaussianTiltMass

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
namespace SKGap

lemma scalar_small_noise_tests {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∀ p ∈ K, p.2.2 ≤ δ → ∃ f : ℝ →ᵇ ℝ,
      scalarPsi j p-(∫ y, f y ∂p.1)+
        log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < -a := by
  have hw (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p)) K :=
    (continuousOn_scalar_test hR hj.le f).mono (fun p hp => ⟨hmom hp,hs p hp⟩)
  have hW (p : ScalarPoint) (hp : p ∈ K) (hz : p.2.2 = 0) :
      ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p) < 0 := by
    have hng : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal := by
      intro he
      exact hne p hp hz (scalar_gaussian_curve hj hj1 (ht p hp) hz (hs p hp).le he)
    obtain ⟨f,hf⟩ := scalar_strict_test (hmom hp) hj hj1 (ht p hp) (hs p hp) hng
    rw [← scalarLogMoment_eq f _ (hs p hp).le] at hf
    exact ⟨f,hf⟩
  obtain ⟨a,ha,δ,hδ,hall⟩ := compact_small_noise_witness hK _ hw
    (σ := fun p : ScalarPoint => p.2.2) (by fun_prop) hσ hW
  refine ⟨a,ha,δ,hδ,?_⟩
  intro p hp hδp
  obtain ⟨f,hf⟩ := hall p hp hδp
  rw [scalarLogMoment_eq f _ (hs p hp).le] at hf
  exact ⟨f,hf⟩

lemma continuousOn_scalarPsi_of_pos {j R : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hmom : K ⊆ scalarMomentDomain R) (hs : ∀ p ∈ K, 0 < scalarS j p) :
    ContinuousOn (scalarPsi j) K := (continuousOn_scalarPsi hR j).mono (by
      intro p hp
      exact ⟨hmom hp,(hs p hp).ne',ne_of_gt (add_pos_of_pos_of_nonneg (hs p hp)
        (mul_nonneg hj (scalarQMoment_bounds p.1).1))⟩)

theorem scalar_compact_isolation {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ z : (Fin n → ℝ) → ScalarPoint, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K ∧ (z y).2.2 ≤ δ) →
      (∀ y ∈ E, (z y).1 = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*scalarPsi j (z y))*
        productNormal (scalarD j (z y)) (scalarS j (z y)) y)) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨a,ha,δ,hδ,hW⟩ := scalar_small_noise_tests hj hj1 hR hK hmom ht hσ hs hne
  let K' := K ∩ {p : ScalarPoint | p.2.2 ≤ δ}
  have hK' : IsCompact K' := hK.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hmom' : K' ⊆ scalarMomentDomain R := fun _ hp => hmom hp.1
  have hs' : ∀ p ∈ K', 0 < scalarS j p := fun p hp => hs p hp.1
  obtain ⟨N,hN⟩ := gaussian_compact_rate hK' (P := fun p : ScalarPoint => p.1)
    continuous_fst.continuousOn (continuous_scalarD j).continuousOn (continuous_scalarS j).continuousOn
    (continuousOn_scalarPsi_of_pos hj.le hR hmom' hs') hs' R (-a)
    (fun p hp => hW p hp.1 hp.2) (half_pos ha)
  refine ⟨a/2,half_pos ha,δ,hδ,N,?_⟩
  intro n hn hn' z E hE hz hemp hmomE
  have hh := hN n hn hn' z E hE hz hemp hmomE
  convert hh using 1
  congr 1
  ring_nf

end SKGap
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

lemma scalar_quadratic_envelope {j q a s Q : ℝ} (hj : 0 ≤ j) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) (hs : 0 < s) (hc : j*q ≤ s) (hQ : 0 ≤ Q) (ha : a^2 ≤ q*Q) :
    j*(a-s*(1-q))^2/(2*s*(s+j*q)) ≤ 3*Q/(8*s)+3*j/2 := by
  have hS : 0 < s+j*q := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hsq : (a-s*(1-q))^2 ≤ 3/2*a^2+3*(s*(1-q))^2 := by
    nlinarith [sq_nonneg (a+2*s*(1-q))]
  have hb : (1-q)^2 ≤ 1 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 3/2*j by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc hQ
  have hss := mul_nonneg hs.le (mul_nonneg hj hq)
  have hsqj := mul_le_mul_of_nonneg_left hsq hj
  have hb'' := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 3*j by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*s*(s+j*q))).mpr
  have he : (3*Q/(8*s)+3*j/2)*(2*s*(s+j*q)) = 3/4*Q*(s+j*q)+3*j*s*(s+j*q) := by
    field_simp
    ring
  rw [he]
  have hjs := mul_nonneg hj hss
  nlinarith

lemma sum_centered_sq_lower {ι : Type*} [Fintype ι] (y : ι → ℝ) (d : ℝ) :
    (∑ i, (y i)^2)/2-(Fintype.card ι:ℝ)*d^2 ≤ ∑ i, (y i-d)^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (y i)^2/2-d^2 ≤ (y i-d)^2 by nlinarith [sq_nonneg (y i-2*d)])
  simpa only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

lemma multiple_gaussian_integrable {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ι → ℝ => exp (-c*∑ i, (y i)^2)) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_exp_neg_mul_sq hc)
  simpa only [volume_pi, ← exp_sum, ← Finset.mul_sum] using h

lemma multiple_gaussian_integral {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    (∫ y : ι → ℝ, exp (-c*∑ i, (y i)^2)) = exp ((Fintype.card ι:ℝ)*log (sqrt (Real.pi/c))) := by
  have he (y : ι → ℝ) : exp (-c*∑ i, (y i)^2) = ∏ i, exp (-c*(y i)^2) := by
    rw [Finset.mul_sum, exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (-c*x^2)), integral_gaussian]
  rw [exp_nat_mul, exp_log (sqrt_pos.mpr (div_pos Real.pi_pos hc))]

theorem quadratic_envelope_tail {ι : Type*} [Fintype ι] {c C R : ℝ} (hc : 0 < c)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) (f : (ι → ℝ) → ℝ)
    (hf : ∀ y ∈ E, f y ≤ exp ((Fintype.card ι:ℝ)*C-c*∑ i, (y i)^2))
    (htail : ∀ y ∈ E, (Fintype.card ι:ℝ)*R ≤ ∑ i, (y i)^2) :
    (∫⁻ y in E, ENNReal.ofReal (f y)) ≤ ENNReal.ofReal
      (exp ((Fintype.card ι:ℝ)*(C-c*R/2+log (sqrt (Real.pi/(c/2)))))) := by
  let g (y : ι → ℝ) := exp ((Fintype.card ι:ℝ)*(C-c*R/2))*exp (-(c/2)*∑ i, (y i)^2)
  have hg : Integrable g := (multiple_gaussian_integrable (half_pos hc)).const_mul _
  have hgnn (y : ι → ℝ) : 0 ≤ g y := mul_nonneg (exp_pos _).le (exp_pos _).le
  have hdom (y : ι → ℝ) (hy : y ∈ E) : f y ≤ g y := by
    refine (hf y hy).trans ?_
    dsimp [g]
    rw [← exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (htail y hy) hc.le
    nlinarith
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (g y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, g y) := (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hgnn)).symm
    _ = _ := by
      congr 1
      dsimp [g]
      rw [integral_const_mul, multiple_gaussian_integral (half_pos hc), ← exp_add]
      congr 1
      ring

lemma choose_quadratic_tail_radius {c C : ℝ} (hc : 0 < c) (L : ℝ) :
    ∃ R > 0, C-c*R/2+log (sqrt (Real.pi/(c/2))) ≤ -L := by
  let R := max 1 (2*(C+log (sqrt (Real.pi/(c/2)))+L)/c)
  refine ⟨R, (by dsimp [R]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  have h : 2*(C+log (sqrt (Real.pi/(c/2)))+L)/c ≤ R := le_max_right _ _
  rw [div_le_iff₀ hc] at h
  nlinarith

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
