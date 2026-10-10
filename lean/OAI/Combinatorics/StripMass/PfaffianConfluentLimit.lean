import Mathlib
import OAI.Combinatorics.StripMass.SpectralComponents

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open Polynomial Set MeasureTheory Filter Matrix StripComplexification
open scoped Topology BigOperators
theorem pfaffian_confluent_limit (N : ℕ) (hN : 1 ≤ N) :
    ∃ g₀ : Polynomial ℝ, CriticalStrip.MonicProblem N g₀ ∧
      (∀ p, CriticalStrip.MonicProblem N p → p = g₀) ∧
      ∃ g : (Fin N → ℂ) → Polynomial ℂ,
        g (fun _ => flatC) = g₀.map Complex.ofRealHom ∧
        (∀ k : ℕ, ContinuousAt (fun a => (g a).coeff k) (fun _ => flatC)) ∧
        ∀ᶠ a in 𝓝 (fun _ : Fin N => flatC),
          (g a).Monic ∧ (g a).natDegree = N ∧
          ∀ (_ : Function.Injective a)
            (_ : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
            (_ : p N a ≠ 0) (z : ℂ),
            (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
              (g a).eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  obtain ⟨g₀, hg₀, huniq⟩ := CriticalStrip.homogeneous_monic_unique N hN
  refine ⟨g₀,hg₀,huniq,confluentPolynomial hN, ?_,
    confluentPolynomial_continuousAt hN, ?_⟩
  · exact (perturbed_unique hN _ (systemMatrix_homogeneous_unit hN) _
      (real_monic_problem_map hg₀)).symm
  · have hd := (systemMatrix_continuous hN).matrix_det.continuousAt.eventually_ne
      (isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN))
    filter_upwards [hd] with a ha
    have hu := isUnit_iff_ne_zero.2 ha
    have hg := confluentPolynomial_spec hN a hu
    refine ⟨hg.1,hg.2.1, ?_⟩
    intro hinj hD hp z hz
    obtain ⟨g,hgm,hgn,hproj,hge⟩ := generic_pfaffian_projection N a hinj hD hp
    have he := perturbed_unique hN a hu g ⟨hgm,hgn,hproj⟩
    rw [← he]
    exact hge z hz

end
end StripPfaffian

 
namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory

 
theorem rho_pos : 0 < rho := by
  unfold rho
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem c_pos : 0 < c := by
  unfold c
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem archWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ archWeight N k p := by
  classical
  unfold archWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem bridgeWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ bridgeWeight N k p := by
  classical
  unfold bridgeWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem K_nonneg (N : ℕ) (k : ℤ) : 0 ≤ K N k :=
  tsum_nonneg (archWeight_nonneg N k)

theorem bridgeKernel_nonneg (N : ℕ) (k : ℤ) : 0 ≤ bridgeKernel N k :=
  tsum_nonneg (bridgeWeight_nonneg N k)

theorem archMass_nonneg (N : ℕ) : 0 ≤ archMass N :=
  tsum_nonneg (K_nonneg N)

theorem bridgeMass_nonneg (N : ℕ) : 0 ≤ bridgeMass N :=
  tsum_nonneg (bridgeKernel_nonneg N)

theorem moment_nonneg (N : ℕ) : 0 ≤ moment N :=
  tsum_nonneg fun k => mul_nonneg (by positivity) (K_nonneg N (k + 1))

@[simp] theorem K_zero (N : ℕ) : K N 0 = 0 := by
  simp [K, archWeight]

 
theorem IsPath.mono {N M : ℕ} {finish : Triangle} {p : List Triangle}
    (hp : IsPath N finish p) (hNM : N ≤ M) : IsPath M finish p := by
  obtain ⟨hfirst, hlast, hsimple, hchain, hbands⟩ := hp
  exact ⟨hfirst, hlast, hsimple, hchain,
    fun v hv => (hbands v hv).trans_le hNM⟩

theorem archWeight_mono {N M : ℕ} (hNM : N ≤ M) (k : ℤ) (p : List Triangle) :
    archWeight N k p ≤ archWeight M k p := by
  classical
  by_cases hp : k ≠ 0 ∧ IsPath N (up k 0) p
  · have hp' : k ≠ 0 ∧ IsPath M (up k 0) p := ⟨hp.1, hp.2.mono hNM⟩
    simp only [archWeight, ite_eq_left hp, ite_eq_left hp', le_refl]
  · rw [archWeight, ite_eq_right hp]
    exact archWeight_nonneg M k p

 

theorem K_le_of_summable {N M : ℕ} (hNM : N ≤ M) (k : ℤ)
    (hM : Summable (archWeight M k)) : K N k ≤ K M k := by
  have hN : Summable (archWeight N k) :=
    Summable.of_nonneg_of_le (archWeight_nonneg N k) (archWeight_mono hNM k) hM
  exact Summable.tsum_le_tsum (archWeight_mono hNM k) hN hM

theorem archMass_le_of_finite {N M : ℕ} (hNM : N ≤ M) (hM : StripSumsFinite M) :
    archMass N ≤ archMass M := by
  have hk : ∀ k, K N k ≤ K M k := fun k => K_le_of_summable hNM k (hM.1 k)
  have hN : Summable (K N) :=
    Summable.of_nonneg_of_le (K_nonneg N) hk hM.2.2.1
  exact Summable.tsum_le_tsum hk hN hM.2.2.1

theorem moment_le_of_finite {N M : ℕ} (hNM : N ≤ M) (hM : StripSumsFinite M) :
    moment N ≤ moment M := by
  have hk : ∀ k : ℕ, (k + 1 : ℝ) * K N (k + 1) ≤ (k + 1 : ℝ) * K M (k + 1) :=
    fun k => mul_le_mul_of_nonneg_left (K_le_of_summable hNM (k + 1) (hM.1 _))
      (by positivity)
  have hN : Summable (fun k : ℕ => (k + 1 : ℝ) * K N (k + 1)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by positivity) (K_nonneg N (k + 1))) hk hM.2.2.2.2
  exact Summable.tsum_le_tsum hk hN hM.2.2.2.2

 

theorem bridgeMass_le_of_finite_and_flux {N M : ℕ} (hNM : N ≤ M)
    (hM : StripSumsFinite M)
    (hfluxN : c * archMass N + bridgeMass N = 1)
    (hfluxM : c * archMass M + bridgeMass M = 1) :
    bridgeMass M ≤ bridgeMass N := by
  have hA := mul_le_mul_of_nonneg_left (archMass_le_of_finite hNM hM) c_pos.le
  linarith

 
theorem sum_increment_bounds {M B : ℕ → ℝ} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hB : AntitoneOn B (Set.Ici 1))
    (hinc : ∀ n : ℕ, 1 ≤ n → lo * B n ≤ M (n + 1) - M n ∧
      M (n + 1) - M n ≤ hi * B n)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a : ℕ) * lo * B b ≤ M b - M a ∧
      M b - M a ≤ (b - a : ℕ) * hi * B a := by
  have h₁ : ∑ j ∈ Finset.Ico a b, lo * B b ≤
      ∑ j ∈ Finset.Ico a b, (M (j + 1) - M j) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Ico.mp hj
    exact (mul_le_mul_of_nonneg_left (hB (ha.trans haj) (ha.trans hab) hjb.le) hlo).trans
      (hinc j (ha.trans haj)).1
  have h₂ : ∑ j ∈ Finset.Ico a b, (M (j + 1) - M j) ≤
      ∑ j ∈ Finset.Ico a b, hi * B a := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨haj, _⟩ := Finset.mem_Ico.mp hj
    exact (hinc j (ha.trans haj)).2.trans
      (mul_le_mul_of_nonneg_left (hB ha (ha.trans haj) haj) hhi)
  constructor
  · simpa only [Finset.sum_Ico_sub _ hab, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_assoc] using h₁
  · simpa only [Finset.sum_Ico_sub _ hab, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_assoc] using h₂

 

theorem comparable_of_antitone_increments {M B : ℕ → ℝ} {α : ℝ}
    (hα : 0 < α)
    (hBnon : ∀ n : ℕ, 1 ≤ n → 0 ≤ B n)
    (hBsucc : ∀ n : ℕ, 1 ≤ n → B (n + 1) ≤ B n)
    (hdiff : Comparable (fun n => M (n + 1) - M n) B)
    (hM : Comparable M (fun n => (n : ℝ) ^ α)) :
    Comparable B (fun n => (n : ℝ) ^ (α - 1)) := by
  obtain ⟨loD, hiD, hloD, hhiD, hD⟩ := hdiff
  obtain ⟨loM, hiM, hloM, hhiM, hM⟩ := hM
  have hB : AntitoneOn B (Set.Ici 1) := antitoneOn_nat_Ici_of_succ_le hBsucc
  have hM1 : 0 ≤ M 1 := by
    have h := (hM 1 le_rfl).1
    norm_num at h
    exact hloM.le.trans h
  have hupper : ∀ n : ℕ, 2 ≤ n →
      B n ≤ (2 * hiM / loD) * (n : ℝ) ^ (α - 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := by linarith
    have hinterval := (sum_increment_bounds hloD.le hhiD.le hB hD
      (a := 1) (b := n) le_rfl hn1).1
    rw [Nat.cast_sub hn1, Nat.cast_one] at hinterval
    have hbound : ((n : ℝ) - 1) * loD * B n ≤ hiM * (n : ℝ) ^ α :=
      (hinterval.trans (sub_le_self _ hM1)).trans (hM n hn1).2
    have hnon : 0 ≤ ((n : ℝ) - 2) * (loD * B n) :=
      mul_nonneg (by linarith) (mul_nonneg hloD.le (hBnon n hn1))
    have hmul : (n : ℝ) * loD * B n ≤ 2 * hiM * (n : ℝ) ^ α := by
      nlinarith only [hbound, hnon]
    calc
      B n ≤ (2 * hiM * (n : ℝ) ^ α) / ((n : ℝ) * loD) :=
        (le_div_iff₀ (mul_pos hnpos hloD)).2 (by nlinarith only [hmul])
      _ = (2 * hiM / loD) * (n : ℝ) ^ (α - 1) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
        field_simp
  obtain ⟨L, hLbig⟩ := exists_nat_gt (max (2 : ℝ) ((2 * hiM / loM) ^ α⁻¹))
  have hLr : (2 : ℝ) ≤ L := (le_max_left _ _).trans hLbig.le
  have hL : 2 ≤ L := by exact_mod_cast hLr
  have hscale : 2 * hiM ≤ loM * (L : ℝ) ^ α := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
      ((le_max_right _ _).trans hLbig.le) hα.le
    rw [Real.rpow_inv_rpow (by positivity) hα.ne'] at hpow
    simpa only [mul_comm] using (div_le_iff₀ hloM).mp hpow
  have hdenom : 0 < ((L : ℝ) - 1) * hiD :=
    mul_pos (by linarith) hhiD
  refine ⟨hiM / (((L : ℝ) - 1) * hiD), max (B 1) (2 * hiM / loD),
    div_pos hhiM hdenom, lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnpow : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hnpos.le _
  constructor
  · have hnLN : n ≤ L * n := by
      calc
        n = 1 * n := (one_mul n).symm
        _ ≤ L * n := Nat.mul_le_mul_right n (by omega)
    have hgrowth : hiM * (n : ℝ) ^ α ≤ M (L * n) - M n := by
      have hlarge := (hM (L * n) (hn.trans hnLN)).1
      dsimp only at hlarge
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) hnpos.le] at hlarge
      have hsmall := (hM n hn).2
      have hscale' := mul_le_mul_of_nonneg_right hscale hnpow
      nlinarith only [hlarge, hsmall, hscale']
    have hinterval := (sum_increment_bounds hloD.le hhiD.le hB hD hn hnLN).2
    rw [Nat.cast_sub hnLN, Nat.cast_mul] at hinterval
    have hbound : hiM * (n : ℝ) ^ α ≤
        B n * (((L : ℝ) - 1) * hiD * (n : ℝ)) := by
      nlinarith only [hgrowth, hinterval]
    calc
      (hiM / (((L : ℝ) - 1) * hiD)) * (n : ℝ) ^ (α - 1) =
          (hiM * (n : ℝ) ^ α) / (((L : ℝ) - 1) * hiD * (n : ℝ)) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
        field_simp
      _ ≤ B n := (div_le_iff₀ (mul_pos hdenom hnpos)).2 hbound
  · rcases eq_or_lt_of_le hn with hn' | hn'
    · subst n
      simp
    · exact (hupper n (by omega)).trans (mul_le_mul_of_nonneg_right
        (le_max_right _ _) (Real.rpow_nonneg hnpos.le _))

 

theorem criticalStripMass_iff_four_estimates : CriticalStripMass ↔
    (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
    (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
    Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
    Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨hfinite, hflux, hinc, hmoment⟩
    have hmono : ∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N := by
      intro N hN
      exact bridgeMass_le_of_finite_and_flux (Nat.le_succ N)
        (hfinite (N + 1) (by omega)) (hflux N hN) (hflux (N + 1) (by omega))
    have hbridge := comparable_of_antitone_increments (by norm_num : (0 : ℝ) < 3 / 4)
      (fun N _ => bridgeMass_nonneg N) hmono hinc hmoment
    refine ⟨hfinite, hflux, hinc, hmoment, ?_, hmono⟩
    simpa only [show (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) by norm_num] using hbridge



 
theorem reflection_deficit_bounds {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - reflectionProduct N x y ∧
    1 - reflectionProduct N x y ≤ 2 * min 1 (x * ∑ i, (y i)⁻¹) := by
  have hR := abs_reflectionProduct_le_one hy hx.le
  refine ⟨by linarith [(abs_le.mp hR).2], ?_⟩
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · linarith [(abs_le.mp hR).1]
  · calc
      1 - reflectionProduct N x y ≤ |1 - reflectionProduct N x y| := le_abs_self _
      _ ≤ ∑ i : Fin N, |1 - (y i - x) / (y i + x)| :=
        abs_one_sub_prod_le _ _ fun i _ => abs_reflectionFactor_le_one hx.le (hy.2 i).1
      _ ≤ ∑ i : Fin N, 2 * x * (y i)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        have hyi := (hy.2 i).1
        have hdenom : 0 < y i + x := add_pos hyi hx
        rw [show 1 - (y i - x) / (y i + x) = 2 * x / (y i + x) by field_simp; ring,
          abs_of_pos (div_pos (by positivity) hdenom)]
        change 2 * x / (y i + x) ≤ 2 * x / y i
        exact div_le_div_of_nonneg_left (by positivity) hyi (le_add_of_nonneg_right hx.le)
      _ = 2 * (x * ∑ i : Fin N, (y i)⁻¹) := by rw [← Finset.mul_sum]; ring

 
theorem reflection_deficit_lower {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N)
    (i : Fin N) (hsmall : ∀ j, y i ≤ y j) {x : ℝ}
    (hx : x ∈ Ioo (y i / 3) (y i / 2)) :
    (1 / 2 : ℝ) ≤ 1 - reflectionProduct N x y := by
  classical
  have hyi := (hy.2 i).1
  have hxpos : 0 < x := (by positivity : 0 < y i / 3).trans hx.1
  have hnon : ∀ j : Fin N, 0 ≤ (y j - x) / (y j + x) := by
    intro j
    exact div_nonneg (by linarith [hsmall j, hx.2]) (add_pos (hy.2 j).1 hxpos).le
  have hproduct : reflectionProduct N x y ≤ (y i - x) / (y i + x) := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := {i}) (t := Finset.univ) (f := fun j : Fin N => (y j - x) / (y j + x))
      (Finset.subset_univ _) (fun j _ => hnon j)
      (fun j _ _ => (le_abs_self _).trans (abs_reflectionFactor_le_one hxpos.le (hy.2 j).1))
    simpa only [reflectionProduct, Finset.prod_singleton] using h
  have hhalf : (y i - x) / (y i + x) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (add_pos hyi hxpos)).2
    linarith [hx.1]
  linarith

 
theorem rpow_le_eight_omega {x : ℝ} (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) :
    (1 / 8 : ℝ) * x ^ (-(1 / 4 : ℝ)) ≤ omega x := by
  have hx0 := hx.1
  have hq : (3 / 2 : ℝ) ≤ (1 + x) / (2 * x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * x)).2
    nlinarith [hx.2]
  have hqnon : 0 ≤ (1 + x) / (2 * x) := by positivity
  have hsq := Real.sq_sqrt hqnon
  have hsnon := Real.sqrt_nonneg ((1 + x) / (2 * x))
  have hs : (6 / 5 : ℝ) ≤ Real.sqrt ((1 + x) / (2 * x)) := by
    nlinarith
  have hsn : 0 ≤ Real.sqrt ((1 + x) / (2 * x)) - 1 := by linarith
  have hosq : (omega x) ^ 2 = (Real.sqrt ((1 + x) / (2 * x)) - 1) / 4 := by
    unfold omega
    nlinarith [Real.sq_sqrt hsn]
  have hsub : Real.sqrt ((1 + x) / (2 * x)) / 6 ≤
      Real.sqrt ((1 + x) / (2 * x)) - 1 := by linarith
  have hpow : ((1 / 8 : ℝ) * x ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) ≤ (omega x) ^ 4 := by
    have hcomp : Real.sqrt ((1 + x) / (2 * x)) / 24 ≤ (omega x) ^ 2 := by linarith
    have hcomp' := mul_self_le_mul_self (by positivity) hcomp
    have hquart : (1 + x) / (2 * x) / 576 ≤ (omega x) ^ 4 := by nlinarith only [hcomp', hsq]
    have hxinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.1.le
    have hqinv : x⁻¹ / 2 ≤ (1 + x) / (2 * x) := by
      calc
        x⁻¹ / 2 = 1 / (2 * x) := by ring
        _ ≤ (1 + x) / (2 * x) := div_le_div_of_nonneg_right (by linarith [hx.1]) (by positivity)
    have he : (x ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
      norm_num [Real.rpow_neg_one]
    rw [mul_pow, he]
    nlinarith only [hquart, hqinv, hxinv]
  exact (pow_le_pow_iff_left₀ (by positivity) (omega_nonneg x) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

 

def pointwiseArchIntegrand (N : ℕ) (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  (1 - reflectionProduct N x y) * omega x / x

def pointwiseArchIntegral (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  ∫ x in Ioo 0 1, pointwiseArchIntegrand N y x

theorem measurable_pointwiseArchIntegrand (N : ℕ) (y : Fin N → ℝ) :
    Measurable (pointwiseArchIntegrand N y) := by
  have hR : Measurable (fun x : ℝ => reflectionProduct N x y) := (measurable_reflectionProduct N).comp (measurable_id.prodMk measurable_const)
  exact ((measurable_const.sub hR).mul measurable_omega).div measurable_id

theorem pointwiseArchIntegrand_bounds {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ pointwiseArchIntegrand N y x ∧
      pointwiseArchIntegrand N y x ≤ inverseHalfSum N y * x ^ (-(3 / 4 : ℝ)) := by
  have hdef := (reflection_deficit_bounds hy hx.1).1
  have hb := (le_abs_self (1 - reflectionProduct N x y)).trans
    (reflectionProduct_endpoint_bound hy hx.1)
  have hS : 0 ≤ inverseHalfSum N y :=
    Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hy.2 i).1 _).le
  constructor
  · exact div_nonneg (mul_nonneg hdef (omega_nonneg x)) hx.1.le
  · have hpow : Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x = x ^ (-(3 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx.1]
      calc
        x ^ (1 / 2 + -(1 / 4) : ℝ) / x = x ^ (1 / 4 : ℝ) / x ^ (1 : ℝ) := by norm_num
        _ = x ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hx.1 _ _).symm
        _ = _ := by norm_num
    calc
      pointwiseArchIntegrand N y x ≤ (Real.sqrt x * inverseHalfSum N y) * omega x / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (omega_nonneg x)) hx.1.le
      _ ≤ (Real.sqrt x * inverseHalfSum N y) * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (omega_le_rpow hx)
          (mul_nonneg (Real.sqrt_nonneg x) hS)) hx.1.le
      _ = inverseHalfSum N y * (Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x) := by ring
      _ = _ := by rw [hpow]

theorem integrableOn_pointwiseArchIntegrand {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    IntegrableOn (pointwiseArchIntegrand N y) (Ioo 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  apply (hp.const_mul (inverseHalfSum N y)).mono'
    (measurable_pointwiseArchIntegrand N y).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pointwiseArchIntegrand_bounds hy hx).1]
  exact (pointwiseArchIntegrand_bounds hy hx).2

 
end
end CriticalStrip

end OAI
