import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FermiDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

def translatedDensity (η : Space → ℝ) (a : Space) (x : Space) : ℝ := η (x-a)

def smearPair (η : Space → ℝ) (a b : Space) : ℝ :=
  ∫ r : Space × Space, translatedDensity η a r.1*translatedDensity η b r.2/‖r.1-r.2‖

lemma translatedDensity_support {η : Space → ℝ} {R : ℝ}
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (a : Space) :
    Function.support (translatedDensity η a) ⊆ closedBall a R := by
  intro x hx
  simpa only [mem_closedBall,dist_eq_norm] using hs (x-a) hx

lemma translatedDensity_measurable {η : Space → ℝ} (hm : Measurable η) (a : Space) :
    Measurable (translatedDensity η a) := hm.comp (measurable_id.sub_const a)

lemma translatedDensity_mass (η : Space → ℝ) (a : Space) :
    (∫ x : Space, translatedDensity η a x) = ∫ x : Space, η x := integral_sub_right_eq_self η a

lemma smearPair_integrable {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) (a b : Space) :
    Integrable (fun r : Space × Space => translatedDensity η a r.1*translatedDensity η b r.2/‖r.1-r.2‖) :=
  bounded_compact_coulomb_integrable (translatedDensity_measurable hm a) (translatedDensity_measurable hm b)
    (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    (translatedDensity_support hs a) (translatedDensity_support hs b)
    (fun x => hb (x-a)) (fun x => hb (x-b))

lemma potential_translatedDensity (η : Space → ℝ) (a x : Space) :
    CoulombAnalysis.tfPotential (translatedDensity η a) x = CoulombAnalysis.tfPotential η (x-a) :=
  integral_translated_pole η x a

lemma smearPair_le_point {η : Space → ℝ} (hm : Measurable η) (hn : ∀ x, 0 ≤ η x)
    {R B : ℝ} (hR : 0 ≤ R) (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, η x ≤ B)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    {a b : Space} (hab : a ≠ b) : smearPair η a b ≤ 1/‖a-b‖ := by
  have haB : ∀ x, |η x| ≤ B := fun x => by rw [abs_of_nonneg (hn x)]; exact hb x
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport haB
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport haB (5/3 : ENNReal)
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs haB a b)]
  calc
    _ ≤ ∫ x : Space, translatedDensity η a x/‖b-x‖ := by
      apply integral_mono_ae (coulomb_potential_pair_integrable (smearPair_integrable hm hs haB a b))
        (translated_pole_integrable hi hp b a)
      filter_upwards [ae_ne_point b] with x hx
      rw [potential_translatedDensity]
      have hh := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hx)
      rw [h1] at hh
      simpa only [translatedDensity,mul_one_div,norm_sub_rev b x] using mul_le_mul_of_nonneg_left hh (hn (x-a))
    _ = CoulombAnalysis.tfPotential η (b-a) := integral_translated_pole η b a
    _ ≤ 1/‖a-b‖ := by
      have hh := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hab.symm)
      simpa only [h1,norm_sub_rev b a] using hh

lemma smearPair_self {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) (a : Space) :
    smearPair η a a = smearPair η 0 0 := by
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs hb a a)]
  simp only [potential_translatedDensity,translatedDensity]
  rw [integral_sub_right_eq_self (fun x : Space => η x*CoulombAnalysis.tfPotential η x) a]
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs hb 0 0)]
  simp only [potential_translatedDensity,translatedDensity,sub_zero]

def finiteSmear {n : ℕ} (η : Space → ℝ) (y : Fin n → Space) (x : Space) : ℝ :=
  ∑ i : Fin n, translatedDensity η (y i) x

lemma finiteSmear_direct {n : ℕ} (η : Space → ℝ) (y : Fin n → Space)
    (hm : Measurable η) {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) :
    (∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) =
      ∑ i : Fin n, ∑ j : Fin n, smearPair η (y i) (y j) := by
  simp only [finiteSmear]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_div]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => smearPair_integrable hm hs hb (y i) (y j))
  · intro i _
    exact integrable_finsetSum _ (fun j _ => smearPair_integrable hm hs hb (y i) (y j))

theorem retained_coulomb_lower_self {n : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R B : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, η x ≤ B)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Fin n → Space) (hy : Function.Injective y) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      (n:ℝ)*(1/2:ℝ)*smearPair η 0 0 ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖y i-y j‖ else 0 := by
  have haB : ∀ x, |η x| ≤ B := fun x => by rw [abs_of_nonneg (hn x)]; exact hb x
  rw [finiteSmear_direct η y hm hs haB]
  have he (i j : Fin n) : smearPair η (y i) (y j) ≤
      (if i=j then smearPair η 0 0 else 0) + (if i ≠ j then 1/‖y i-y j‖ else 0) := by
    by_cases hij : i=j
    · subst j
      simp only [ne_eq,not_true_eq_false,ite_false,add_zero]
      exact (smearPair_self hm hs haB (y i)).le
    · simp only [ite_eq_right hij,ite_eq_left hij,zero_add]
      exact smearPair_le_point hm hn hR hs hb hr h1 (fun hh => hij (hy hh))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => he i j))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  rw [sum_ordered_pairs (fun i j : Fin n => 1/‖y i-y j‖) (fun i j => by rw [norm_sub_rev])] at hh
  linarith

end CoulombAtom

end

end OAI
