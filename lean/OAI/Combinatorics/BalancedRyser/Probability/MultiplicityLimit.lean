import OAI.Combinatorics.BalancedRyser.Deletion.RobustDeletionAssembly
import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCompactness

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology NNReal

universe u

theorem tsum_abs_sub_distance_le {ι : Type*} {p q r : ι → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r) :
    |(∑' i, |p i - r i|) - (∑' i, |q i - r i|)| ≤ ∑' i, |p i - q i| := by
  have hpr := (hp.sub hr).abs
  have hqr := (hq.sub hr).abs
  have hdiff := (hpr.sub hqr).abs
  calc
    |(∑' i, |p i - r i|) - (∑' i, |q i - r i|)| =
        |∑' i, (|p i - r i| - |q i - r i|)| := by
      rw [hpr.tsum_sub hqr]
    _ ≤ ∑' i, abs (abs (p i - r i) - abs (q i - r i)) := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => |p i - r i| - |q i - r i|)
          (by simpa only [Real.norm_eq_abs] using hdiff))
    _ ≤ ∑' i, |p i - q i| := by
      apply Summable.tsum_le_tsum _ hdiff (hp.sub hq).abs
      intro i
      calc
        abs (abs (p i - r i) - abs (q i - r i)) ≤ |(p i - r i) - (q i - r i)| :=
          abs_abs_sub_abs_le_abs_sub _ _
        _ = |p i - q i| := by congr 1; ring

theorem tendsto_totalVariation_to_fixed
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q r : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hr : Summable r)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => (1 / 2 : ℝ) * ∑' i, |p n i - r i|) l
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |q i - r i|)) := by
  have hraw : Tendsto (fun n => ∑' i, |p n i - r i|) l
      (𝓝 (∑' i, |q i - r i|)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (tendsto_tsum_abs_sub_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
    intro n
    simpa only [Real.norm_eq_abs] using
      tsum_abs_sub_distance_le (hp_sum n).summable hq_sum.summable hr
  exact tendsto_const_nhds.mul hraw

theorem deletionPoissonMass_hasSum (k : ℕ) : HasSum (deletionPoissonMass k) 1 := by
  change HasSum (fun n => (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {n}) 1
  simp only [ProbabilityTheory.poissonMeasure_real_singleton]
  exact ProbabilityTheory.hasSum_one_poissonMeasure (k : ℝ≥0)

theorem empiricalMultiplicityMass_nonneg
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (i : ℕ) : 0 ≤ empiricalMultiplicityMass D i := by
  unfold empiricalMultiplicityMass
  positivity

theorem deletionMultiplicityTV_tendsto
    (k : ℕ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D : ∀ n, Finset (Line (F n)))
    (p : ℕ → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : HasSum p 1)
    (hpoint : ∀ i, Tendsto (fun n => empiricalMultiplicityMass (D n) i) atTop (𝓝 (p i))) :
    Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |p i - deletionPoissonMass k i|)) := by
  exact tendsto_totalVariation_to_fixed
    (fun n i => empiricalMultiplicityMass_nonneg (D n) i) hp_nonneg
    (fun n => FiniteProfile.empirical_multiplicity_hasSum (D n)) hp_sum
    (deletionPoissonMass_hasSum k).summable hpoint

theorem planeProfile_empty_cover_zero
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (i : ℕ) :
    planeProfile D ∅ (i, 0) = empiricalMultiplicityMass D i := by
  simp [planeProfile, lineMultiplicity, empiricalMultiplicityMass, deletionMultiplicity]
  rfl

theorem multiplicityFailureClass_limit_density_zero
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : c = 0 := by
  have hC (n : ℕ) : C n = ∅ := (hclass n).2.1
  have hratio : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 c) := by
    simpa only [hC, Finset.card_empty, Nat.cast_zero, zero_div] using hlim.1
  exact tendsto_nhds_unique hratio tendsto_const_nhds

theorem multiplicityFailureClass_limit_coordinates
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) (i : ℕ) :
    Tendsto (fun n => empiricalMultiplicityMass (D n) i) atTop (𝓝 (P (i, 0))) := by
  have hC (n : ℕ) : C n = ∅ := (hclass n).2.1
  have hcoord := (tendsto_pi_nhds.1 hlim.2.1) (i, 0)
  simpa only [hC, planeProfile_empty_cover_zero] using hcoord

theorem empiricalMultiplicityMass_firstMoment_hasSum
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) :
    HasSum (fun i : ℕ => (i : ℝ) * empiricalMultiplicityMass D i)
      ((D.card : ℝ) / (Fintype.card F : ℝ)) := by
  have h := (FiniteProfile.weighted_histogram_hasSum
    (Finset.univ : Finset (Point F)) (deletionMultiplicity D) (fun i : ℕ => (i : ℝ))).div_const
      ((Fintype.card F : ℝ) ^ 2)
  have hs : (∑ p : Point F, (deletionMultiplicity D p : ℝ)) =
      (D.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast FiniteProfile.sum_multiplicity D
  rw [hs] at h
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  convert! h using 1
  · funext i
    unfold empiricalMultiplicityMass
    ring
  · field_simp

theorem empiricalMultiplicityMass_mean_le
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    (∑' i : ℕ, (i : ℝ) * empiricalMultiplicityMass D i) ≤ 2 * (k : ℝ) := by
  rw [(empiricalMultiplicityMass_firstMoment_hasSum D).tsum_eq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : (0 : ℝ) < Fintype.card F := by linarith
  have hcard : (D.card : ℝ) = (k : ℝ) * (Fintype.card F + 1) := by
    exact_mod_cast FiniteProfile.deletionSet_card hD
  rw [hcard, div_le_iff₀ hqpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem multiplicityFailureClass_limit_probability
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ i : ℕ, 0 ≤ P (i, 0)) ∧ HasSum (fun i : ℕ => P (i, 0)) 1 := by
  have hpoint := multiplicityFailureClass_limit_coordinates k τ D C hclass hlim
  have hnonneg (n i : ℕ) : 0 ≤ empiricalMultiplicityMass (D n) i :=
    empiricalMultiplicityMass_nonneg (D n) i
  have hnorm (n : ℕ) : HasSum (empiricalMultiplicityMass (D n)) 1 :=
    FiniteProfile.empirical_multiplicity_hasSum (D n)
  have hmoment (n : ℕ) : Summable (fun i : ℕ => (i : ℝ) * empiricalMultiplicityMass (D n) i) :=
    (empiricalMultiplicityMass_firstMoment_hasSum (D n)).summable
  have hbound (n : ℕ) :
      (∑' i : ℕ, (i : ℝ) * empiricalMultiplicityMass (D n) i) ≤ 2 * (k : ℝ) :=
    empiricalMultiplicityMass_mean_le (hclass n).1
  have htight := profile_tight_of_moment (fun i : ℕ => i)
    (fun B => Set.finite_Iic B) hnonneg hnorm hmoment hbound
  exact ⟨fun i => ge_of_tendsto (hpoint i) (Eventually.of_forall fun n => hnonneg n i),
    hasSum_one_of_tendsto_of_tight hnonneg hnorm hpoint htight⟩

theorem multiplicityFailureClass_limit_tv
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    τ ≤ (1 / 2 : ℝ) * ∑' i : ℕ, |P (i, 0) - deletionPoissonMass k i| := by
  obtain ⟨hp0, hpsum⟩ := multiplicityFailureClass_limit_probability k τ D C hclass hlim
  have hp := multiplicityFailureClass_limit_coordinates k τ D C hclass hlim
  exact ge_of_tendsto (deletionMultiplicityTV_tendsto k D (fun i => P (i, 0)) hp0 hpsum hp)
    (Eventually.of_forall fun n => (hclass n).2.2)

end Balanced

end OAI
