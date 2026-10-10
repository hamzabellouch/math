import Mathlib.Analysis.Normed.Group.InfiniteSum
import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCompactness

namespace OAI

open scoped BigOperators Topology
open Filter

namespace Balanced.ProfileMarginalTV

theorem tsum_abs_marginal_sub_le {α β : Type*} {p q : α × β → ℝ}
    (hp : Summable p) (hq : Summable q) :
    (∑' a, |(∑' b, p (a,b)) - ∑' b, q (a,b)|) ≤
      ∑' ab, |p ab - q ab| := by
  have hs : Summable (fun ab => |p ab - q ab|) := (hp.sub hq).abs
  have hpoint (a : α) : |(∑' b, p (a,b)) - ∑' b, q (a,b)| ≤
      ∑' b, |p (a,b) - q (a,b)| := by
    rw [← (hp.prod_factor a).tsum_sub (hq.prod_factor a)]
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm ((hp.prod_factor a).sub (hq.prod_factor a)).norm
  have hrow : Summable (fun a => |(∑' b, p (a,b)) - ∑' b, q (a,b)|) :=
    hs.prod.of_nonneg_of_le (fun a => abs_nonneg _) hpoint
  exact (hrow.tsum_le_tsum hpoint hs.prod).trans_eq hs.tsum_prod.symm

theorem totalVariation_marginal_le {α β : Type*} {p q : α × β → ℝ}
    (hp : Summable p) (hq : Summable q) :
    (1 / 2 : ℝ) * (∑' a, |(∑' b, p (a,b)) - ∑' b, q (a,b)|) ≤
      (1 / 2 : ℝ) * ∑' ab, |p ab - q ab| :=
  mul_le_mul_of_nonneg_left (tsum_abs_marginal_sub_le hp hq) (by norm_num)

theorem tendsto_marginal_totalVariation {α β ι : Type*} {l : Filter ι}
    {p : ι → α × β → ℝ} {q : α × β → ℝ}
    (hp_nonneg : ∀ n ab, 0 ≤ p n ab) (hq_nonneg : ∀ ab, 0 ≤ q ab)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ ab, Tendsto (fun n => p n ab) l (𝓝 (q ab))) :
    Tendsto (fun n => (1 / 2 : ℝ) *
      ∑' a, |(∑' b, p n (a,b)) - ∑' b, q (a,b)|) l (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (by norm_num) (tsum_nonneg (fun _ => abs_nonneg _)))
    (fun n => totalVariation_marginal_le (hp_sum n).summable hq_sum.summable)
  exact tendsto_totalVariation_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint

theorem abs_tsum_abs_sub_sub_le {α : Type*} {p q r : α → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r) :
    abs ((∑' i, |p i - r i|) - ∑' i, |q i - r i|) ≤ ∑' i, |p i - q i| := by
  have hpr := (hp.sub hr).abs
  have hqr := (hq.sub hr).abs
  rw [← hpr.tsum_sub hqr]
  calc
    |∑' i, (|p i - r i| - |q i - r i|)| ≤
        ∑' i, abs (|p i - r i| - |q i - r i|) := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hpr.sub hqr).norm
    _ ≤ ∑' i, |p i - q i| := by
      apply (hpr.sub hqr).abs.tsum_le_tsum _ (hp.sub hq).abs
      intro i
      simpa only [sub_sub_sub_cancel_right] using
        abs_abs_sub_abs_le_abs_sub (p i - r i) (q i - r i)

theorem tendsto_totalVariation_distance {α ι : Type*} {l : Filter ι}
    {p : ι → α → ℝ} {q r : α → ℝ}
    (hp : ∀ n, Summable (p n)) (hq : Summable q) (hr : Summable r)
    (h : Tendsto (fun n => (1 / 2 : ℝ) * ∑' i, |p n i - q i|) l (𝓝 0)) :
    Tendsto (fun n => (1 / 2 : ℝ) * ∑' i, |p n i - r i|) l
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |q i - r i|)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ h
  intro n
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left (abs_tsum_abs_sub_sub_le (hp n) hq hr) (by norm_num)

theorem deletionPoissonMass_hasSum (k : ℕ) : HasSum (deletionPoissonMass k) 1 := by
  unfold deletionPoissonMass
  simp_rw [ProbabilityTheory.poissonMeasure_real_singleton]
  exact ProbabilityTheory.hasSum_one_poissonMeasure (k : NNReal)

section ActualProfiles

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem lineMultiplicity_eq_deletionMultiplicity (D : Finset (Line F)) (x : Point F) :
    lineMultiplicity D x = deletionMultiplicity D x := rfl

theorem planeProfile_row_hasSum (D C : Finset (Line F)) (i : ℕ) :
    HasSum (fun j => planeProfile D C (i,j)) (empiricalMultiplicityMass D i) := by
  classical
  have h := (FiniteProfile.histogram_hasSum
    (Finset.univ.filter (fun x : Point F => lineMultiplicity D x = i))
    (lineMultiplicity C)).div_const ((Fintype.card F : ℝ) ^ 2)
  apply h.congr_fun
  intro multiplicity
  apply congrArg (fun points : Finset (Point F) =>
    (points.card : ℝ) / (Fintype.card F : ℝ) ^ 2)
  ext point
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem tsum_planeProfile_row (D C : Finset (Line F)) (i : ℕ) :
    (∑' j, planeProfile D C (i,j)) = empiricalMultiplicityMass D i :=
  (planeProfile_row_hasSum D C i).tsum_eq

end ActualProfiles

section VaryingFields

variable {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]

theorem empiricalMultiplicity_tendsto_marginal
    (D C : ∀ n, Finset (Line (F n))) {P : Profile}
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij))) :
    Tendsto (fun n => (1 / 2 : ℝ) *
      ∑' i, |empiricalMultiplicityMass (D n) i - ∑' j, P (i,j)|)
      atTop (𝓝 0) := by
  have h := tendsto_marginal_totalVariation
    (p := fun n => planeProfile (D n) (C n))
    (fun n ij => by unfold planeProfile; positivity) hPnonneg
    (fun n => FiniteProfile.plane_profile_hasSum (D n) (C n)) hPsum hpoint
  simpa only [tsum_planeProfile_row] using h

theorem deletionMultiplicityTV_tendsto_zero
    (D C : ∀ n, Finset (Line (F n))) (k : ℕ) {P : Profile}
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij)))
    (hmarginal : ∀ i, (∑' j, P (i,j)) = deletionPoissonMass k i) :
    Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop (𝓝 0) := by
  simpa only [hmarginal, deletionMultiplicityTV] using
    empiricalMultiplicity_tendsto_marginal D C hPnonneg hPsum hpoint

theorem not_poisson_marginal_of_bad_tv
    (D C : ∀ n, Finset (Line (F n))) (k : ℕ) {P : Profile} {τ : ℝ}
    (hτ : 0 < τ) (hbad : ∀ n, τ ≤ deletionMultiplicityTV k (D n))
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij))) :
    ¬ ∀ i, (∑' j, P (i,j)) = deletionPoissonMass k i := by
  intro hmarginal
  have ht := deletionMultiplicityTV_tendsto_zero D C k hPnonneg hPsum hpoint hmarginal
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hτ).exists
  exact (not_lt_of_ge (hbad n)) hn

theorem deletionMultiplicityTV_tendsto
    (D C : ∀ n, Finset (Line (F n))) (k : ℕ) {P : Profile}
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij))) :
    Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i|)) := by
  exact tendsto_totalVariation_distance
    (fun n => (FiniteProfile.empirical_multiplicity_hasSum (D n)).summable)
    hPsum.summable.prod (deletionPoissonMass_hasSum k).summable
    (empiricalMultiplicity_tendsto_marginal D C hPnonneg hPsum hpoint)

theorem bad_tv_persists
    (D C : ∀ n, Finset (Line (F n))) (k : ℕ) {P : Profile} {τ : ℝ}
    (hbad : ∀ n, τ ≤ deletionMultiplicityTV k (D n))
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij))) :
    τ ≤ (1 / 2 : ℝ) * ∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i| :=
  ge_of_tendsto (deletionMultiplicityTV_tendsto D C k hPnonneg hPsum hpoint)
    (Filter.Eventually.of_forall hbad)

theorem poisson_marginal_of_vanishing_tolerance
    (D C : ∀ n, Finset (Line (F n))) (k : ℕ) {P : Profile} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hsmall : ∀ n, deletionMultiplicityTV k (D n) ≤ ε n)
    (hPnonneg : ∀ ij, 0 ≤ P ij) (hPsum : HasSum P 1)
    (hpoint : ∀ ij, Tendsto (fun n => planeProfile (D n) (C n) ij)
      atTop (𝓝 (P ij))) :
    ∀ i, (∑' j, P (i,j)) = deletionPoissonMass k i := by
  have hz : Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop (𝓝 0) := by
    apply squeeze_zero _ hsmall hε
    intro n
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun i => abs_nonneg _))
  have heq : (1 / 2 : ℝ) * ∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i| = 0 :=
    tendsto_nhds_unique (deletionMultiplicityTV_tendsto D C k hPnonneg hPsum hpoint) hz
  have hsum : (∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i|) = 0 := by linarith
  have hs := (hPsum.summable.prod.sub (deletionPoissonMass_hasSum k).summable).abs
  intro i
  have hi := hs.le_tsum i (fun j _ => abs_nonneg _)
  rw [hsum] at hi
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

end VaryingFields
end Balanced.ProfileMarginalTV

end OAI
