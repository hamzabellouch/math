import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCompactness
import OAI.Combinatorics.BalancedRyser.Selection.ProfileOccupancy2

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Balanced.ProfileMarginalLimits

theorem abs_tsum_comp_sub_le {ι κ : Type*} {p q : ι → ℝ}
    (hp : Summable p) (hq : Summable q) (f : κ → ι)
    (hf : Function.Injective f) :
    |(∑' j, p (f j)) - ∑' j, q (f j)| ≤ ∑' i, |p i - q i| := by
  have hs : Summable (fun i => |p i - q i|) := (hp.sub hq).abs
  have heq := (hp.comp_injective hf).tsum_sub (hq.comp_injective hf)
  simp only [Function.comp_def] at heq
  rw [← heq]
  calc
    |∑' j, (p (f j) - q (f j))| ≤ ∑' j, |p (f j) - q (f j)| := by
      have hnorm : Summable (fun j => ‖p (f j) - q (f j)‖) := by
        simpa only [Real.norm_eq_abs, Function.comp_def] using (hs.comp_injective hf)
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, |p i - q i| :=
      tsum_comp_le_tsum_of_inj hs (fun i => abs_nonneg _) hf

theorem tendsto_tsum_comp_of_probability_mass
    {ι κ α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (f : κ → ι) (hf : Function.Injective f) :
    Tendsto (fun n => ∑' j, p n (f j)) l (𝓝 (∑' j, q (f j))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_tsum_abs_sub_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
  simpa only [Real.norm_eq_abs] using
    abs_tsum_comp_sub_le (hp_sum n).summable hq_sum.summable f hf

private theorem finite_totalDegree_sublevel (B : ℕ) :
    Set.Finite {ij : ℕ × ℕ | ij.1 + ij.2 ≤ B} := by
  apply ((Set.finite_Iic B).prod (Set.finite_Iic B)).subset
  intro ij hij
  change ij.1 + ij.2 ≤ B at hij
  change ij.1 ≤ B ∧ ij.2 ≤ B
  omega

variable {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]
  {D C : ∀ n, Finset (Line (F n))} {k : ℕ} {P : Profile}

theorem planeProfile_limit_hasSum
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P)) :
    HasSum P 1 := by
  have hp (n : ℕ) (ij : ℕ × ℕ) : 0 ≤ planeProfile (D n) (C n) ij := by
    unfold planeProfile
    positivity
  have hs (n : ℕ) : HasSum (planeProfile (D n) (C n)) 1 :=
    FiniteProfile.plane_profile_hasSum (D n) (C n)
  have hws (n : ℕ) : Summable (fun ij : ℕ × ℕ =>
      ((ij.1 + ij.2 : ℕ) : ℝ) * planeProfile (D n) (C n) ij) :=
    (FiniteProfile.plane_profile_firstMoment_hasSum (D n) (C n)).summable
  have hM (n : ℕ) : (∑' ij : ℕ × ℕ,
      ((ij.1 + ij.2 : ℕ) : ℝ) * planeProfile (D n) (C n) ij) ≤ 2 * k + 4 := by
    have hm : HasSum (fun ij : ℕ × ℕ =>
        ((ij.1 + ij.2 : ℕ) : ℝ) * planeProfile (D n) (C n) ij)
        ((((D n).card + (C n).card : ℕ) : ℝ) / (Fintype.card (F n) : ℝ)) :=
      FiniteProfile.plane_profile_firstMoment_hasSum (D n) (C n)
    rw [hm.tsum_eq]
    exact FiniteProfile.plane_firstMoment_le_source_bound (hpair n).1 (hpair n).2.2
  exact hasSum_one_of_tendsto_of_tight hp hs (fun ij => hP.apply_nhds ij)
    (profile_tight_of_moment (fun ij : ℕ × ℕ => ij.1 + ij.2)
      finite_totalDegree_sublevel hp hs hws hM)

theorem planeProfile_tendsto_l1
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P)) :
    Tendsto (fun n => ∑' ij, |planeProfile (D n) (C n) ij - P ij|)
      atTop (𝓝 0) := by
  have hp (n : ℕ) (ij : ℕ × ℕ) : 0 ≤ planeProfile (D n) (C n) ij := by
    unfold planeProfile
    positivity
  exact tendsto_tsum_abs_sub_of_probability_mass hp
    (fun ij => ge_of_tendsto (hP.apply_nhds ij) (Eventually.of_forall fun n => hp n ij))
    (fun n => FiniteProfile.plane_profile_hasSum (D n) (C n))
    (planeProfile_limit_hasSum hpair hP) (fun ij => hP.apply_nhds ij)

theorem planeProfile_tendsto_marginal {ι : Type*}
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P))
    (f : ι → ℕ × ℕ) (hf : Function.Injective f) :
    Tendsto (fun n => ∑' i, planeProfile (D n) (C n) (f i))
      atTop (𝓝 (∑' i, P (f i))) := by
  have hp (n : ℕ) (ij : ℕ × ℕ) : 0 ≤ planeProfile (D n) (C n) ij := by
    unfold planeProfile
    positivity
  exact tendsto_tsum_comp_of_probability_mass hp
    (fun ij => ge_of_tendsto (hP.apply_nhds ij) (Eventually.of_forall fun n => hp n ij))
    (fun n => FiniteProfile.plane_profile_hasSum (D n) (C n))
    (planeProfile_limit_hasSum hpair hP) (fun ij => hP.apply_nhds ij) f hf

theorem planeProfile_core_density_tendsto
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P)) :
    Tendsto (fun n => ((uncoveredBy (D n)).card : ℝ) /
      (Fintype.card (F n) : ℝ) ^ 2) atTop (𝓝 (∑' j, P (0, j))) := by
  have ht := planeProfile_tendsto_marginal hpair hP
    (fun j : ℕ => (0, j)) (fun _ _ h => (Prod.mk.inj h).2)
  simpa only [(FiniteProfile.planeProfile_zero_row_hasSum (D _) (C _)).tsum_eq] using ht

theorem planeProfile_uncovered_density_tendsto
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P)) :
    Tendsto (fun n => ((uncoveredBy (C n)).card : ℝ) /
      (Fintype.card (F n) : ℝ) ^ 2) atTop (𝓝 (∑' i, P (i, 0))) := by
  have ht := planeProfile_tendsto_marginal hpair hP
    (fun i : ℕ => (i, 0)) (fun _ _ h => (Prod.mk.inj h).1)
  simpa only [(FiniteProfile.planeProfile_zero_column_hasSum (D _) (C _)).tsum_eq] using ht

theorem planeProfile_uncovered_lower_bound
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P))
    {δ : ℝ} (hδ : ∀ n, δ * (Fintype.card (F n) : ℝ) ^ 2 ≤
      ((uncoveredBy (C n)).card : ℝ)) :
    δ ≤ ∑' i, P (i, 0) := by
  apply ge_of_tendsto (planeProfile_uncovered_density_tendsto hpair hP)
  apply Eventually.of_forall
  intro n
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (Fintype.card (F n) : ℝ) ^ 2)).mpr
  exact hδ n

theorem planeProfile_zero_row_hasSum_of_density
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P))
    {μ : ℝ} (hdensity : Tendsto (fun n => ((uncoveredBy (D n)).card : ℝ) /
      (Fintype.card (F n) : ℝ) ^ 2) atTop (𝓝 μ)) :
    HasSum (fun j : ℕ => P (0, j)) μ := by
  have hs := (planeProfile_limit_hasSum hpair hP).summable.comp_injective
    (fun _ _ h => (Prod.mk.inj h).2 : Function.Injective (fun j : ℕ => (0, j)))
  have heq := tendsto_nhds_unique (planeProfile_core_density_tendsto hpair hP) hdensity
  simpa only [Function.comp_def, heq] using hs.hasSum

end Balanced.ProfileMarginalLimits

end

end OAI
