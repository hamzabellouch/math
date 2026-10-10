import OAI.Combinatorics.BalancedRyser.Incidence.ProfileLimitIncidence
import OAI.Combinatorics.BalancedRyser.Probability.NearCoverFinite
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileShrinkingExceptions
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyRowIntegral

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

namespace FiniteProfile

theorem profileSequenceLimit_marginals
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ i : ℕ, Tendsto (fun n => ∑' j : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' j : ℕ, P (i, j)))) ∧
    (∀ j : ℕ, Tendsto (fun n => ∑' i : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' i : ℕ, P (i, j)))) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  have hP : IsBoundedProfile M P :=
    (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  let p : ℕ → {x : Profile | IsBoundedProfile M x} := fun n =>
    ⟨planeProfile (D n) (C n),
      planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2⟩
  have ht : Tendsto p atTop (𝓝 ⟨P, hP⟩) := by
    exact tendsto_subtype_rng.mpr hlim.2.1
  constructor
  · intro i
    exact (ProfileContinuity.continuous_boundedProfile_row_sum M i).tendsto
      ⟨P, hP⟩ |>.comp ht
  · intro j
    exact (ProfileContinuity.continuous_boundedProfile_column_sum M j).tendsto
      ⟨P, hP⟩ |>.comp ht

end FiniteProfile

namespace NearCoverVisibility

theorem nearCoverClass_limit_row_ae
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hεnonneg : ∀ q, 0 ≤ ε q)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    ∀ᵐ x ∂(νC : Measure Profile), (∑' j : ℕ, x (0, j)) = Real.exp (-(k : ℝ)) := by
  exact ProfileShrinkingExceptions.profileSequenceLimit_row_sum_eq_of_integral_tendsto_zero
    k D C (fun n => (hclass n).1) hlim _
    (nearCoverClass_integral_abs_tendsto k δ ε hεnonneg hε D C hclass hq)

theorem nearCoverClass_visibleExcess
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (ε : ℕ → ℝ)
    (hεnonneg : ∀ q, 0 ≤ ε q) (hε : Tendsto ε atTop (𝓝 0)) :
    ProfileVisibleExcess (NearCoverClass k δ ε) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hpair : ∀ n, IsProfilePair k (D n) (C n) := fun n => (hclass n).1
  obtain ⟨hP, hDsupport, hCsupport⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim
  obtain ⟨hmassD, hmassC, hincD, hincC⟩ :=
    FiniteProfile.profileSequenceLimit_mass_incidence k hpair hq hlim
  obtain ⟨hcorner, hbudget⟩ := nearCoverClass_limit_corner_budget k δ ε D C hclass hlim
  obtain ⟨hrows, hcols⟩ := FiniteProfile.profileSequenceLimit_marginals k D C hpair hlim
  have hrowSum : (∑' j : ℕ, P (0, j)) = Real.exp (-(k : ℝ)) := by
    apply tendsto_nhds_unique (hrows 0)
    simpa only [(FiniteProfile.planeProfile_zero_row_hasSum _ _).tsum_eq] using
      nearCoverClass_core_density_tendsto k δ ε hε D C hclass hq
  have hrow : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-(k : ℝ))) := by
    rw [← hrowSum]
    exact (OccupancyVisibility.row_summable_of_probability P hP.2.1 0).hasSum
  have huncovered : δ ≤ ∑' i : ℕ, P (i, 0) := by
    apply ge_of_tendsto (hcols 0)
    apply Eventually.of_forall
    intro n
    rw [(FiniteProfile.planeProfile_zero_column_hasSum _ _).tsum_eq]
    apply (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := F n)))).mpr
    exact (hclass n).2.2.1
  have hnormC : ∀ᵐ x ∂(νC : Measure Profile), (∀ ij, 0 ≤ x ij) ∧ HasSum x 1 := by
    filter_upwards [hCsupport] with x hx
    exact ⟨hx.1, hx.2.1⟩
  have hrowAE := nearCoverClass_limit_row_ae k δ ε hεnonneg hε D C hclass hq hlim
  have hmoment : HasSum (fun j : ℕ => (j : ℝ) * P (0, j))
      (c * Real.exp (-(k : ℝ))) := by
    have h := OccupancyVisibility.row_integral_hasSum (νC : Measure Profile) 0 hnormC
    have hint : (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂(νC : Measure Profile)) =
        c * Real.exp (-(k : ℝ)) := by
      rw [integral_congr_ae hrowAE, integral_const, smul_eq_mul, hmassC]
    rw [hint] at h
    convert h using 1
    funext j
    exact (hincC (0, j)).symm
  have hf : Integrable (fun x : Profile => x (0, 1)) (νC : Measure Profile) := by
    apply ((clippedProfileCoordinate (0, 1)).integrable (νC : Measure Profile)).congr
    filter_upwards [hCsupport] with x hx
    exact clippedProfileCoordinate_eq_of_bounded hx (0, 1)
  apply visible_excess_of_row_moments P (νD : Measure Profile) (νC : Measure Profile)
    (Real.exp_pos _) hδ hbudget hmassD hmassC
    (fun i j => by simpa using hincD (i + 1, j)) (by simpa using hincC (0, 1))
    hcorner (fun j => hP.1 (0, j)) hrow hmoment huncovered hf
  filter_upwards [hnormC, hrowAE] with x hx hxr
  exact ⟨fun j => hx.1 (0, j),
    OccupancyVisibility.row_summable_of_probability x hx.2 0, hxr⟩

end NearCoverVisibility
end Balanced

end

end OAI
