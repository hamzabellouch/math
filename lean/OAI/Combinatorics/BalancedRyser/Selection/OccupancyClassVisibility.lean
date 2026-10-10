import OAI.Combinatorics.BalancedRyser.Profiles.ProfileLimitLaws
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarginalContinuity
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyRowIntegral
import OAI.Combinatorics.BalancedRyser.Selection.ProfileOccupancy2
import OAI.Combinatorics.BalancedRyser.Selection.RobustOccupancyAssembly

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology NNReal

universe u

namespace OccupancyClassVisibility

theorem coordinate_error_le_two_tv
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (k : ℕ) (D : Finset (Line F)) (i : ℕ) :
    |empiricalMultiplicityMass D i - deletionPoissonMass k i| ≤
      2 * deletionMultiplicityTV k D := by
  have hs := ((FiniteProfile.empirical_multiplicity_hasSum D).summable.sub
    (deletionPoissonMass_hasSum k).summable).abs
  have h := hs.le_tsum i (fun j _ => abs_nonneg
    (empiricalMultiplicityMass D j - deletionPoissonMass k j))
  unfold deletionMultiplicityTV
  linarith

theorem plane_zero_row_eq_empirical_zero
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) :
    (∑' j : ℕ, planeProfile D C (0, j)) = empiricalMultiplicityMass D 0 := by
  rw [(FiniteProfile.planeProfile_zero_row_hasSum D C).tsum_eq]
  unfold empiricalMultiplicityMass uncoveredBy
  congr 3
  ext p
  simp [deletionMultiplicity, Finset.filter_eq_empty_iff]

theorem plane_row_tendsto
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (k : ℕ)
    (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) (i : ℕ) :
    Tendsto (fun n => ∑' j : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' j : ℕ, P (i, j))) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  let S := {p : Profile | IsBoundedProfile M p}
  let p : ℕ → S := fun n => ⟨planeProfile (D n) (C n),
    planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2⟩
  let p₀ : S := ⟨P,
    (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1⟩
  have ht : Tendsto p atTop (𝓝 p₀) := tendsto_subtype_rng.mpr hlim.2.1
  exact (ProfileContinuity.continuous_boundedProfile_row_sum M i).tendsto p₀ |>.comp ht

theorem isCompact_row_constraint (M : ℝ) (hM : 0 ≤ M)
    (i : ℕ) (A : Set ℝ) (hA : IsClosed A) :
    IsCompact {p : Profile | IsBoundedProfile M p ∧ (∑' j : ℕ, p (i, j)) ∈ A} := by
  let S := {p : Profile | IsBoundedProfile M p}
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (ProfileAmbientCompactness.isCompact_boundedProfiles M hM)
  have hc : IsCompact {p : S | (∑' j : ℕ, p.val (i, j)) ∈ A} :=
    (hA.preimage (ProfileContinuity.continuous_boundedProfile_row_sum M i)).isCompact
  have hi := hc.image (continuous_subtype_val : Continuous (Subtype.val : S → Profile))
  convert hi using 1
  ext p
  constructor
  · rintro ⟨hp, hrow⟩
    exact ⟨⟨p, hp⟩, hrow, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

theorem cover_row_closed_support
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (k : ℕ)
    (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (i : ℕ) (A : Set ℝ) (hA : IsClosed A)
    (hrow : ∀ n, ∀ l ∈ C n, (∑' j : ℕ, lineProfile (D n) (C n) l (i, j)) ∈ A) :
    ∀ᵐ p ∂(νC : Measure Profile), (∑' j : ℕ, p (i, j)) ∈ A := by
  have hK := isCompact_row_constraint (2 * (k : ℝ) + 4) (by positivity) i A hA
  have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK
    (μ := fun n => empiricalProfileMeasure (D n) (C n) (C n))
    (fun n => ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
      (D n) (C n) (C n) hK.measurableSet (fun l hl =>
        ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
          hrow n l hl⟩)) hlim.2.2.2
  have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νC _).mp hzero)
  exact hae.mono fun _ hp => hp.2

end OccupancyClassVisibility

theorem occupancyFailureClass_limit_zero_row
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    HasSum (fun j : ℕ => P (0, j)) (Real.exp (-(k : ℝ))) := by
  have hpair := fun n => (hclass n).1
  have hP := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  have hrow := OccupancyClassVisibility.plane_row_tendsto k D C hpair hlim 0
  have hzero : deletionPoissonMass k 0 = Real.exp (-(k : ℝ)) := by
    simp [deletionPoissonMass, ProbabilityTheory.poissonMeasure_real_singleton]
  have hmass : Tendsto (fun n => empiricalMultiplicityMass (D n) 0)
      atTop (𝓝 (Real.exp (-(k : ℝ)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (by simpa using (hε.comp hq).const_mul 2)
    intro n
    rw [Real.norm_eq_abs, ← hzero]
    exact (OccupancyClassVisibility.coordinate_error_le_two_tv k (D n) 0).trans
      (mul_le_mul_of_nonneg_left (hclass n).2.2.1 (by norm_num))
  have heq : (∑' j : ℕ, P (0, j)) = Real.exp (-(k : ℝ)) := by
    apply tendsto_nhds_unique hrow
    simpa only [OccupancyClassVisibility.plane_zero_row_eq_empirical_zero] using hmass
  exact heq ▸ (OccupancyVisibility.row_summable_of_probability P hP.2.1 0).hasSum

theorem occupancyFailureClass_limit_common_sign
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ᵐ x : Profile ∂(νC : Measure Profile),
      Real.exp (-(k : ℝ)) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
    (∀ᵐ x : Profile ∂(νC : Measure Profile),
      (∑' j : ℕ, x (0, j)) ≤ Real.exp (-(k : ℝ)) - lam) := by
  cases high
  · right
    apply OccupancyClassVisibility.cover_row_closed_support k D C
      (fun n => (hclass n).1) hlim 0 (Set.Iic _) isClosed_Iic
    intro n l hl
    rw [(FiniteProfile.lineProfile_zero_row_hasSum (D n) (C n) l).tsum_eq]
    exact (hclass n).2.2.2 l hl
  · left
    apply OccupancyClassVisibility.cover_row_closed_support k D C
      (fun n => (hclass n).1) hlim 0 (Set.Ici _) isClosed_Ici
    intro n l hl
    rw [(FiniteProfile.lineProfile_zero_row_hasSum (D n) (C n) l).tsum_eq]
    exact (hclass n).2.2.2 l hl

theorem occupancyFailureClass_visibleExcess
    (k : ℕ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (high : Bool) :
    ProfileVisibleExcess (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hpair := fun n => (hclass n).1
  have hs := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).2.2
  apply OccupancyVisibility.visible_excess_of_normalized_common_sign
    P (νD : Measure Profile) (νC : Measure Profile)
    (ha.trans_le (occupancyFailureClass_limit_density_lower k a lam ε high D C hclass hlim))
    hlam (hlim.deletion_mass (fun n => (hpair n).1) hq) hlim.cover_mass
  · intro i j
    simpa only [Nat.cast_add, Nat.cast_one] using hlim.deletion_incidence (i + 1, j)
  · exact hlim.cover_incidence
  · exact hs.mono (fun x hx => ⟨hx.1, hx.2.1⟩)
  · exact occupancyFailureClass_limit_zero_row k a lam ε high hε D C hclass hq hlim
  · exact occupancyFailureClass_limit_common_sign k a lam ε high D C hclass hlim

theorem robustOccupancy_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K lam : ℝ) (hlam : 0 < lam) :
    ∀ η : ℝ, 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  apply robustOccupancy_extend_fraction k K lam
  intro η hη hηone
  apply robustOccupancy_of_profileCounting_of_visible hcounting k hk K lam η hη hηone
  intro ε hε high
  exact occupancyFailureClass_visibleExcess k (η / 4) lam (by positivity) hlam ε hε high

end Balanced

end

end OAI
