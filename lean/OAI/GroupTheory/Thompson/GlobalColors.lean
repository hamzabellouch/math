import OAI.GroupTheory.Thompson.PartitionColorFamily
import OAI.GroupTheory.Thompson.RestrictionCovariance
import OAI.GroupTheory.Thompson.CorrelationVariance

namespace OAI

/-!
# Globally defined colors of the actual Thompson-group images

A non-basic image, or a basic image failing the simultaneous family respect
condition, receives zero. Thus every correlation is bounded on the entire
actual group, including outside a finite set used for averaging.
-/

noncomputable section

open scoped InnerProductSpace

universe uE

namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

/-- The genuine partial image of the uniform partition, made total with `none`. -/
def imagePartitionOption (g : F) (n : ℕ) : Option BasicPartition := by
  classical
  exact if hg : ImageBasic g n then some (imagePartition g n hg) else none

/-- One condition for the whole actual parent/child family at a group element. -/
def GlobalAdmissible (D n : ℕ) (g : F) : Prop :=
  ∃ hg : ImageBasic g n, PartitionAdmissible D (imagePartition g n hg)

def globalColor (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q : IntervalIndex D) (g : F) : UnitBall E :=
  optionFamilyColor hD f (imagePartitionOption g n) q

theorem globalColor_of_imageBasic (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (g : F) (hg : ImageBasic g n) (q : IntervalIndex D) :
    globalColor hD f n q g = partitionFamilyColor hD f (imagePartition g n hg) q := by
  simp only [globalColor, imagePartitionOption, dite_eq_left hg, optionFamilyColor_some]

theorem globalColor_of_image_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (g : F) (hg : ImageBasic g n)
    (hp : PartitionAdmissible D (imagePartition g n hg)) (q : IntervalIndex D) :
    globalColor hD f n q g =
      partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
        ((imagePartition g n hg).restrict (familyInterval D q) (hp q)) := by
  rw [globalColor_of_imageBasic hD f n g hg q]
  exact partitionFamilyColor_of_admissible hD f _ hp q

theorem globalColor_of_not_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (g : F)
    (h : ¬GlobalAdmissible D n g) (q : IntervalIndex D) :
    globalColor hD f n q g = unitBallZero E := by
  classical
  by_cases hg : ImageBasic g n
  · rw [globalColor_of_imageBasic hD f n g hg q]
    exact partitionFamilyColor_of_not_admissible hD f _
      (fun hp => h ⟨hg, hp⟩) q
  · simp only [globalColor, imagePartitionOption, dite_eq_right hg, optionFamilyColor_none]

theorem globalColor_norm_le (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q : IntervalIndex D) (g : F) :
    ‖(globalColor hD f n q g : E)‖ ≤ 1 :=
  (globalColor hD f n q g).property

/-- The actual finite group set has one common admissibility level. -/
theorem eventually_global_admissible (D : ℕ) (K : Finset F) :
    ∃ N, ∀ n ≥ N, ∀ g ∈ K, GlobalAdmissible D n g := by
  obtain ⟨N, hN⟩ := eventually_image_respects K (intervalFamily D)
  refine ⟨N, ?_⟩
  intro n hn g hg
  obtain ⟨hb, hr⟩ := hN n hn g hg
  exact ⟨hb, fun q => hr (familyInterval D q) (familyInterval_mem D q)⟩

theorem exists_common_admissible (D : ℕ) (K : Finset F) :
    ∃ n, ∀ g ∈ K, GlobalAdmissible D n g := by
  obtain ⟨N, hN⟩ := eventually_global_admissible D K
  exact ⟨N, hN N le_rfl⟩

/-- The exact recursive identity at every admissible actual group point. -/
theorem globalColor_parent (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (g : F) (hg : GlobalAdmissible D n g) (i : Fin D) :
    globalColor hD f n (.inl i) g =
      f (ballMean hD (fun j => globalColor hD f n (.inr (i, j)) g)) := by
  obtain ⟨hb, hp⟩ := hg
  simp only [globalColor_of_imageBasic hD f n g hb]
  exact partitionFamilyColor_parent hD f _ hp i

/-- Source and target admissibility suffice; the transport need not preserve
any other selected interval. -/
theorem globalColor_covariance (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (h g : F) (q r : IntervalIndex D)
    (hc : CarriesAffinely h (familyInterval D q) (familyInterval D r))
    (hg : GlobalAdmissible D n g) (hhg : GlobalAdmissible D n (h * g)) :
    globalColor hD f n q g = globalColor hD f n r (h * g) := by
  obtain ⟨hb, hp⟩ := hg
  obtain ⟨hhb, hhp⟩ := hhg
  rw [globalColor_of_image_admissible hD f n g hb hp q,
    globalColor_of_image_admissible hD f n (h * g) hhb hhp r]
  apply congrArg (partitionColor (selectedInterval D) (selectedInterval_internal D) hD f)
  exact (image_restrict_covariance h g n (familyInterval D q) (familyInterval D r)
    hc hb hhb (hp q) (hhp r)).symm

/-- A real correlation on all of the actual group. -/
def globalCorrelation (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q r : IntervalIndex D) (g : F) : ℝ :=
  ⟪(globalColor hD f n q g : E), globalColor hD f n r g⟫_ℝ

theorem globalCorrelation_abs_le_one (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (q r : IntervalIndex D) (g : F) :
    |globalCorrelation hD f n q r g| ≤ 1 :=
  unit_inner_abs_le _ _ (globalColor_norm_le hD f n q g)
    (globalColor_norm_le hD f n r g)

theorem globalCorrelation_covariance (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (h g : F) (q r q' r' : IntervalIndex D)
    (hq : CarriesAffinely h (familyInterval D q) (familyInterval D q'))
    (hr : CarriesAffinely h (familyInterval D r) (familyInterval D r'))
    (hg : GlobalAdmissible D n g) (hhg : GlobalAdmissible D n (h * g)) :
    globalCorrelation hD f n q r g = globalCorrelation hD f n q' r' (h * g) := by
  unfold globalCorrelation
  rw [globalColor_covariance hD f n h g q q' hq hg hhg,
    globalColor_covariance hD f n h g r r' hr hg hhg]

/-- Exact affine covariance and global boundedness imply the finite comparison. -/
theorem globalCorrelation_translate_bound (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (A : Finset F) (hA : A.Nonempty)
    (h : F) (q r q' r' : IntervalIndex D)
    (hq : CarriesAffinely h (familyInterval D q) (familyInterval D q'))
    (hr : CarriesAffinely h (familyInterval D r) (familyInterval D r'))
    (hg : ∀ g ∈ A, GlobalAdmissible D n g)
    (hhg : ∀ g ∈ A, GlobalAdmissible D n (h * g)) :
    |realAvg A (globalCorrelation hD f n q r) -
      realAvg A (globalCorrelation hD f n q' r')| ≤ boundaryRatio A h := by
  classical
  have heq : realAvg A (globalCorrelation hD f n q r) =
      realAvg A (fun g => globalCorrelation hD f n q' r' (h * g)) := by
    apply realAvg_congr
    intro g hmem
    exact globalCorrelation_covariance hD f n h g q r q' r' hq hr
      (hg g hmem) (hhg g hmem)
  rw [heq]
  exact abs_realAvg_translate_sub_le A hA h (globalCorrelation hD f n q' r')
    (globalCorrelation_abs_le_one hD f n q' r')

end ThompsonNonamenability

end

end OAI
