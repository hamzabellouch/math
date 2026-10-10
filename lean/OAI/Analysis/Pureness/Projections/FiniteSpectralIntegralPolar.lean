import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegral
import OAI.Analysis.Pureness.Stabilization.RankCyclic
import OAI.Analysis.Pureness.Stabilization.CuntzIdentities

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set
open scoped ENNReal NNReal

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem supported_cfc_polar_factor (x : D) (f : ℝ → ℝ)
    (hf : Continuous f) (hfpos : ∀ t, 0 ≤ f t) (δ : ℝ≥0) (hδ : 0 < δ)
    (hfzero : ∀ t : ℝ, t ≤ δ → f t = 0) :
    ∃ y : D, star y * y = cfcₙ f (star x * x) ∧
      y * star y = cfcₙ f (x * star x) := by
  obtain ⟨g, hg, hg0, hgf⟩ := supported_cfc_factor f hf hfpos δ hδ hfzero
  let a := Positive.starMul x
  let b := Positive.mulStar x
  have ha : IsSelfAdjoint a.1 := IsSelfAdjoint.of_nonneg a.2
  have hb : IsSelfAdjoint b.1 := IsSelfAdjoint.of_nonneg b.2
  have hid (c : Positive D) : cfcₙ g c.1 * c.1 * cfcₙ g c.1 = cfcₙ f c.1 := by
    calc
      _ = cfcₙ (fun t : ℝ => g t * t * g t) c.1 := by
        rw [cfcₙ_mul (fun t : ℝ => g t * t) g c.1,
          cfcₙ_mul g (fun t : ℝ => t) c.1, cfcₙ_id' ℝ c.1]
      _ = _ := cfcₙ_congr (fun t _ => hgf t)
  have hcomm : x * cfcₙ g a.1 = cfcₙ g b.1 * x :=
    cfc_intertwine a b x (by dsimp [a, b, Positive.starMul, Positive.mulStar]; exact (mul_assoc _ _ _).symm) g hg hg0
  let y := x * cfcₙ g a.1
  have hleft : star y * y = cfcₙ f a.1 := by
    dsimp [y]
    rw [star_mul, (cfcₙ_predicate g a.1).star_eq]
    calc
      _ = cfcₙ g a.1 * a.1 * cfcₙ g a.1 := by dsimp [a, Positive.starMul]; noncomm_ring
      _ = _ := hid a
  have hright : y * star y = cfcₙ f b.1 := by
    dsimp [y]
    rw [hcomm, star_mul, (cfcₙ_predicate g b.1).star_eq]
    calc
      _ = cfcₙ g b.1 * b.1 * cfcₙ g b.1 := by dsimp [b, Positive.mulStar]; noncomm_ring
      _ = _ := hid b
  exact ⟨y, hleft, hright⟩

theorem positive_cut_polar_cuntz (x : D) (δ : ℝ≥0) (hδ : 0 < δ) :
    CuntzBelow (Positive.cut δ (Positive.starMul x)) (Positive.cut δ (Positive.mulStar x)) ∧
    CuntzBelow (Positive.cut δ (Positive.mulStar x)) (Positive.cut δ (Positive.starMul x)) := by
  obtain ⟨y,hy,hz⟩ := supported_cfc_polar_factor x (fun t => max (t-δ) 0)
    ((continuous_id.sub continuous_const).max continuous_const) (fun _ => le_max_right _ _)
    δ hδ (fun t ht => max_eq_right (sub_nonpos.mpr ht))
  have hl : Positive.starMul y = Positive.cut δ (Positive.starMul x) := Subtype.ext hy
  have hr : Positive.mulStar y = Positive.cut δ (Positive.mulStar x) := Subtype.ext hz
  rw [← hl, ← hr]
  exact ⟨starMul_cuntzBelow_mulStar y, mulStar_cuntzBelow_starMul y⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finitePositiveClass_cut_polar (n : ℕ) (x : FinMatrix A n) (δ : ℝ≥0) (hδ : 0 < δ) :
    finitePositiveClass n (Positive.cut δ (Positive.starMul x)) =
      finitePositiveClass n (Positive.cut δ (Positive.mulStar x)) := by
  obtain ⟨h,h'⟩ := positive_cut_polar_cuntz x δ hδ
  exact le_antisymm ((finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr h))
    ((finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr h'))

theorem finiteSpectralIntegral_polar
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (n : ℕ) (x : FinMatrix A n) :
    finiteSpectralIntegral d n (Positive.starMul x) =
      finiteSpectralIntegral d n (Positive.mulStar x) := by
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold finiteDimensionDistribution
  rw [finitePositiveClass_cut_polar n x t.toNNReal (Real.toNNReal_pos.mpr ht)]
end CuntzPureness

end

end OAI
