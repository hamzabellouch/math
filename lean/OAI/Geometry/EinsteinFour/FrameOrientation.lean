import OAI.Geometry.EinsteinFour.FrameBundle

namespace OAI

/-! An orientation is a continuous choice of one of the two orientation
classes in every orthonormal frame fiber. This separates the individual
Weyl norms used by the scalar argument from the orientation-independent sum
used in radial averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure FrameOrientation (g : SmoothMetric M) where
  positive : Set (FrameBundle g)
  clopen : IsClopen positive
  nonempty_fiber : ∀ c, ∃ e : OrthonormalFrame g c, (⟨c, e⟩ : FrameBundle g) ∈ positive
  compatible : ∀ c (e f : OrthonormalFrame g c),
    (⟨c, e⟩ : FrameBundle g) ∈ positive →
      ((⟨c, f⟩ : FrameBundle g) ∈ positive ↔ 0 < e.matrix.det * f.matrix.det)

def FrameOrientation.frame {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    OrthonormalFrame g c := Classical.choose (o.nonempty_fiber c)

theorem FrameOrientation.frame_positive {g : SmoothMetric M} (o : FrameOrientation g)
    (c : M) : (⟨c, o.frame c⟩ : FrameBundle g) ∈ o.positive :=
  Classical.choose_spec (o.nonempty_fiber c)

theorem FrameOrientation.positive_iff_det {g : SmoothMetric M} (o : FrameOrientation g)
    (c : M) (e : OrthonormalFrame g c) :
    (⟨c, e⟩ : FrameBundle g) ∈ o.positive ↔ 0 < (o.frame c).matrix.det * e.matrix.det :=
  o.compatible c (o.frame c) e (o.frame_positive c)

def plusNorm {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedBlockNorm (plusWeyl g c (o.frame c))

def minusNorm {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedBlockNorm (minusWeyl g c (o.frame c))

theorem plusNorm_nonneg {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    0 ≤ plusNorm o c := normalizedBlockNorm_nonneg _

theorem minusNorm_nonneg {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    0 ≤ minusNorm o c := normalizedBlockNorm_nonneg _

theorem plusNorm_eq_zero_iff {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    plusNorm o c = 0 ↔ plusWeyl g c (o.frame c) = 0 :=
  normalizedBlockNorm_eq_zero_iff _

theorem minusNorm_eq_zero_iff {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    minusNorm o c = 0 ↔ minusWeyl g c (o.frame c) = 0 :=
  normalizedBlockNorm_eq_zero_iff _

end

end PositiveEinsteinFour.Geometry

end OAI
