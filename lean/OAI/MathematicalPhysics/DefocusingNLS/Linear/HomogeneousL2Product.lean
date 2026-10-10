import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzObservation

namespace OAI

/-! # Actual multiplication of physical L² data by a Y coefficient

The coefficient is the bounded continuous physical representative. This
bilinear map supplies the principal part of each top-order derivative.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure E)

private theorem physicalL2Product_memLp (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V : HomogeneousY a k) (u : H) :
    MemLp (fun x => homogeneousPhysicalCLM a k ha ha1 hk V x * u x) 2 volume := by
  apply (Lp.memLp u).of_le_mul
    ((homogeneousPhysicalCLM a k ha ha1 hk V).continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u))
  filter_upwards [] with x
  exact (norm_mul _ _).trans_le
    (mul_le_mul_of_nonneg_right
      (homogeneousPhysical_point_bound a k ha ha1 hk V x) (norm_nonneg _))

noncomputable def homogeneousPhysicalL2ProductValue (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V : HomogeneousY a k) (u : H) : H :=
  (physicalL2Product_memLp a k ha ha1 hk V u).toLp
    (fun x => homogeneousPhysicalCLM a k ha ha1 hk V x * u x)

theorem homogeneousPhysicalL2ProductValue_ae (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V : HomogeneousY a k) (u : H) :
    homogeneousPhysicalL2ProductValue a k ha ha1 hk V u =ᵐ[volume]
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk V x * u x) :=
  MemLp.coeFn_toLp _

theorem homogeneousPhysicalL2ProductValue_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V : HomogeneousY a k) (u : H) :
    ‖homogeneousPhysicalL2ProductValue a k ha ha1 hk V u‖ ≤
      ‖homogeneousPointEvaluation a k ha ha1 hk 0‖ * ‖V‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (homogeneousPhysical_point_bound a k ha ha1 hk V x) (norm_nonneg _)

noncomputable def homogeneousPhysicalL2Product (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℂ] H →L[ℂ] H :=
  let A := homogeneousPhysicalL2ProductValue a k ha ha1 hk
  let B : HomogeneousY a k →ₗ[ℂ] H →ₗ[ℂ] H := LinearMap.mk₂ ℂ A
    (fun V W u => by
      apply Lp.ext
      filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk (V + W) u,
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V u,
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk W u,
        Lp.coeFn_add (A V u) (A W u)] with x hsum hV hW hout
      change A (V + W) u x = (A V u + A W u : H) x
      rw [hsum, hout, Pi.add_apply, hV, hW, map_add,
        ZeroAtInftyContinuousMap.add_apply, add_mul])
    (fun c V u => by
      apply Lp.ext
      filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk (c • V) u,
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V u,
        Lp.coeFn_smul c (A V u)] with x hcv hV hout
      change A (c • V) u x = (c • A V u : H) x
      rw [hcv, hout, Pi.smul_apply, hV, map_smul,
        ZeroAtInftyContinuousMap.smul_apply]
      simp only [smul_eq_mul]
      ring)
    (fun V u v => by
      apply Lp.ext
      filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V (u + v),
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V u,
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V v,
        Lp.coeFn_add u v, Lp.coeFn_add (A V u) (A V v)] with x hsum hu hv hin hout
      change A V (u + v) x = (A V u + A V v : H) x
      rw [hsum, hout, hin, Pi.add_apply, Pi.add_apply, hu, hv, mul_add])
    (fun c V u => by
      apply Lp.ext
      filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V (c • u),
        homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk V u,
        Lp.coeFn_smul c u, Lp.coeFn_smul c (A V u)] with x hcu hu hin hout
      change A V (c • u) x = (c • A V u : H) x
      rw [hcu, hout, hin, Pi.smul_apply, Pi.smul_apply, hu]
      simp only [smul_eq_mul]
      ring)
  B.mkContinuous₂ ‖homogeneousPointEvaluation a k ha ha1 hk 0‖
    (homogeneousPhysicalL2ProductValue_norm_le a k ha ha1 hk)

@[simp] theorem homogeneousPhysicalL2Product_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V : HomogeneousY a k) (u : H) :
    homogeneousPhysicalL2Product a k ha ha1 hk V u =
      homogeneousPhysicalL2ProductValue a k ha ha1 hk V u := rfl

theorem homogeneousPhysicalL2Product_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (V f : 𝓢(E, ℂ)) :
    homogeneousPhysicalL2Product a k ha ha1 hk
      (homogeneousSchwartzEmbedding a k ha ha1 hk V) (f.toLp 2 volume) =
        (SchwartzMap.smulLeftCLM ℂ V f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [homogeneousPhysicalL2ProductValue_ae a k ha ha1 hk
    (homogeneousSchwartzEmbedding a k ha ha1 hk V) (f.toLp 2 volume),
    SchwartzMap.coeFn_toLp f 2 volume,
    SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ V f) 2 volume] with x hprod hf hout
  change homogeneousPhysicalL2ProductValue a k ha ha1 hk _ _ x = _
  rw [hprod, homogeneousPhysicalCLM_Schwartz, hf, hout,
    SchwartzMap.smulLeftCLM_apply_apply V.hasTemperateGrowth, smul_eq_mul]

end DefocusingNLS

end OAI
