import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFourierIsometry

namespace OAI

/-! # Multiplication of torus L² functions by continuous coefficients -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure T)
noncomputable local instance torusL2ProductMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusL2ProductProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem torusL2Product_memLp (V : C(T, ℂ)) (f : H) :
    MemLp (fun x => V x * f x) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := ‖V‖)
    (V.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [] with x
  change ‖V x * f x‖ ≤ ‖V‖ * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm V x) (norm_nonneg _)

noncomputable def torusL2ProductValue (V : C(T, ℂ)) (f : H) : H :=
  (torusL2Product_memLp V f).toLp (fun x => V x * f x)

theorem torusL2ProductValue_ae (V : C(T, ℂ)) (f : H) :
    torusL2ProductValue V f =ᵐ[volume] (fun x => V x * f x) := MemLp.coeFn_toLp _

theorem torusL2ProductValue_norm_le (V : C(T, ℂ)) (f : H) :
    ‖torusL2ProductValue V f‖ ≤ ‖V‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [torusL2ProductValue_ae V f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm V x) (norm_nonneg _)

noncomputable def torusL2Product (V : C(T, ℂ)) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := torusL2ProductValue V
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [torusL2ProductValue_ae V (f + g), torusL2ProductValue_ae V f,
          torusL2ProductValue_ae V g, Lp.coeFn_add f g,
          Lp.coeFn_add (torusL2ProductValue V f) (torusL2ProductValue V g)] with x hfg hf hg ha hb
        rw [hfg, ha, hb]
        simp only [Pi.add_apply]
        rw [hf, hg, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [torusL2ProductValue_ae V (c • f), torusL2ProductValue_ae V f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (torusL2ProductValue V f)] with x hcf hf ha hb
        simp only [RingHom.id_apply]
        rw [hcf, ha, hb]
        simp only [Pi.smul_apply]
        rw [hf]
        simp only [smul_eq_mul]
        ring }
    ‖V‖ (torusL2ProductValue_norm_le V)

theorem torusL2Product_ae (V : C(T, ℂ)) (f : H) :
    torusL2Product V f =ᵐ[volume] (fun x => V x * f x) :=
  torusL2ProductValue_ae V f

theorem torusL2Product_continuous (V f : C(T, ℂ)) :
    torusL2Product V (f.toLp 2 volume ℂ) = (V * f).toLp 2 volume ℂ := by
  apply Lp.ext
  have hf : (f.toLp 2 volume ℂ : H) =ᵐ[volume] f :=
    ContinuousMap.coeFn_toLp volume f
  have hout : ((V * f).toLp 2 volume ℂ : H) =ᵐ[volume] (V * f) :=
    ContinuousMap.coeFn_toLp volume (V * f)
  filter_upwards [torusL2ProductValue_ae V (f.toLp 2 volume ℂ),
    hf, hout] with x hp hfx houtx
  change torusL2ProductValue V (f.toLp 2 volume ℂ) x = _
  rw [hp, hfx, houtx]
  rfl

theorem torusL2Product_mFourier (m n : Fin 12 → ℤ) :
    torusL2Product (UnitAddTorus.mFourier m) (UnitAddTorus.mFourierLp 2 n) =
      UnitAddTorus.mFourierLp 2 (m + n) := by
  rw [torusL2Product_continuous]
  congr 1
  ext x
  exact (UnitAddTorus.mFourier_add (m := m) (n := n)).symm

end DefocusingNLS

end OAI
