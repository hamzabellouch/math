import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralSmoothTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance torusDirectionalFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusDirectionalFourierProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusCoordinateShift_add (j : Fin 2) (s t : ℝ) :
    torusCoordinateShift j (s+t)=torusCoordinateShift j s+torusCoordinateShift j t := by
  ext i
  by_cases hi : i=j <;> simp [torusCoordinateShift,hi]

lemma torusCoordinateShift_zero (j : Fin 2) : torusCoordinateShift j 0=0 := by
  ext i
  simp [torusCoordinateShift]

lemma continuous_torusCoordinateShift (j : Fin 2) : Continuous (torusCoordinateShift j) := by
  apply continuous_pi
  intro i
  by_cases hi : i=j
  · simpa [torusCoordinateShift,hi] using AddCircle.continuous_mk' (1:ℝ)
  · simpa [torusCoordinateShift,hi] using (continuous_const : Continuous (fun _ : ℝ => (0 : UnitAddCircle)))

theorem mFourierCoeff_of_directional_derivative
    (f : C(UnitAddTorus (Fin 2),ℂ)) (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hLip : ∀ t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤K*|t|)
    {d : UnitAddTorus (Fin 2) → ℂ} (hd : AEStronglyMeasurable d volume)
    (hder : ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (d θ) 0)
    (h : TorusModes) :
    mFourierCoeff d h = (2*Real.pi*Complex.I*(h j)) * mFourierCoeff f h := by
  let F : ℝ → UnitAddTorus (Fin 2) → ℂ := fun t θ =>
    mFourier (-h) θ * f (θ+torusCoordinateShift j t)
  have hFc (t : ℝ) : Continuous (F t) :=
    (mFourier (-h)).continuous.mul (f.continuous.comp (continuous_id.add continuous_const))
  have hFL : ∀ᵐ θ : UnitAddTorus (Fin 2),
      LipschitzOnWith (Real.nnabs K) (fun t => F t θ) univ := by
    apply Eventually.of_forall
    intro θ
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro t s
    have he : θ+torusCoordinateShift j t=
        (θ+torusCoordinateShift j s)+torusCoordinateShift j (t-s) := by
      rw [add_assoc,←torusCoordinateShift_add,add_sub_cancel]
    calc
      dist (F t θ) (F s θ)=‖f (θ+torusCoordinateShift j t)-f (θ+torusCoordinateShift j s)‖ := by
        rw [dist_eq_norm]
        simp only [F,←mul_sub,norm_mul,mFourier_norm_one,one_mul]
      _≤K*|t-s| := by rw [he]; exact hLip (t-s) (θ+torusCoordinateShift j s)
      _=(Real.nnabs K:ℝ)*dist t s := by rw [Real.coe_nnabs,abs_of_nonneg hK,Real.dist_eq]
  have hI := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ:=(volume : Measure (UnitAddTorus (Fin 2))))
    (F:=F) (F':=fun θ => mFourier (-h) θ*d θ)
    (s:=univ) (bound:=fun _ => K) (x₀:=(0:ℝ)) (univ_mem)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((mFourier (-h)).continuous.aestronglyMeasurable.mul hd) hFL
    (integrable_const _) (hder.mono fun θ hθ => hθ.const_mul _)
  have he : (fun t => ∫ θ,F t θ) =
      fun t : ℝ => Complex.exp (2*Real.pi*Complex.I*(h j)*t)*mFourierCoeff f h := by
    funext t
    change mFourierCoeff (fun θ => f (θ+torusCoordinateShift j t)) h=_
    rw [mFourierCoeff_translation,mFourier_coordinateShift]
  rw [he] at hI
  have hE := ((((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul
    (2*Real.pi*Complex.I*(h j))).cexp).mul_const (mFourierCoeff f h)
  have heD := hI.2.unique hE
  simpa only [mFourierCoeff,smul_eq_mul,id_eq,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,Complex.ofReal_one,mul_one,one_mul] using heD

end ScalarConductivity

end
end

end OAI
