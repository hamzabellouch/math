import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusDirectionalFourier

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance torusDirectionalDerivativeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusDirectionalDerivativeProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TorusRealPlane := Fin 2 → ℝ

def torusRealProjection (x : TorusRealPlane) : UnitAddTorus (Fin 2) := fun j => (x j:UnitAddCircle)
def torusRealRepresentative (θ : UnitAddTorus (Fin 2)) : TorusRealPlane :=
  (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) θ).val

lemma continuous_torusRealProjection : Continuous torusRealProjection := by
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_apply j)

lemma measurable_torusRealRepresentative : Measurable torusRealRepresentative :=
  measurable_subtype_coe.comp (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurable

lemma torusRealProjection_representative (θ : UnitAddTorus (Fin 2)) :
    torusRealProjection (torusRealRepresentative θ)=θ :=
  (measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply θ

lemma torusRealProjection_add (x y : TorusRealPlane) :
    torusRealProjection (x+y)=torusRealProjection x+torusRealProjection y := by
  ext j
  simp [torusRealProjection]

lemma torusRealProjection_direction (j : Fin 2) (t : ℝ) :
    torusRealProjection (t • Pi.single j (1:ℝ))=torusCoordinateShift j t := by
  ext i
  by_cases hij : i=j <;> simp [torusRealProjection,torusCoordinateShift,hij]

lemma torusRealRepresentative_ae {P : TorusRealPlane → Prop}
    (h : ∀ᵐ x ∂(volume : Measure TorusRealPlane),P x) :
    ∀ᵐ θ : UnitAddTorus (Fin 2), P (torusRealRepresentative θ) := by
  let K : Set TorusRealPlane := {x | ∀ i,x i∈Ioc (0:ℝ) (0+1)}
  have hK : MeasurableSet K := MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hp := (measurePreserving_subtype_coe hK).comp
    (measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ)))
  exact hp.quasiMeasurePreserving.ae (ae_restrict_of_ae h)

lemma torusRealLift_lipschitz (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|) :
    LipschitzWith (2*K) (fun x : TorusRealPlane => f (torusRealProjection x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : torusRealProjection x=(torusRealProjection y+torusCoordinateShift 0 (x 0-y 0))+
      torusCoordinateShift 1 (x 1-y 1) := by
    ext j
    fin_cases j <;> simp [torusRealProjection,torusCoordinateShift]
  have hx (j : Fin 2) : |x j-y j|≤dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y j
  calc
    dist (f (torusRealProjection x)) (f (torusRealProjection y)) ≤
        dist (f (torusRealProjection x))
          (f (torusRealProjection y+torusCoordinateShift 0 (x 0-y 0)))+
        dist (f (torusRealProjection y+torusCoordinateShift 0 (x 0-y 0)))
          (f (torusRealProjection y)) := dist_triangle _ _ _
    _≤(K:ℝ)*|x 1-y 1|+(K:ℝ)*|x 0-y 0| := by
      apply add_le_add
      · rw [dist_eq_norm,he]
        exact hLip 1 _ _
      · rw [dist_eq_norm]
        exact hLip 0 _ _
    _≤((2*K:ℝ≥0):ℝ)*dist x y := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (hx 0) K.coe_nonneg,
        mul_le_mul_of_nonneg_left (hx 1) K.coe_nonneg]

def torusDirectionalDerivative (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) : ℂ :=
  lineDeriv ℝ (fun x => f (torusRealProjection x)) (torusRealRepresentative θ) (Pi.single j 1)

lemma torusDirectionalDerivative_eq (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) :
    torusDirectionalDerivative f j θ=deriv (fun t => f (θ+torusCoordinateShift j t)) 0 := by
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  change f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=_
  rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]

lemma measurable_torusDirectionalDerivative {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : Continuous f) (j : Fin 2) : Measurable (torusDirectionalDerivative f j) :=
  (measurable_lineDeriv (hf.comp continuous_torusRealProjection)).comp measurable_torusRealRepresentative

lemma torusDirectionalDerivative_ae (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|) (j : Fin 2) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (torusDirectionalDerivative f j θ) 0 := by
  have hd : ∀ᵐ x ∂(volume : Measure TorusRealPlane),
      DifferentiableAt ℝ (fun y => f (torusRealProjection y)) x :=
    (torusRealLift_lipschitz f K hLip).ae_differentiableAt
  filter_upwards [torusRealRepresentative_ae hd] with θ hθ
  have he (t : ℝ) : f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=
      f (θ+torusCoordinateShift j t) := by
    rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]
  simpa only [HasLineDerivAt,he,torusDirectionalDerivative] using (hθ.lineDifferentiableAt (v:=Pi.single j 1)).hasLineDerivAt

lemma torusDirectionalDerivative_norm (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (θ : UnitAddTorus (Fin 2)) :
    ‖torusDirectionalDerivative f j θ‖≤2*K := by
  have h := norm_lineDeriv_le_of_lipschitz ℝ (torusRealLift_lipschitz f K hLip)
    (x₀:=torusRealRepresentative θ) (v:=Pi.single j 1)
  simpa only [torusDirectionalDerivative,NNReal.coe_mul,NNReal.coe_ofNat,
    Pi.norm_single,norm_one,mul_one] using h

theorem torusDirectionalDerivative_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (torusDirectionalDerivative f j) h=
      (2*Real.pi*Complex.I*(h j))*mFourierCoeff f h :=
  mFourierCoeff_of_directional_derivative f j K K.coe_nonneg (hLip j)
    (measurable_torusDirectionalDerivative f.continuous j).aestronglyMeasurable
    (torusDirectionalDerivative_ae f K hLip j) h

end ScalarConductivity

end
end

end OAI
