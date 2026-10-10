import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalTestEnergy
import OAI.Analysis.Conductivity.Fourier.CylinderFourierGraph
import OAI.Analysis.Conductivity.Sources.AngularJet

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance angularGraphMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance angularGraphIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma smoothAxisModeJet_ae {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) (j : Fin 4) :
    (smoothAxisModeJet hq R h) j =ᵐ[FiniteAxisMeasure R]
      fun t => ![q t,deriv q t,(Complex.I*(h 0))*q t,(Complex.I*(h 1))*q t] j := by
  have hq₀ := smoothFiniteAxisLp_ae hq.continuous R
  have hq₁ := smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R
  have hq₂ := Lp.coeFn_smul (Complex.I*(h 0:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  have hq₃ := Lp.coeFn_smul (Complex.I*(h 1:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  fin_cases j
  · exact hq₀
  · exact hq₁
  · exact hq₂.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])
  · exact hq₃.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])

lemma sourceAngularLpJet_coefficient {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes) :
    cylinderJetCoefficient R (sourceAngularLpJet hf a b R) h=
      smoothAxisModeJet (sourceAngularCoefficient_smooth hf a b h) R h := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [cylinderCoefficientLp_ae (sourceAngularLpJet hf a b R j) h,
    Measure.ae_ae_of_ae_prod (sourceAngularLpJet_ae hf a b R j),
    smoothAxisModeJet_ae (sourceAngularCoefficient_smooth hf a b h) R h j,
    ae_restrict_mem measurableSet_Ioc] with t ht₁ ht₂ ht₃ htm
  change cylinderCoefficientLp (sourceAngularLpJet hf a b R j) h t=_
  rw [ht₁,ht₃]
  calc
    cylinderCoefficient (sourceAngularLpJet hf a b R j) h t=
        mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h := by
      unfold cylinderCoefficient mFourierCoeff
      apply integral_congr_ae
      filter_upwards [ht₂] with θ hθ
      rw [hθ]
    _=_ := sourceAngularJet_fourier hf a b R h (Ioc_subset_Icc_self htm) j

theorem sourceAngularLpJet_graph (s : Fin 3 → ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) :
    (sourceAngularLpJet hf a b R,
      (smoothCollarTrace s b hf,smoothCollarTrace s (a*R+b) hf))∈cylinderSobolevGraph s R := by
  let q : TorusModes → smoothComplexAxis := fun h =>
    ⟨sourceAngularCoefficient f a b h,sourceAngularCoefficient_smooth hf a b h⟩
  apply cylinderGraph_of_smooth_coefficients s R _ q
    (sourceAngularLpJet_coefficient hf a b R) _ _
  · intro h
    rw [smoothCollarTrace_fst]
    simp [q,sourceAngularCoefficient]
  · intro h
    rw [smoothCollarTrace_fst]
    rfl

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma hasDerivAt_outer_of_strict_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {g : ℝ → ℝ} {x d : ℝ} {v : E}
    (hg : HasStrictDerivAt g d x) (hd : d≠0)
    (hF : HasDerivAt (F ∘ g) v x) : HasDerivAt F (d⁻¹ • v) (g x) := by
  let q := hg.localInverse g d x hd
  have hq : q (g x)=x := hg.eventually_left_inverse hd |>.self_of_nhds
  have h := hF.scomp_of_eq (g x) (hg.to_localInverse hd).hasDerivAt hq.symm
  apply h.congr_of_eventuallyEq
  filter_upwards [hg.eventually_right_inverse hd] with y hy
  exact congrArg F hy.symm

lemma hasStrictDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasStrictDerivAt (faceRayAngle w j) (faceRayDensity w j b) b :=
  hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Filter.Eventually.of_forall fun x => hasDerivAt_faceRayAngle w j x)
    (continuous_faceRayDensity w j).continuousAt

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

lemma torusDirectionalDerivative_of_face (F : UnitAddTorus (Fin 2) → ℂ)
    (θ : UnitAddTorus (Fin 2)) (k : Fin 2) {w : ℝ} (hw : 0<w)
    (i : Fin 4) (b : ℝ) (v : ℂ)
    (hF : HasDerivAt (fun u => F (θ+torusCoordinateShift k
      (faceRayAngle w i u-faceRayAngle w i b))) v b) :
    torusDirectionalDerivative F k θ=(faceRayDensity w i b)⁻¹ • v := by
  have h := hasDerivAt_outer_of_strict_comp (F:=fun t => F (θ+torusCoordinateShift k t))
    ((hasStrictDerivAt_faceRayAngle w i b).sub_const (faceRayAngle w i b))
    (faceRayDensity_pos' hw i b).ne' hF
  simpa only [sub_self,torusDirectionalDerivative_eq] using h.deriv

lemma hasDerivAt_coordinate_update (x : Fin 3 → ℝ) (k : Fin 3) :
    HasDerivAt (fun u => Function.update x k u) (Pi.single k 1) (x k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l=k
  · subst l
    simp only [Function.update_self,Pi.single_eq_same]
    exact hasDerivAt_id' (x k)
  · simpa [Function.update_of_ne hl,Pi.single_apply,hl] using hasDerivAt_const (x k) (x l)

lemma physicalTestCovector_update {f : (Fin 3 → ℝ) → ℝ} {point : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f point) (k : Fin 3) :
    HasDerivAt (fun u => f (Function.update point k u)) (physicalTestCovector f point k) (point k) := by
  simpa only [Function.update_eq_self,Function.comp_def,physicalTestCovector] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (point k) (hasDerivAt_coordinate_update point k)
      (Function.update_eq_self k point).symm

lemma sourceAngularTest_face0 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|≤1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity 1 i (x 1))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 1 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num) i (x 1)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 1).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 1), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h1
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 0 (faceRayAngle 1 i u-faceRayAngle 1 i (x 1))=
      ![((faceRayAngle 1 i u:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ hu.le h2]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularTest_face1 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|<1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity sourceRadialWidth j (x 2))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 2 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 2).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 2), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h2
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 1 (faceRayAngle sourceRadialWidth j u-faceRayAngle sourceRadialWidth j (x 2))=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j u:ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ h1 hu.le]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularAxial_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|≤1) :
    sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))=
      (a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0 : ℝ) := by
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 0).comp_of_eq t
      (((hasDerivAt_id t).const_mul a).add_const b) hx.symm
  have he : (fun u => f (sourceAngularCollar (a*u+b) (torusAngles (sourceFaceAngles i j x))))=
      (fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 (a*u+b))) := by
    funext u
    dsimp only [Function.comp_def]
    rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ h1 h2]
    congr 2
    ext k
    fin_cases k <;> simp
  unfold sourceAngularAxial
  rw [he]
  change ((deriv ((fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 u)) ∘
    (fun u => a*u+b)) t : ℝ) : ℂ)=_
  have hd' := hd.deriv
  simpa only [id_eq,mul_one,mul_comm] using congrArg Complex.ofReal hd'

theorem sourceAngularJet_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|<1) :
    (fun k : Fin 3 => (sourceAngularJet f a b k.succ
      (t,torusAngles (sourceFaceAngles i j x))).re)=
      ![a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0,
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1)),
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))] := by
  ext k
  fin_cases k
  · change (sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))).re=_
    exact congrArg Complex.re (sourceAngularAxial_face hf a b t i j hx h1.le h2.le)
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))
    rw [sourceAngularTest_face0 hf a b t i j hx h1 h2.le]
    rw [Complex.real_smul]
    norm_cast
    ring
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))
    rw [sourceAngularTest_face1 hf a b t i j hx h1.le h2]
    rw [Complex.real_smul]
    norm_cast
    ring

end ScalarConductivity

end
end

end OAI
