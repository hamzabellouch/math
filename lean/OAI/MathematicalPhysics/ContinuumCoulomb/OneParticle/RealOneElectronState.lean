import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalH1
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronCoordinates

namespace OAI

/-! Real spatial functions embedded into the full spinful one-electron
weak-H1 space. This transfers nuclear form estimates to orbital products. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem real_one_electron_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    fderiv ℝ (fun y : Configuration 1 => (f (oneElectronCoordinates y) : ℂ)) x
        (EuclideanSpace.single a 1) =
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hf.differentiable (by norm_num) _).hasFDerivAt.comp x oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt)
  have hn : oneElectronCoordinates (EuclideanSpace.single a 1) = EuclideanSpace.single a.2 1 := by
    rcases a with ⟨a,b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact oneElectronCoordinates_single b
  have h := congrArg (fun L : Configuration 1 →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hd.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,hn] using h

def realOneElectronState (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) : Coulomb.H1Vector 1 :=
  classicalH1State (fun _ x => (f (oneElectronCoordinates x) : ℂ))
    (fun _ => Complex.ofRealCLM.contDiff.comp (hf.comp oneElectronCoordinates.contDiff))
    (fun _ => (hL2.comp_measurePreserving oneElectronCoordinates.measurePreserving).ofReal)
    (fun _ a => by
      have hm : MemLp (fun x : Configuration 1 =>
          (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ)) 2 :=
        ((hd (EuclideanSpace.single a.2 1)).comp_measurePreserving
        oneElectronCoordinates.measurePreserving).ofReal
      simpa only [real_one_electron_partial hf] using hm)

theorem realOneElectronState_value (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hL2 : MemLp f 2) (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2)
    (s : SpinConfiguration 1) (x : Configuration 1) :
    (realOneElectronState f hf hL2 hd).value s x = (f (oneElectronCoordinates x) : ℂ) := rfl

theorem realOneElectronState_gradient (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hL2 : MemLp f 2) (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) (x : Configuration 1) :
    (realOneElectronState f hf hL2 hd).gradient s a x =
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single a.2 1) : ℂ) :=
  real_one_electron_partial hf a x

theorem real_nuclear_integrable_transfer (F : Position → ℝ)
    (hI : ∀ w : Coulomb.H1Vector 1, ∀ s : SpinConfiguration 1,
      Integrable (fun x => |F (Coulomb.position x 0)| * ‖w.value s x‖^2))
    (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) :
    Integrable (fun y => |F y| * f y^2) := by
  have h := hI (realOneElectronState f hf hL2 hd) (fun _ => 0)
  simp only [realOneElectronState_value,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    ← oneElectronCoordinates_apply] at h
  exact (oneElectronCoordinates.measurePreserving.integrable_comp_emb
    oneElectronCoordinates.toHomeomorph.measurableEmbedding).mp h

theorem real_nuclear_form_transfer (F : Position → ℝ) (B : ℝ)
    (hbound : ∀ w : Coulomb.H1Vector 1, ∀ s : SpinConfiguration 1,
      (∫ x, |F (Coulomb.position x 0)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (0,k) x‖^2))
    (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2)
    (hd : ∀ e : Position, MemLp (fun x => fderiv ℝ f x e) 2) :
    (∫ y, |F y| *f y^2) ≤ B*((∫ y, f y^2)+
      ∑ k : Fin 3, ∫ y, (fderiv ℝ f y (EuclideanSpace.single k 1))^2) := by
  have h := hbound (realOneElectronState f hf hL2 hd) (fun _ => 0)
  simp only [realOneElectronState_value,realOneElectronState_gradient,Complex.norm_real,
    Real.norm_eq_abs,sq_abs] at h
  have hp (x : Configuration 1) : Coulomb.position x 0 = oneElectronCoordinates x := rfl
  simp_rw [hp] at h
  have hF : (∫ x : Configuration 1, |F (oneElectronCoordinates x)| * f (oneElectronCoordinates x)^2) =
      ∫ y, |F y| * f y^2 := oneElectronCoordinates_integral (fun y => |F y| * f y^2)
  have hM : (∫ x : Configuration 1, f (oneElectronCoordinates x)^2) = ∫ y, f y^2 :=
    oneElectronCoordinates_integral (fun y => f y^2)
  have hD (k : Fin 3) : (∫ x : Configuration 1,
      (fderiv ℝ f (oneElectronCoordinates x) (EuclideanSpace.single k 1))^2) =
      ∫ y, (fderiv ℝ f y (EuclideanSpace.single k 1))^2 :=
    oneElectronCoordinates_integral (fun y => (fderiv ℝ f y (EuclideanSpace.single k 1))^2)
  rw [hF,hM] at h
  simp_rw [hD] at h
  exact h

end ContinuumCoulomb

end

end OAI
