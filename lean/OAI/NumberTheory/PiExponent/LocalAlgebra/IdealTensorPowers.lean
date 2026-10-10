import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal
import OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def idealPowerInclusion (J : LineBundle X) (ι : J.sheaf ⟶ O X) :
    ∀ n : ℕ, (J.pow n).sheaf ⟶ O X
  | 0 => 𝟙 _
  | n+1 => tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n

lemma idealPowerInclusion_mono (J : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι]
    (n : ℕ) : Mono (idealPowerInclusion J ι n) := by
  induction n with
  | zero => change Mono (𝟙 (O X)); infer_instance
  | succ n ih =>
    let := ih
    let := tensorInclusion_mono J (J.pow n) ι
    change Mono (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)
    infer_instance

def idealPowerFrame (J : LineBundle X) (U : X.Opens)
    (e : J.sheaf.restrict U.ι ≅ O U.toScheme) :
    ∀ n : ℕ, (J.pow n).sheaf.restrict U.ι ≅ O U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n+1 => tensorFrame J (J.pow n) U e (idealPowerFrame J U e n)

def affineMapCoefficient {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) : Γ(X,U.1) :=
  U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a ≫ f.hom))

lemma affineMapCoefficient_comp {M N P : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme)
    (g : P.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) (b : N ⟶ P) :
    affineMapCoefficient U e g (a ≫ b) =
      affineMapCoefficient U e f a * affineMapCoefficient U f g b := by
  unfold affineMapCoefficient
  rw [← map_mul,← endValue_comp]
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]

private lemma affineMapCoefficient_id {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    affineMapCoefficient U e e (𝟙 M) = 1 := by
  simp only [affineMapCoefficient]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, endValue_id, map_one]

lemma idealPowerInclusion_ideal (J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (n : ℕ) :
    Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)} =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  induction n with
  | zero =>
    simp only [idealPowerFrame, idealPowerInclusion]
    exact (congrArg (fun r : Γ(X,U.1) => Ideal.span {r})
      (affineMapCoefficient_id U (Scheme.Modules.restrictUnitIso U.1.ι))).trans (by simp)
  | succ n ih =>
    change Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)} = _
    erw [affineMapCoefficient_comp U _ (idealPowerFrame J U.1 e n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι)} =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
