import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorInclusion
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder

namespace OAI


                                    
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

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

lemma affineCoefficient_map {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) (a : M ⟶ N) :
    affineCoefficient U f (s ≫ a) =
      affineCoefficient U e s * affineMapCoefficient U e f a := by
  unfold affineCoefficient affineMapCoefficient
  rw [← map_mul]
  congr 1
  rw [show restrictSection U.1.ι (s ≫ a) = restrictSection U.1.ι s ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map a by
        exact (congrArg (fun morphism =>
          (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫ morphism)
          ((Scheme.Modules.restrictFunctor U.1.ι).map_comp s a)).trans
          (Category.assoc _ _ _).symm]
  exact coefficient_postcompose e f _ _

lemma idealPowerInclusion_ideal (J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (n : ℕ) :
    Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)} =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  let unitFrame : (O X).restrict U.1.ι ≅ O U.1.toScheme :=
    Scheme.Modules.restrictUnitIso U.1.ι
  change Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
    unitFrame (idealPowerInclusion J ι n)} = (Ideal.span {affineMapCoefficient U e unitFrame ι})^n
  induction n with
  | zero =>
    change Ideal.span {affineMapCoefficient U unitFrame unitFrame (𝟙 (O X))} = _
    have hidentity : affineMapCoefficient U unitFrame unitFrame (𝟙 (O X)) = 1 := by
      let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
        Scheme.Modules.restrictFunctor U.1.ι
      change U.1.topIso.hom (endValue
        (unitFrame.inv ≫ restrictionFunctor.map (𝟙 (O X)) ≫ unitFrame.hom)) = 1
      rw [restrictionFunctor.map_id, Category.id_comp, unitFrame.inv_hom_id,
        endValue_id, map_one]
    rw [hidentity, Ideal.span_singleton_one, pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    change Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      unitFrame (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)} = _
    rw [affineMapCoefficient_comp U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) unitFrame (tensorInclusion J (J.pow n) ι)
      (idealPowerInclusion J ι n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι)} =
      Ideal.span {affineMapCoefficient U e unitFrame ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

lemma affineCoefficient_map_order {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) (a : M ⟶ N)
    (I : Ideal Γ(X,U.1)) (u v : ℕ)
    (hs : affineCoefficient U e s ∈ I^u)
    (ha : Ideal.span {affineMapCoefficient U e f a} ≤ I^v) :
    affineCoefficient U f (s ≫ a) ∈ I^(u+v) := by
  rw [affineCoefficient_map U e, pow_add]
  exact Ideal.mul_mem_mul hs (ha (Ideal.subset_span (Set.mem_singleton _)))

end
end MaximalSeshadri.Geometry

end

end OAI
