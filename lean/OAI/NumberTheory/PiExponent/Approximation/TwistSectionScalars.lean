import OAI.NumberTheory.PiExponent.Approximation.TensorPure
import OAI.NumberTheory.PiExponent.Approximation.TwistSections

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleSectionMultiplyRight_pure (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens) (m : Γ(M,U)) :
    (moduleSectionMultiplyRight M s).app U m =
      pure M L U m (s.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorRightUnit M).hom.app U
      (pure M (structureSheaf X) U m (1 : Γ(X,U))) = m := by
    erw [right_unit_pure, one_smul]
  have hi : (moduleTensorRightUnit M).inv.app U m =
      pure M (structureSheaf X) U m (1 : Γ(X,U)) := by
    calc
      _ = (moduleTensorRightUnit M).inv.app U
          ((moduleTensorRightUnit M).hom.app U
            (pure M (structureSheaf X) U m (1 : Γ(X,U)))) := congrArg _ h.symm
      _ = _ := congrArg (fun q => q.app U
        (pure M (structureSheaf X) U m (1 : Γ(X,U)))) (moduleTensorRightUnit M).hom_inv_id
  change (moduleTensorMap (𝟙 M) s).app U ((moduleTensorRightUnit M).inv.app U m) = _
  erw [hi, TensorPure.map_pure]
  rfl

lemma moduleTensorFrame_pure (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) (U : X.Opens) (m : Γ(M,U)) (l : Γ(L,U)) :
    (moduleTensorFrame M e).hom.app U (pure M L U m l) =
      (show Γ(X,U) from e.hom.app U l) • m := by
  change (moduleTensorRightUnit M).hom.app U
    ((moduleTensorMap (𝟙 M) e.hom).app U (pure M L U m l)) = _
  have h := TensorPure.map_pure (𝟙 M) e.hom U m l
  exact (congrArg (fun t => (moduleTensorRightUnit M).hom.app U t) h).trans
    (right_unit_pure M U m (e.hom.app U l))

lemma moduleSectionMultiplyRight_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (e : L ≅ structureSheaf X)
    (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorFrame M e).hom.app U ((moduleSectionMultiplyRight M s).app U m) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (coefficient e s) • m := by
  rw [moduleSectionMultiplyRight_pure, moduleTensorFrame_pure]
  exact congrArg (fun a : Γ(X,U) => a • m) (end_naturality (s ≫ e.hom) U)

lemma moduleSectionMultiplyRight_restrict_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) (V : U.toScheme.Opens)
    (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTensorRestrictFrame U L e).app M).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m) =
      U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (coefficient e (restrictSection U.ι s)) •
        (show Γ(M.restrict U.ι,V) from m) := by
  change (moduleTensorFrame (M.restrict U.ι) e).hom.app V
    ((moduleTensorRestrict U M L).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m)) = _
  have h₁ := moduleSectionMultiplyRight_pure M s (U.ι ''ᵁ V) m
  have h₂ := restrict_pure U M L V m (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  have h₃ := moduleTensorFrame_pure (M.restrict U.ι) e V m
    (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  refine ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V
      ((moduleTensorRestrict U M L).hom.app V t)) h₁).trans
    ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V t) h₂).trans h₃)).trans ?_
  have h := end_naturality (restrictSection U.ι s ≫ e.hom) V
  apply congrArg (fun a : Γ(U.toScheme,V) => a • (show Γ(M.restrict U.ι,V) from m))
  calc
    _ = (show Γ(U.toScheme,V) from e.hom.app V ((restrictSection U.ι s).app V
        (1 : Γ(U.toScheme,V)))) := by
      change e.hom.app V (s.app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) =
        e.hom.app V (s.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))))
      rw [show (U.ι.appIso V).inv (1 : Γ(U.toScheme,V)) =
        (1 : Γ(X,U.ι ''ᵁ V)) from (U.ι.appIso V).inv.hom.map_one]
    _ = _ := h

lemma moduleTwistForward_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n k : ℕ)
    (m : Γ((moduleTwistFunctor L n).obj M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ k •
          ((moduleTwistRestrictFrame L U e n).app M).hom.app V m := by
  induction k with
  | zero => simp only [moduleTwistForward, NatTrans.id_app, pow_zero, one_smul]; rfl
  | succ k ih =>
    change ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L (n+k)).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L (n+k)).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

lemma moduleTwistSection_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n : ℕ) (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ n •
          (show Γ(M.restrict U.ι,V) from m) := by
  induction n with
  | zero =>
      simp only [moduleTwistSection, moduleTwistRestrictFrame, NatTrans.id_app, pow_zero]
      exact (one_smul Γ(U.toScheme, V) (show Γ(M.restrict U.ι, V) from m)).symm
  | succ n ih =>
    change ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
