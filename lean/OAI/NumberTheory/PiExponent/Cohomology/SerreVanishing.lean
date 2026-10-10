import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

namespace OAI

namespace PiExponent.SerreVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

private abbrev schemeUnit (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

theorem ext_eq_zero_of_affine_cover (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : l ≤ q)
    (x : Abelian.Ext.{u+1} (C := X.Modules) (schemeUnit X) M q) : x = 0 := by
  cases l with
  | zero => exact False.elim (Nat.not_lt_zero 0 hl)
  | succ l =>
      have he : l + (q - (l + 1)) + 1 = q := by omega
      revert x
      clear hq
      rw [← he]
      exact PiExponentSeshadri.FiniteCoverCohomology.cover_ext_zero
        l U hU hcover M _

end

end PiExponent.SerreVanishing

end OAI
