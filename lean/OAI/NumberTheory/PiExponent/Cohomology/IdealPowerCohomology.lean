import OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections
import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem ext_eq_zero_of_isZero (A M : X.Modules) (hM : IsZero M) (q : ℕ)
    (x : Abelian.Ext.{1} A M q) : x = 0 := by
  have hz := (extFunctorObj A q).map_isZero hM
  exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hz) x 0

theorem powerModule_twist_ext_zero_of_layers (I : X.IdealSheafData) (L : LineBundle X)
    (N n q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q) : x = 0 := by
  have hzero : ∀ k ≤ N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q, x = 0 := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      exact ext_eq_zero_of_isZero _ _ ((moduleTwistFunctor L n).map_isZero hN) q
    | @of_succ k hk ih =>
      intro x
      let S := (powerSequence I k).map (moduleTwistFunctor L n)
      have hS : S.ShortExact := moduleTwistFunctor_shortExact L n _ (powerSequence_shortExact I k)
      obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS x
        (hLayer k hk _)
      have hiy : y = 0 := ih y
      exact hy.symm.trans
        ((congrArg (fun z : Abelian.Ext.{1} (structureSheaf X) S.X₁ q =>
          z.comp (Ext.mk₀ S.f) (add_zero q)) hiy).trans
            (Ext.zero_comp (structureSheaf X) q (Ext.mk₀ S.f) q (add_zero q)))
  exact hzero k hk x

theorem powerModule_ext_zero_of_layers (I : X.IdealSheafData)
    (N q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X) (closedModule (I^k)) q) : x = 0 := by
  let L : LineBundle X := {
    sheaf := structureSheaf X
    locallyRankOne := fun x => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩ }
  exact powerModule_twist_ext_zero_of_layers I L N 0 q hN hLayer k hk x

attribute [local irreducible] closedModule moduleTwistFunctor powerLayer

theorem eventual_ideal_twist_vanishing_of_layers [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (L : LineBundle X)
    (hLayer : ∀ k, ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  classical
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  choose B hB using hLayer
  refine ⟨(Finset.range N).sup B, fun n hn q hq x => ?_⟩
  have hL (k : ℕ) (hk : k < N) := hB k n
    ((Finset.le_sup (Finset.mem_range.mpr hk)).trans hn) q hq
  have h := powerModule_twist_ext_zero_of_layers I L N n q hN hL 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule I)) q, z = 0 := by
    exact (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule J)) q, z = 0) (pow_one I)).mp h
  exact h' x
end
end PiExponentSeshadri.IdealModule

end OAI
