import OAI.Algebra.AuslanderReiten.Cones.BimoduleTwoCone
import OAI.Algebra.AuslanderReiten.Homology.TNullhomotopy

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def barB (n : ℕ) : (Q₀).X n ⟶ (P₀).X (n+1) :=
  ModuleCat.ofHom (X := (Q₀).X n) (Y := (P₀).X (n+1)) (B q H (n+1))

def barG (n : ℕ) : (Q₀).X (n+1) ⟶ (P₀).X n :=
  ModuleCat.ofHom (X := (Q₀).X (n+1)) (Y := (P₀).X n) (G q H n)

def barDb : (Q₀).X 0 ⟶ (P₀).X 0 :=
  ModuleCat.ofHom (X := (Q₀).X 0) (Y := (P₀).X 0)
    ((B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0))

theorem barDb_cycle : (Q₀).d 1 0 ≫ barDb q H = 0 := by
  have hs : (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0).comp
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 1) = 0 := by
    apply LinearMap.ext
    intro x
    exact AbsoluteBar.boundary_squared k R 0 x
  rw [AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  change ((B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0)).comp
    (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 1) = 0
  rw [LinearMap.comp_assoc, hs, LinearMap.comp_zero]

theorem barB_bottom : barB q H 0 ≫ (P₀).d 1 0 = barDb q H := by
  rw [AbsoluteBar.complex_d]
  apply ModuleCat.hom_ext
  exact B_differential_zero q H

theorem barB_chain (n : ℕ) :
    barB q H (n+1) ≫ (P₀).d (n+2) (n+1) = (Q₀).d (n+1) n ≫ barB q H n := by
  simp only [AbsoluteBar.complex_d, AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (B_differential q H (n+1)) x
  exact add_right_cancel (hh.trans
    (SparseParity.module_add_self_eq_zero (k := k) (B q H (n+1)
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n+1) x))).symm)

theorem barG_equation (n : ℕ) :
    barB q H (n+2) ≫ barComparison q n =
      barG q H (n+1) ≫ (P₀).d (n+1) n + (Q₀).d (n+2) (n+1) ≫ barG q H n := by
  simp only [AbsoluteBar.complex_d, AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  exact G_equation q H n

end ArExplicit.T

end

end OAI
