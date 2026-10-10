import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonFixedTrackProgress
import OAI.GroupTheory.SimpleAmenable.Homology.ConfigurationEquivariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationResolution
open Classical CategoryTheory Finsupp
namespace ConfigurationChains
variable {V : Type*} {R : V → V → Prop}

noncomputable def complex (R : V → V → Prop) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (degree R n))
    (fun n => ModuleCat.ofHom (degreeBoundary R n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact degreeBoundary_square R n c)

noncomputable def representation {G : Type*} [Monoid G] [MulAction G V]
    (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (n : ℕ) :
    Representation ℤ G (degree R n) where
  toFun g := degreePush (fun v => g • v) (hR g) n
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change push (fun v : V => (1:G) • v) c.val=c.val
    have he : (fun v : V => (1:G) • v)=id := funext (fun v => one_smul G v)
    rw [he]
    exact push_id c.val
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change push (fun v : V => (g*h) • v) c.val=push (fun v => g • v) (push (fun v => h • v) c.val)
    rw [push_comp]
    simp only [Function.comp_def, mul_smul]

@[simp] theorem representation_boundary {G : Type*} [Monoid G] [MulAction G V]
    (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (g : G) (n : ℕ)
    (c : degree R (n+1)) :
    representation hR n g (degreeBoundary R n c)=
      degreeBoundary R n (representation hR (n+1) g c) :=
  degreePush_boundary _ (hR g) n c

noncomputable def simplexModuleEquiv (R : V → V → Prop) (n : ℕ) :
    degree R n ≃ₗ[ℤ] ({l : List V // l.Pairwise R ∧ l.length=n} →₀ ℤ) := by
  have he : degree R n=Finsupp.supported ℤ ℤ {l : List V | l.Pairwise R ∧ l.length=n} := by
    ext c
    rw [Finsupp.mem_supported]
    rfl
  exact (LinearEquiv.ofEq _ _ he).trans (Finsupp.supportedEquivFinsupp _)

theorem lowDegree_exact
    (hc : ∀S : Finset V,S.card≤31 → ∃v,∀w∈S,R v w)
    {n : ℕ} (hn : n≤2) :
    Function.Exact (degreeBoundary R (n+1)) (degreeBoundary R n) := by
  intro c
  constructor
  · intro hz
    have hz' : boundary c.val=0 := congrArg Subtype.val hz
    obtain ⟨d,hd,he⟩ := low_degree_filling hc (by omega : n+1≤3) c.property hz'
    exact ⟨⟨d,hd⟩,Subtype.ext he⟩
  · rintro ⟨d,rfl⟩
    exact degreeBoundary_square R n d

end ConfigurationChains

namespace PolygonPlacement

noncomputable def configurationRepresentation (a m n : ℕ) :
    Representation ℤ (polygonFullGroup a m) (ConfigurationChains.degree (@Apart a m) n) :=
  ConfigurationChains.representation (fun g v w h => (apart_smul_iff g v w).mpr h) n
end PolygonPlacement
end ConfigurationResolution

end SimpleAmenable
end
end

end OAI
