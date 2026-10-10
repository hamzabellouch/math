import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeanSubgroup
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Finite.Lattice

namespace OAI

/-!
# Coarse equivalences of discrete groups

Finite subsets are the bounded sets in a word metric on a finitely generated
group. Controlling all finite sets of differences is the metric-free form of
being bornologous. For finitely generated groups, a coarse equivalence in this
sense is a quasi-isometry. It also matches the coarse-equivalence formulation
of Li's finiteness and duality theorems.
-/

namespace PolycyclicRecognition

open scoped Pointwise

variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- Uniform control of bounded differences, for the discrete group coarse structure. -/
def GroupBornologous (f : G → H) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set H, T.Finite ∧
    ∀ x y, x⁻¹ * y ∈ S → (f x)⁻¹ * f y ∈ T

theorem groupBornologous_hom (f : G →* H) : GroupBornologous f := by
  intro S hS
  refine ⟨f '' S, hS.image f, fun x y hxy => ?_⟩
  exact ⟨x⁻¹ * y, hxy, by simp⟩

theorem GroupBornologous.comp {f : G → H} {g : H → J}
    (hg : GroupBornologous g) (hf : GroupBornologous f) :
    GroupBornologous (g ∘ f) := by
  intro S hS
  obtain ⟨T, hT, hfT⟩ := hf S hS
  obtain ⟨U, hU, hgU⟩ := hg T hT
  exact ⟨U, hU, fun x y hxy => hgU (f x) (f y) (hfT x y hxy)⟩

/-- Coarse inverse maps with uniformly bounded errors, measured by finite
sets of group differences. -/
structure GroupCoarseEquivalence (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  invFun : H → G
  bornologous_toFun : GroupBornologous toFun
  bornologous_invFun : GroupBornologous invFun
  left_error : (Set.range fun x => x⁻¹ * invFun (toFun x)).Finite
  right_error : (Set.range fun y => y⁻¹ * toFun (invFun y)).Finite

namespace GroupCoarseEquivalence

/-- Coarse inverses force finite fibers; this is the properness condition in
the discrete-group definition of a coarse map. -/
theorem finite_fiber (e : GroupCoarseEquivalence G H) (y : H) :
    (e.toFun ⁻¹' {y}).Finite := by
  apply (e.left_error.image (fun a => e.invFun y * a⁻¹)).subset
  intro x hx
  have hxy : e.toFun x = y := hx
  refine ⟨x⁻¹ * e.invFun y, ?_, ?_⟩
  · exact ⟨x, by dsimp only; rw [hxy]⟩
  · simp

def symm (e : GroupCoarseEquivalence G H) : GroupCoarseEquivalence H G where
  toFun := e.invFun
  invFun := e.toFun
  bornologous_toFun := e.bornologous_invFun
  bornologous_invFun := e.bornologous_toFun
  left_error := e.right_error
  right_error := e.left_error

omit [Group J] in
private theorem composite_error (f : G → H) (g : H → G) (f' : H → J) (g' : J → H)
    (hg : GroupBornologous g)
    (h : (Set.range fun x => x⁻¹ * g (f x)).Finite)
    (h' : (Set.range fun y => y⁻¹ * g' (f' y)).Finite) :
    (Set.range fun x => x⁻¹ * g (g' (f' (f x)))).Finite := by
  obtain ⟨T, hT, hgT⟩ := hg _ h'
  apply (h.mul hT).subset
  rintro _ ⟨x, rfl⟩
  refine ⟨x⁻¹ * g (f x), ⟨x, rfl⟩,
    (g (f x))⁻¹ * g (g' (f' (f x))), ?_, ?_⟩
  · exact hgT (f x) (g' (f' (f x))) ⟨f x, rfl⟩
  · simp [mul_assoc]

def trans (e : GroupCoarseEquivalence G H) (e' : GroupCoarseEquivalence H J) :
    GroupCoarseEquivalence G J where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  bornologous_toFun := e'.bornologous_toFun.comp e.bornologous_toFun
  bornologous_invFun := e.bornologous_invFun.comp e'.bornologous_invFun
  left_error := composite_error e.toFun e.invFun e'.toFun e'.invFun
    e.bornologous_invFun e.left_error e'.left_error
  right_error := composite_error e'.invFun e'.toFun e.invFun e.toFun
    e'.bornologous_toFun e'.right_error e.right_error

end GroupCoarseEquivalence

theorem finite_rightCosetRepresentatives (K : Subgroup G) [K.FiniteIndex] :
    (Set.range (rightCosetRepresentative K)).Finite := by
  have : Finite (Quotient (QuotientGroup.rightRel K)) :=
    Finite.of_equiv (G ⧸ K) (QuotientGroup.quotientRightRelEquivQuotientLeftRel K).symm
  apply (Set.finite_range (fun q : Quotient (QuotientGroup.rightRel K) => q.out)).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨Quotient.mk'' g, rfl⟩

theorem groupBornologous_subgroupCoordinate (K : Subgroup G) [K.FiniteIndex] :
    GroupBornologous (subgroupCoordinate K) := by
  intro S hS
  let R := Set.range (rightCosetRepresentative K)
  have hR : R.Finite := finite_rightCosetRepresentatives K
  let T := R * S * R⁻¹
  have hT : T.Finite := (hR.mul hS).mul hR.inv
  refine ⟨K.subtype ⁻¹' T, hT.preimage (fun _ _ _ _ h => Subtype.val_injective h), ?_⟩
  intro x y hxy
  change ((subgroupCoordinate K x : G))⁻¹ * (subgroupCoordinate K y : G) ∈ T
  have heq : ((subgroupCoordinate K x : G))⁻¹ * (subgroupCoordinate K y : G) =
      rightCosetRepresentative K x * (x⁻¹ * y) * (rightCosetRepresentative K y)⁻¹ := by
    simp [subgroupCoordinate, mul_assoc]
  rw [heq]
  refine ⟨_, ⟨_, ⟨x, rfl⟩, _, hxy, rfl⟩, _, ?_, rfl⟩
  simpa only [Set.mem_inv, inv_inv] using
    (show rightCosetRepresentative K y ∈ R from ⟨y, rfl⟩)

/-- Finite-index subgroups are coarsely equivalent to their ambient groups.
The coordinate map uses a finite right-coset transversal. -/
noncomputable def finiteIndexCoarseEquivalence (K : Subgroup G) [K.FiniteIndex] :
    GroupCoarseEquivalence K G where
  toFun := K.subtype
  invFun := subgroupCoordinate K
  bornologous_toFun := groupBornologous_hom K.subtype
  bornologous_invFun := groupBornologous_subgroupCoordinate K
  left_error := by
    let R := Set.range (rightCosetRepresentative K)
    have hR : R.Finite := finite_rightCosetRepresentatives K
    apply (hR.inv.preimage (fun _ _ _ _ h => Subtype.val_injective h)).subset
    rintro _ ⟨x, rfl⟩
    change (x : G)⁻¹ * ((x : G) * (rightCosetRepresentative K x)⁻¹) ∈ R⁻¹
    simpa only [inv_mul_cancel_left, Set.mem_inv, inv_inv] using
      (show rightCosetRepresentative K x ∈ R from ⟨x, rfl⟩)
  right_error := by
    apply (finite_rightCosetRepresentatives K).inv.subset
    rintro _ ⟨y, rfl⟩
    change y⁻¹ * (y * (rightCosetRepresentative K y)⁻¹) ∈ _
    simpa only [inv_mul_cancel_left, Set.mem_inv, inv_inv] using
      (show rightCosetRepresentative K y ∈ Set.range (rightCosetRepresentative K)
        from ⟨y, rfl⟩)

end PolycyclicRecognition

end OAI
