import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Matrices
import OAI.Analysis.TracialCohomology.PartialRepresentations
import OAI.Analysis.TracialCohomology.FreeSeparation

namespace OAI

/-! Matrix representations for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} {p : M} (s : System n p)

def permValue (σ : Equiv.Perm (Fin n)) : M := ∑ i, s.entry (σ i) i

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_one : permValue s 1=p := by
  exact s.sum_diag

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_mul (σ ρ : Equiv.Perm (Fin n)) :
    permValue s (σ*ρ)=permValue s σ*permValue s ρ := by
  classical
  simp [permValue,Finset.sum_mul,Finset.mul_sum,s.mul_entry,Equiv.Perm.mul_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_inv (σ : Equiv.Perm (Fin n)) :
    permValue s σ⁻¹=star (permValue s σ) := by
  classical
  simp only [permValue,star_sum,s.star_entry]
  have hh := Equiv.sum_comp σ (fun i => s.entry (σ⁻¹ i) i)
  simpa using hh.symm

def matrixRep {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin n)) : Rep G M where
  val g := permValue s (π g)
  mul g h := by rw [map_mul,permValue_mul]
  inv g := by rw [map_inv,permValue_inv]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma matrixRep_support {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin n)) :
    (matrixRep s π).support=p := by
  change permValue s (π 1)=p
  rw [map_one,permValue_one]

omit [StarOrderedRing M] in
lemma off_diagonal_trace (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    {i j : Fin n} (hij : i ≠ j) : τ (s.entry i j)=0 := by
  have hh := htr (s.entry i i) (s.entry i j)
  simpa [s.mul_entry,Ne.symm hij] using hh

omit [StarOrderedRing M] in
lemma matrixRep_trace_zero (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin n)) (g : G)
    (hg : ∀ i, π g i ≠ i) : τ (matrixRep s π g)=0 := by
  change τ (∑ i, s.entry (π g i) i)=0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i _ => off_diagonal_trace s τ htr (hg i))

universe u v
variable {A : Type u}

def regularPerm {H : Type u} [Group H] [Fintype H] (π : FreeGroup A →* H) :
    FreeGroup A →* Equiv.Perm (Fin (Fintype.card H)) where
  toFun g := (Fintype.equivFin H).symm.trans ((Equiv.mulLeft (π g)).trans (Fintype.equivFin H))
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp

lemma regularPerm_ne {H : Type u} [Group H] [Fintype H] (π : FreeGroup A →* H)
    (g : FreeGroup A) (hg : π g ≠ 1) (i : Fin (Fintype.card H)) : regularPerm π g i ≠ i := by
  intro hh
  have he := congrArg (Fintype.equivFin H).symm hh
  change (Fintype.equivFin H).symm ((Fintype.equivFin H) (π g*((Fintype.equivFin H).symm i)))=_ at he
  rw [Equiv.symm_apply_apply] at he
  exact hg ((mul_eq_right).mp he)

section Dual
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem finite_corner_rep (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (S : Finset (FreeGroup A)) :
    ∃ w : Rep (FreeGroup A) M, w.support=p ∧
      ∀ g ∈ S, g ≠ 1 → τ (w g)=0 := by
  classical
  obtain ⟨H,hG,hF,π,hπ⟩ := PopaFinite.exists_finite_separation S
  let := hG
  let := hF
  obtain ⟨s,hs⟩ := exists_system e τ hτ htr hfaith h1 hfactor hdiff
    (Fintype.card H) Fintype.card_pos hp
  refine ⟨matrixRep s (regularPerm π),matrixRep_support s _,fun g hg hg1 => ?_⟩
  exact matrixRep_trace_zero s τ htr _ g (regularPerm_ne π g (hπ g hg hg1))
end Dual
end PopaPatching

end

end OAI
