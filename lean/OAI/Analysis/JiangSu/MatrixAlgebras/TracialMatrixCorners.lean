import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.TracialProjectionComparison
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixUnitsHom

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U

 theorem tracial_matrix_corner (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    (m : ℕ) (hm : 0 < m) {r : D} (hr : IsStarProjection r) :
    ∃ p : D, ∃ R : ProjectionRow (Fin m) p,R.sample p=r := by
  classical
  obtain ⟨p,hp,hortho,hsum,htr⟩ := comparison_relative_partition U hfree
    hsimple hinf hcmp hnuc {1} (Set.countable_singleton _) m hm hr
    (fun a ha => by simpa only [Set.mem_singleton_iff] using ha ▸ Commute.one_right r)
  let i₀ : Fin m := ⟨0,hm⟩
  have heq (i : Fin m) (s : ℕ → TracialState A) :
      ((L s).functional (p i₀)).re=((L s).functional (p i)).re := by
    have h0 := (htr i₀ 1 (Set.mem_singleton _)).2 s
    have hi := (htr i 1 (Set.mem_singleton _)).2 s
    simp only [mul_one] at h0 hi
    rw [h0,hi]
  choose v hv hvr using fun i => tracial_projection_equivalence U hfree
    hsimple hinf hcmp hnuc (hp i₀).1 (hp i).1 (heq i)
  have hright (i : Fin m) : star (v i)*p i=star (v i) :=
    partialIsometry_right_support (hp i).1 (by simpa only [star_star] using hvr i)
  have hleft (i : Fin m) : p i*v i=v i := by
    simpa only [star_mul,star_star,(hp i).1.isSelfAdjoint.star_eq] using congrArg star (hright i)
  let R : ProjectionRow (Fin m) (p i₀) := {
    projection := (hp i₀).1
    entry := v
    gram_diag := hv
    gram_offdiag := by
      intro i j hij
      calc
        star (v i)*v j=(star (v i)*p i)*(p j*v j) := by rw [hright,hleft]
        _ = star (v i)*(p i*p j)*v j := by noncomm_ring
        _ = 0 := by rw [hortho hij,mul_zero,zero_mul] }
  refine ⟨p i₀,R,?_⟩
  change (∑ i,v i*p i₀*star (v i))=r
  simp only [show ∀ i,v i*p i₀=v i from fun i => partialIsometry_right_support (hp i₀).1 (hv i),hvr]
  exact hsum

 theorem tracial_noncentral_matrix_hom (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    (m : ℕ) (hm : 0 < m) : Nonempty (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D) := by
  obtain ⟨p,R,hR⟩ := tracial_matrix_corner U hfree hsimple hinf hcmp hnuc m hm (IsStarProjection.one D)
  let E : ConcreteMatrixUnits.System (Fin m) D := {
    entry := R.coeff p
    mul_entry := by
      intro i j k l
      rw [R.coeff_mul p p R.projection.isIdempotentElem.eq,R.projection.isIdempotentElem.eq]
    star_entry := by intro i j; rw [R.coeff_star,R.projection.isSelfAdjoint.star_eq]
    sum_diag := hR }
  exact ⟨E.hom⟩

end DirectComparison

end
end

end OAI
