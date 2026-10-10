import OAI.Analysis.SphereIsometry.UltraSphere
import OAI.Analysis.SphereIsometry.DefectSequence
import OAI.Analysis.SphereIsometry.SphereCompletion

namespace OAI

/-!
# Positive maximal defect is attained on actual completed ultranorm spaces

The final spaces, sphere isometry, inverse, and bound are all constructed. The
orientation disjunction keeps the same original maximal absolute defect.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Nontrivial Y]

/-- The actual coordinatewise sphere equivalence followed by ambient completion. -/
def completedUltraSphereEquiv (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    UnitSphere (UltraCompletion U X) ≃ᵢ UnitSphere (UltraCompletion U Y) :=
  completedSphereEquiv (ultraSphereEquiv U f)

@[simp] theorem completedUltraSphereEquiv_symm (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    (completedUltraSphereEquiv U f).symm = completedUltraSphereEquiv U f.symm := by
  simp only [completedUltraSphereEquiv, completedSphereEquiv_symm, ultraSphereEquiv_symm]

/-- Exact fixed-radius formula on the canonical embedded unit classes. -/
theorem signedDefect_completedUltraSphereEquiv (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ) (s t : ℕ → UnitSphere X) :
    signedDefect (completedUltraSphereEquiv U f) q
      (sphereCoe (UltraQuotient U X) (unitClass U s))
      (sphereCoe (UltraQuotient U X) (unitClass U t)) =
        realULim U (fun n => signedDefect f q (s n) (t n)) := by
  exact (signedDefect_completedSphereEquiv_coe (ultraSphereEquiv U f) q
    (unitClass U s) (unitClass U t)).trans (signedDefect_ultraSphereEquiv U f q s t)

theorem HasDefectBound.completedUltraSphereEquiv
    {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ} (h : HasDefectBound f M)
    (U : Ultrafilter ℕ) : HasDefectBound (completedUltraSphereEquiv U f) M :=
  (h.ultraSphereEquiv U).completedSphereEquiv

/-- Positive original maximal absolute defect is attained, with the same global
bound, in one orientation on explicitly constructed nonzero real Banach spaces. -/
theorem positive_maxDefect_attained_or_inverse
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (hM : 0 < maxDefect f) :
    let F := completedUltraSphereEquiv freeUltrafilter f
    HasDefectBound F (maxDefect f) ∧
    HasDefectBound F.symm (maxDefect f) ∧
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((∃ x y : UnitSphere (UltraCompletion freeUltrafilter X),
          signedDefect F t x y = maxDefect f) ∨
       (∃ x y : UnitSphere (UltraCompletion freeUltrafilter Y),
          signedDefect F.symm t x y = maxDefect f)) := by
  have hbound := (hasDefectBound_maxDefect f).completedUltraSphereEquiv freeUltrafilter
  refine ⟨hbound, hbound.symm, ?_⟩
  obtain ⟨t, ht, hseq | hseq⟩ := exists_fixed_radius_defect_sequence f hM
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inl ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim
  · obtain ⟨s, r, hlim⟩ := hseq
    refine ⟨t, ht, Or.inr ⟨sphereCoe _ (unitClass freeUltrafilter s),
      sphereCoe _ (unitClass freeUltrafilter r), ?_⟩⟩
    rw [completedUltraSphereEquiv_symm, signedDefect_completedUltraSphereEquiv]
    exact realULim_eq_of_tendsto freeUltrafilter hlim

end Tingley

end

end OAI
