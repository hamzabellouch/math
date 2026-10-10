import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density
import OAI.Probability.CriticalPercolation.Clusters.Earlier
import OAI.Probability.CriticalPercolation.Clusters.HitValue
import OAI.Probability.CriticalPercolation.GraphGeometry.HittingSubAvoidance

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_joint_gluing_strict (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  by_cases ho : o ∈ A
  · have hA (ω : Set E) : (component (G.openGraph ω) o ∩ A).Nonempty :=
      ⟨o, component_self _ _, ho⟩
    have hh : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
        (fun _ => (1 : ℝ)) := by
      funext ω
      exact ite_eq_left (hA ω)
    have hj : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
        (fun ω => hitValue T (component (G.openGraph ω) o)) := by
      funext ω
      exact jointHitValue_eq_hitValue (hA ω)
    erw [hh, hj, expect_const w hw, one_mul]
    exact ha o ho
  · let n := Fintype.card A
    let e : Fin n ≃ A := (Fintype.equivFin A).symm
    let f : Fin n → V := fun j => e j
    let x : Fin (n+1) → V := Fin.snoc f o
    have hx : Function.Injective x := by
      apply Fin.snoc_injective_iff.mpr
      refine ⟨?_, ?_⟩
      · exact Subtype.val_injective.comp e.injective
      · rintro ⟨j, hj⟩
        exact ho (hj ▸ (e j).property)
    have hlast : x (Fin.last n) = o := Fin.snoc_last _ _
    have hearlier : earlier x (Fin.last n) = A := by
      ext v
      constructor
      · rintro ⟨j, hj, h⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · have he : x i.castSucc = f i := Fin.snoc_castSucc _ _ _
          exact h ▸ he ▸ (e i).property
        · exact (lt_irrefl _ hj).elim
      · intro hv
        let i := e.symm ⟨v, hv⟩
        refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
        dsimp only [x]
        rw [Fin.snoc_castSucc]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
    have h := G.finite_joint_gluing_list w hw hpos hclosed x hx T a (by
      intro j
      simpa only [x, Fin.snoc_castSucc] using ha (f j) (e j).property)
    rwa [hearlier, hlast] at h

end CriticalPercolation.BondGraph

end
end

end OAI
