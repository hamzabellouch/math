import Mathlib
import OAI.Geometry.Cannon.Boundary.WordBall
import OAI.Geometry.Cannon.Actions.Height

namespace OAI

section
section
section
noncomputable section
section
namespace CannonTriples

open Set Metric

abbrev Triples (X : Type*) := {t : Fin 3 → X // Function.Injective t}

instance {X : Type*} [TopologicalSpace X] : TopologicalSpace (Triples X) :=
  inferInstanceAs (TopologicalSpace {t : Fin 3 → X // Function.Injective t})

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def separation (t : Fin 3 → X) : ℝ := min (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))

lemma separation_pos (t : Triples X) : 0 < separation t.val := by
  apply lt_min
  · exact dist_pos.mpr (fun hh => (by decide : (0:Fin 3) ≠ 1) (t.property hh))
  · apply lt_min
    · exact dist_pos.mpr (fun hh => (by decide : (0:Fin 3) ≠ 2) (t.property hh))
    · exact dist_pos.mpr (fun hh => (by decide : (1:Fin 3) ≠ 2) (t.property hh))

lemma separation_le (t : Fin 3 → X) (i j : Fin 3) (hij : i ≠ j) : separation t ≤ dist (t i) (t j) := by
  have h₀ := min_le_left (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  have h₁ := (min_le_right (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))).trans
    (min_le_left (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  have h₂ := (min_le_right (dist (t 0) (t 1)) (min (dist (t 0) (t 2)) (dist (t 1) (t 2)))).trans
    (min_le_right (dist (t 0) (t 2)) (dist (t 1) (t 2)))
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h₀
    | exact h₁
    | exact h₂
    | exact h₀.trans_eq (dist_comm _ _)
    | exact h₁.trans_eq (dist_comm _ _)
    | exact h₂.trans_eq (dist_comm _ _)

lemma injective_of_separation_pos {t : Fin 3 → X} (ht : 0 < separation t) : Function.Injective t := by
  intro i j he
  by_contra hn
  have hh := ht.trans_le (separation_le t i j hn)
  simp only [he,dist_self,lt_self_iff_false] at hh

lemma continuous_separation : Continuous (separation : (Fin 3 → X) → ℝ) := by
  unfold separation
  fun_prop

theorem compact_uniform_separation {K : Set (Triples X)} (hK : IsCompact K) :
    ∃ e : ℝ, 0 < e ∧ ∀ t ∈ K, e ≤ separation t.val := by
  by_cases hn : K.Nonempty
  · obtain ⟨t,_,hmin⟩ := hK.exists_isMinOn hn
      (continuous_separation.comp continuous_subtype_val).continuousOn
    exact ⟨separation t.val,separation_pos t,fun _ hu => hmin hu⟩
  · exact ⟨1,by norm_num,fun t ht => (hn ⟨t,ht⟩).elim⟩

theorem separated_compact [CompactSpace X] {e : ℝ} (he : 0 < e) :
    IsCompact {t : Triples X | e ≤ separation t.val} := by
  rw [Subtype.isCompact_iff]
  have him : Subtype.val '' {t : Triples X | e ≤ separation t.val} =
      {t : Fin 3 → X | e ≤ separation t} := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro ht
      exact ⟨⟨t,injective_of_separation_pos (he.trans_le ht)⟩,ht,rfl⟩
  rw [him]
  exact (isClosed_le continuous_const continuous_separation).isCompact

def map (f : X ≃ₜ Y) (t : Triples X) : Triples Y :=
  ⟨f ∘ t.val,f.injective.comp t.property⟩

lemma map_continuous (f : X ≃ₜ Y) : Continuous (map f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact f.continuous.comp ((continuous_apply i).comp continuous_subtype_val)

def homeomorph (f : X ≃ₜ Y) : Triples X ≃ₜ Triples Y where
  toFun := map f
  invFun := map f.symm
  left_inv t := by apply Subtype.ext; funext i; exact f.symm_apply_apply _
  right_inv t := by apply Subtype.ext; funext i; exact f.apply_symm_apply _
  continuous_toFun := map_continuous f
  continuous_invFun := map_continuous f.symm

end CannonTriples

end

namespace CannonRelease
open CannonGraph CannonVisual CannonTriples Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance triplesSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_triples_proper :
    let _ := visualMetricSpace D hδ
    ∀ K : Set (Triples (Boundary D)), IsCompact K →
      {g : G | ∃ t ∈ K, CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t ∈ K}.Finite := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro K hK
  by_cases hn : K.Nonempty
  · obtain ⟨t,_⟩ := hn
    obtain ⟨r,hr⟩ := Quotient.exists_rep (t.val 0)
    obtain ⟨s,hs⟩ := Quotient.exists_rep (t.val 1)
    have hrs : ¬ (raySetoid D).r r s := by
      intro hh
      have he : t.val 0 = t.val 1 := hr.symm.trans ((Quotient.sound hh).trans hs)
      exact (by decide : (0:Fin 3) ≠ 1) (t.property he)
    obtain ⟨e,he,hsep⟩ := compact_uniform_separation hK
    apply (finite_triple_translates D hδ r s hrs he).subset
    rintro g ⟨u,hu,hgu⟩
    have hh := hsep u hu
    have hhg := hsep _ hgu
    refine ⟨u.val 0,u.val 1,u.val 2,?_,?_,?_,?_,?_,?_⟩
    · exact hh.trans (separation_le _ 0 1 (by decide))
    · exact hh.trans (separation_le _ 0 2 (by decide))
    · exact hh.trans (separation_le _ 1 2 (by decide))
    · exact hhg.trans (separation_le _ 0 1 (by decide))
    · exact hhg.trans (separation_le _ 0 2 (by decide))
    · exact hhg.trans (separation_le _ 1 2 (by decide))
  · apply Set.finite_empty.subset
    rintro _ ⟨t,ht,_⟩
    exact (hn ⟨t,ht⟩).elim

theorem boundary_triples_normalize :
    let _ := visualMetricSpace D hδ
    ∃ e : ℝ, 0 < e ∧ ∀ t : Triples (Boundary D), ∃ g : G,
      e ≤ separation (CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t).val := by
  let _ := visualMetricSpace D hδ
  dsimp only
  let e := 1/(2*(8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*Real.exp (2*visualExponent δ))
  refine ⟨e,by dsimp [e]; positivity,?_⟩
  intro t
  have h01 : t.val 0 ≠ t.val 1 := fun h => (by decide : (0:Fin 3) ≠ 1) (t.property h)
  have h02 : t.val 0 ≠ t.val 2 := fun h => (by decide : (0:Fin 3) ≠ 2) (t.property h)
  have h12 : t.val 1 ≠ t.val 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (t.property h)
  by_cases hA : dist (t.val 0) (t.val 1) ≤ dist (t.val 0) (t.val 2)
  · by_cases hB : dist (t.val 0) (t.val 1) ≤ dist (t.val 1) (t.val 2)
    · obtain ⟨g,hg01,hg02,hg12⟩ := normalize_closest D hδ _ _ _ h01 hA hB
      exact ⟨g,le_min hg01 (le_min hg02 hg12)⟩
    · obtain ⟨g,hg12,hg10,hg20⟩ := normalize_closest D hδ _ _ _ h12
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hB))
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hB).trans hA)
      refine ⟨g,le_min ?_ (le_min ?_ hg12)⟩
      · exact hg10.trans_eq (dist_comm _ _)
      · exact hg20.trans_eq (dist_comm _ _)
  · by_cases hC : dist (t.val 0) (t.val 2) ≤ dist (t.val 1) (t.val 2)
    · obtain ⟨g,hg02,hg01,hg21⟩ := normalize_closest D hδ _ _ _ h02
        (le_of_not_ge hA) (by simpa only [boundaryDist,dist_comm] using hC)
      refine ⟨g,le_min hg01 (le_min hg02 ?_)⟩
      exact hg21.trans_eq (dist_comm _ _)
    · obtain ⟨g,hg12,hg10,hg20⟩ := normalize_closest D hδ _ _ _ h12
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hC).trans (le_of_not_ge hA))
        (by simpa only [boundaryDist,dist_comm] using (le_of_not_ge hC))
      refine ⟨g,le_min ?_ (le_min ?_ hg12)⟩
      · exact hg10.trans_eq (dist_comm _ _)
      · exact hg20.trans_eq (dist_comm _ _)

theorem boundary_triples_cocompact :
    let _ := visualMetricSpace D hδ
    ∃ K : Set (Triples (Boundary D)), IsCompact K ∧
      ∀ t : Triples (Boundary D), ∃ g : G, ∃ u ∈ K,
        CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) u = t := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨e,he,hsep⟩ := boundary_triples_normalize D hδ
  refine ⟨{t | e ≤ separation t.val},separated_compact he,?_⟩
  intro t
  obtain ⟨g,hg⟩ := hsep t
  refine ⟨g⁻¹,CannonTriples.map (boundaryHomeomorph D ⟨δ,hδ⟩ g) t,hg,?_⟩
  apply Subtype.ext
  funext i
  change boundaryTranslate D ⟨δ,hδ⟩ g⁻¹ (boundaryTranslate D ⟨δ,hδ⟩ g (t.val i)) = t.val i
  exact (boundaryHomeomorph D ⟨δ,hδ⟩ g).left_inv (t.val i)

end CannonRelease

end
end
end
end

end OAI
