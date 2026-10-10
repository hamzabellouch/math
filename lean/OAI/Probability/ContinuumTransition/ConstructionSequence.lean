import OAI.Probability.ContinuumTransition.ConstructionStep

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure ConstructionData (p : ℝ) where
  t : ℝ
  τ : ℝ
  γ : ℝ
  τ_pos : 0 < τ
  τ_small : τ ≤ p/100
  γ_pos : 0 < γ
  cap : ConstructionCap t (firstMass p+1)
  geometry : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
    closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w)
  stages : ∀ n, ConstructionStage t p τ n
  ranges : ℕ → ℝ
  initial_zero : (stages 0).σ = fun _ => 0
  initial_mass : (stages 0).a = firstMass p
  transitions : ∀ n, StageTransition (stages n) (stages (n+1)) (ranges n)

lemma sequence_of_initial {t p τ γ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hτp : τ ≤ p/100)
    (hγ : 0 < γ) (hcap : ConstructionCap t (firstMass p+1))
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    (s₀ : ConstructionStage t p τ 0) (hzero : s₀.σ = fun _ => 0) (hfirst : s₀.a = firstMass p) :
    Nonempty (ConstructionData p) := by
  have hex := fun n (s : ConstructionStage t p τ n) => construction_step hp hτ hτp hγ hcap hgeom s
  let next := fun n (s : ConstructionStage t p τ n) => Classical.choose (hex n s)
  let length := fun n (s : ConstructionStage t p τ n) => Classical.choose (Classical.choose_spec (hex n s))
  have hn (n) (s : ConstructionStage t p τ n) : StageTransition s (next n s) (length n s) :=
    Classical.choose_spec (Classical.choose_spec (hex n s))
  let seq : ∀ n, ConstructionStage t p τ n := Nat.rec s₀ (fun n s => next n s)
  refine ⟨⟨t,τ,γ,hτ,hτp,hγ,hcap,hgeom,seq,(fun n => length n (seq n)),hzero,hfirst,?_⟩⟩
  intro n
  exact hn n (seq n)

lemma exists_constructionData : Nonempty (ConstructionData packingDensity) := by
  have hp := packingDensity_pos
  obtain ⟨τ₀,γ,hτ₀,hγ,hgeom₀⟩ := robust_vertex_triangle hp
  let τ := min τ₀ (packingDensity/100)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτp : τ ≤ packingDensity/100 := min_le_right _ _
  have hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex packingDensity i) ≤ τ) →
      closedBall (triangleCenter packingDensity) γ ⊆ convexHull ℝ (range w) :=
    fun w hw => hgeom₀ w (fun i => (hw i).trans (min_le_left _ _))
  have ha : 0 < firstMass packingDensity := firstMass_pos hp
  obtain ⟨T,hT⟩ := exists_constructionCap (show 0 < firstMass packingDensity+1 by linarith)
  obtain ⟨t,ht,x,hx,htr⟩ := physical_initial_triple hτ hγ (show (0:ℝ) < 1/64 by norm_num)
    (show (1:ℝ)/64 < 1/2 by norm_num) hT.t_large (hT.lt_gap (by linarith : firstMass packingDensity ≤ firstMass packingDensity+1))
    (hgeom (triangleVertex packingDensity) (fun _ => by simp only [dist_self]; exact hτ.le))
  let s₀ : ConstructionStage t packingDensity τ 0 := {
    σ := fun _ => 0, R := fun _ => 1, a := firstMass packingDensity, x := x,
    σ_nonneg := fun _ => le_refl _, R_one := fun _ => le_refl _, σ_summable := summable_zero,
    a_pos := ha, mass := by simp [geometricBudget],
    referenceBounded := ⟨1,by norm_num,fun _ _ => le_refl _⟩,
    location := by
      change dist x initialPoint < 1/64 at hx
      norm_num [locationRadius,geometricBudget]
      linarith,
    triple := by
      have he : groupRadius τ 0 = τ/2 := by norm_num [groupRadius,geometricBudget]; ring
      rw [he,physicalProfile_zero]
      exact htr }
  exact sequence_of_initial hp hτ hτp hγ (hT.mono_t ht) hgeom s₀ rfl rfl

end ContinuumTemperature
end
end

end OAI
