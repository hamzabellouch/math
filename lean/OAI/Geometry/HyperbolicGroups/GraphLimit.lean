import Mathlib
import OAI.Geometry.HyperbolicGroups.OrbitLimit
import OAI.Geometry.HyperbolicGroups.GraphAction
import OAI.Geometry.HyperbolicGroups.GraphSquares

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate OrbitLimit
universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)

/-- The actual graph-valued orbit array, uniformly bounded using the fixed
finite route to each vertex. -/
def array (v : Vertex) : OrbitLimit.Array (Ω := Ω) O where
  val n m := A n ((g n m).val v) (O n).base
  bound := by
    refine ⟨(route v).length * M, mul_nonneg (by positivity) hM, fun n m => ?_⟩
    rw [(g n m).route v]
    exact Path.bound (A n) (O n).base _ _
      (fun i => by rw [hact]; exact (O n).bound i) _

variable (S : SamplingSequence Field Admissible L Ω label)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

abbrev limit (v : Vertex) : OrbitLimit.Space (Ω := Ω) O U :=
  OrbitLimit.point O U (array O A letter hact g hM v)

include S hU in
lemma side {a b : Vertex} (s : Step a b) :
    dist (limit (U := U) O A letter hact g hM a) (limit (U := U) O A letter hact g hM b) ^ 2 = 1 := by
  apply S.limit_edge O hU _ _ s.field (fun n => Equiv.refl (L n)) hM
  intro n m
  change dist (A n ((g n m).val a) (O n).base) (A n ((g n m).val b) (O n).base) = _
  rw [(g n m).orbit_path (A n) (O n).base (.cons s (.nil _))]
  simp only [Path.eval, mul_one, Equiv.refl_apply]
  cases hs : s.forward
  · simp only [Step.value, hs, Bool.false_eq_true, ↓reduceIte,
      IsometricAction.displacement_inv, hact]
  · simp only [Step.value, hs, ↓reduceIte, hact]

include S hU hinv in
lemma path_lower {a b : Vertex} (p : Path a b) (hp : p.fields.Nodup)
    (hadm : Admissible p.fields.toFinset) :
    (p.length : ℝ) ≤ dist (limit (U := U) O A letter hact g hM a) (limit (U := U) O A letter hact g hM b) ^ 2 := by
  obtain ⟨σ,hσ⟩ := p.exists_compatible hp
  rw [← p.fields_length]
  apply S.limit_path O hU A letter hact admissible_down _ _
    (fun n => Path.read (inv n) σ) hM p.fields hp hadm
  intro n m
  change dist (A n ((g n m).val a) (O n).base) (A n ((g n m).val b) (O n).base) = _
  rw [(g n m).orbit_path (A n) (O n).base p]
  have he := p.eval_word hσ (label n m) (letter n) (inv n) (hinv n)
  simp only [he, OrbitWord.word]

include S hU hinv in
lemma square_twoStep (τ : TwoPath) :
    dist (limit (U := U) O A letter hact g hM (.inl (left τ)))
      (limit (U := U) O A letter hact g hM (.inl (right τ))) ^ 2 = 2 := by
  let a := limit (U := U) O A letter hact g hM (.inl (left τ))
  let b := limit (U := U) O A letter hact g hM (.inl (middle τ))
  let c := limit (U := U) O A letter hact g hM (.inl (right τ))
  let d := limit (U := U) O A letter hact g hM (.inr τ)
  have hab : dist a b ^ 2 = 1 := side O A letter hact g hM S hU (first τ)
  have hbc : dist b c ^ 2 = 1 := side O A letter hact g hM S hU (second τ)
  have hcd : dist c d ^ 2 = 1 := side O A letter hact g hM S hU (Step.pos (.inr (τ,0)))
  have hda : dist d a ^ 2 = 1 := by
    simpa only [source, target, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte] using
      side O A letter hact g hM S hU (Step.pos (.inr (τ,1)))
  have hac : 2 ≤ dist a c ^ 2 := by
    let p := Path.cons (first τ) (.cons (second τ) (.nil _))
    have hp : p.fields.Nodup := by simpa [p, Path.fields, first_field, second_field] using square_core_ne τ
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
        admissible_square_pair τ _ _ (first_mem_square τ) (second_mem_square τ)
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha
  have hbd : 2 ≤ dist b d ^ 2 := by
    let p := Path.cons (second τ) (.cons (Step.pos (.inr (τ,0))) (.nil _))
    have hp : p.fields.Nodup := by simp [p, Path.fields, second_field, Step.pos]
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, Step.pos, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
        admissible_square_pair τ _ _ (second_mem_square τ) (fresh_mem_square τ 0)
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha
  have hq := CATZero.quadrilateral (OrbitLimit.catZero O U) a b c d
  rw [hab,hbc,hcd,hda] at hq
  nlinarith [sq_nonneg (dist (CATZero.mid (OrbitLimit.catZero O U) a c)
    (CATZero.mid (OrbitLimit.catZero O U) b d))]

include S hU hinv in
/-- Source Proposition configuration (i), constructed from matches, paths,
unit edge expectations, and decorating-square rigidity. -/
theorem metricCore : CoreGeometry.MetricCore
    (fun v => limit (U := U) O A letter hact g hM (.inl v)) := by
  constructor
  · intro a b hab
    exact side O A letter hact g hM S hU (coreStep hab)
  · intro a b c hab hbc hac
    obtain ⟨τ, hh | hh⟩ := twoPath_complete hab hbc hac
    · rw [← hh.1, ← hh.2.2]
      exact square_twoStep O A letter hact g hM S hU inv hinv τ
    · rw [← hh.1, ← hh.2.2, dist_comm]
      exact square_twoStep O A letter hact g hM S hU inv hinv τ
  · intro a b c d hab hbc hcd hac hbd hq
    let p := Path.cons (coreStep hab) (.cons (coreStep hbc) (.cons (coreStep hcd) (.nil _)))
    have hp : p.fields.Nodup := by
      simpa only [p, Path.fields, coreStep_field] using corePath_three_nodup hab hbc hcd hac hbd
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, coreStep_field] using corePath_three_admissible hab hbc hcd hq
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha

end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
