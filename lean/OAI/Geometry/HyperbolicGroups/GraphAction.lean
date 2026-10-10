import Mathlib
import OAI.Geometry.HyperbolicGroups.ConditionalStar
import OAI.Geometry.HyperbolicGroups.Graph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Step
variable {G L : Type*} [Group G]
def value {a b : Vertex} (s : Step a b) (label : Field → L) (letter : L → G) : G :=
  if s.forward then letter (label s.field) else (letter (label s.field))⁻¹

lemma value_symm {a b : Vertex} (s : Step a b) (label : Field → L) (letter : L → G) :
    s.symm.value label letter = (s.value label letter)⁻¹ := by
  cases h : s.forward <;> simp [value, symm, h]
end Step

namespace Path
variable {G L : Type*} [Group G] {a b c : Vertex}
def eval (label : Field → L) (letter : L → G) : {a b : Vertex} → Path a b → G
  | _, _, .nil _ => 1
  | _, _, .cons s p => s.value label letter * p.eval label letter

lemma eval_append (label : Field → L) (letter : L → G) (p : Path a b) (q : Path b c) :
    (p.append q).eval label letter = p.eval label letter * q.eval label letter := by
  induction p with
  | nil => simp [append, eval]
  | cons s p ih => simp only [append, eval, ih, mul_assoc]

lemma eval_symm (label : Field → L) (letter : L → G) (p : Path a b) :
    p.symm.eval label letter = (p.eval label letter)⁻¹ := by
  induction p with
  | nil => simp [symm, eval]
  | cons s p ih => simp [symm, eval_append, eval, ih, Step.value_symm]

/-- A field-sign map is compatible with each actual edge traversal. -/
def Compatible (σ : Field → Bool) : {a b : Vertex} → Path a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons s p => σ s.field = s.forward ∧ p.Compatible σ

lemma compatible_congr (p : Path a b) {σ τ : Field → Bool}
    (h : ∀ f ∈ p.fields, σ f = τ f) (hp : p.Compatible σ) : p.Compatible τ := by
  induction p with
  | nil => trivial
  | cons s p ih =>
    exact ⟨(h s.field (by simp [fields])).symm.trans hp.1,
      ih (fun f hf => h f (by simp [fields, hf])) hp.2⟩

lemma exists_compatible (p : Path a b) (h : p.fields.Nodup) : ∃ σ, p.Compatible σ := by
  classical
  induction p with
  | nil => exact ⟨fun _ => true, trivial⟩
  | cons s p ih =>
    obtain ⟨σ, hσ⟩ := ih (List.nodup_cons.mp h).2
    refine ⟨Function.update σ s.field s.forward, ?_, ?_⟩
    · simp
    · apply p.compatible_congr (σ := σ) _ hσ
      intro f hf
      rw [Function.update_of_ne]
      intro he
      exact (List.nodup_cons.mp h).1 (he ▸ hf)

def read (inv : L ≃ L) (σ : Field → Bool) (f : Field) : L ≃ L :=
  if σ f then Equiv.refl L else inv

lemma eval_word (p : Path a b) {σ : Field → Bool} (hσ : p.Compatible σ)
    (label : Field → L) (letter : L → G) (inv : L ≃ L)
    (hinv : ∀ i, letter (inv i) = (letter i)⁻¹) :
    p.eval label letter = OrbitWord.word (fun _ : Unit => label) (read inv σ) letter () p.fields := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [eval, fields, OrbitWord.cons, ih hσ.2]
    congr 1
    cases hs : s.forward <;> simp [Step.value, read, hσ.1, hs, hinv]

lemma bound {X : Type*} [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X)
    (label : Field → L) (letter : L → G) {M : ℝ}
    (hb : ∀ i, dist o (A (letter i) o) ≤ M) (p : Path a b) :
    dist o (A (p.eval label letter) o) ≤ p.length * M := by
  induction p with
  | nil => simp [eval, length]
  | cons s p ih =>
    have hs : dist o (A (s.value label letter) o) ≤ M := by
      cases h : s.forward
      · simpa only [Step.value, h, Bool.false_eq_true, ↓reduceIte,
          IsometricAction.displacement_inv] using hb (label s.field)
      · simpa only [Step.value, h, ↓reduceIte] using hb (label s.field)
    have hh := (IsometricAction.displacement_mul_le A o _ _).trans (add_le_add hs ih)
    simpa [eval, length, add_mul, add_comm M] using hh
end Path

/-- Actual consistency of the labelled graph in a group, not a metric
configuration or a conclusion of the sampling argument. -/
structure Potential {L G : Type*} [Group G] (label : Field → L) (letter : L → G) where
  val : Vertex → G
  root_one : val root = 1
  edge : ∀ f, val (target f) = val (source f) * letter (label f)

namespace Potential
variable {L G : Type*} [Group G] {label : Field → L} {letter : L → G}
  (g : Potential label letter)

lemma step {a b : Vertex} (s : Step a b) : g.val b = g.val a * s.value label letter := by
  cases h : s.forward
  · obtain ⟨ha,hb⟩ := s.endpoints_neg h
    simp only [Step.value, h, Bool.false_eq_true, ↓reduceIte]
    have hh := g.edge s.field
    simp only [ha,hb] at hh
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  · obtain ⟨ha,hb⟩ := s.endpoints_pos h
    simp only [Step.value, h, ↓reduceIte]
    simpa only [ha,hb] using g.edge s.field

lemma path {a b : Vertex} (p : Path a b) : g.val b = g.val a * p.eval label letter := by
  induction p with
  | nil => simp [Path.eval]
  | cons s p ih => rw [ih, g.step s, mul_assoc]; rfl

lemma route (v : Vertex) : g.val v = (MasterGraph.route v).eval label letter := by
  simpa only [g.root_one, one_mul] using g.path (MasterGraph.route v)

lemma orbit_path {X : Type*} [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X)
    {a b : Vertex} (p : Path a b) :
    dist (A (g.val a) o) (A (g.val b) o) = dist o (A (p.eval label letter) o) := by
  rw [g.path p, map_mul, IsometryEquiv.mul_apply]
  exact (A (g.val a)).isometry.dist_eq _ _

/-- Rooted potentials are provided by the actual cycle relators on fixed routes. -/
def of_relators (label : Field → L) (letter : L → G)
    (hroot : (MasterGraph.route root).eval label letter = 1)
    (hloop : ∀ f, ((MasterGraph.route (source f)).append
      (.cons (Step.pos f) (MasterGraph.route (target f)).symm)).eval label letter = 1) :
    Potential label letter where
  val v := (MasterGraph.route v).eval label letter
  root_one := hroot
  edge f := by
    have hh := hloop f
    simp only [Path.eval_append, Path.eval, Step.value, Step.pos, ↓reduceIte,
      Path.eval_symm] at hh
    exact (eq_of_mul_inv_eq_one (by simpa only [← mul_assoc] using hh)).symm

end Potential
end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
