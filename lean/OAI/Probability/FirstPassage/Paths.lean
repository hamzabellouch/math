import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFPP

abbrev Vertex := ℤ × ℤ

abbrev Edge := Vertex × Bool

inductive Step where
  | east | west | north | south
  deriving DecidableEq

def Step.delta : Step → Vertex
  | .east => (1, 0)
  | .west => (-1, 0)
  | .north => (0, 1)
  | .south => (0, -1)

def Step.reverse : Step → Step
  | .east => .west
  | .west => .east
  | .north => .south
  | .south => .north

def Step.edge (p : Vertex) : Step → Edge
  | .east => (p, false)
  | .west => (p + (-1, 0), false)
  | .north => (p, true)
  | .south => (p + (0, -1), true)

@[simp] theorem Step.delta_reverse (d : Step) : d.reverse.delta = -d.delta := by
  cases d <;> rfl

@[simp] theorem Step.edge_reverse (p : Vertex) (d : Step) :
    d.reverse.edge (p + d.delta) = d.edge p := by
  cases d <;> simp [Step.reverse, Step.edge, Step.delta, Prod.ext_iff]

def displacement (ds : List Step) : Vertex := (ds.map Step.delta).sum

def pathCost (τ : Edge → ℝ) (p : Vertex) : List Step → ℝ
  | [] => 0
  | d :: ds => τ (d.edge p) + pathCost τ (p + d.delta) ds

@[simp] theorem displacement_nil : displacement [] = 0 := rfl
@[simp] theorem displacement_cons (d : Step) (ds : List Step) :
    displacement (d :: ds) = d.delta + displacement ds := by simp [displacement]
@[simp] theorem displacement_append (ds es : List Step) :
    displacement (ds ++ es) = displacement ds + displacement es := by
  simp [displacement]

theorem pathCost_append (τ : Edge → ℝ) (p : Vertex) (ds es : List Step) :
    pathCost τ p (ds ++ es) =
      pathCost τ p ds + pathCost τ (p + displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, add_assoc]

theorem pathCost_nonneg {τ : Edge → ℝ} (hτ : ∀ e, 0 ≤ τ e)
    (p : Vertex) (ds : List Step) : 0 ≤ pathCost τ p ds := by
  induction ds generalizing p with
  | nil => exact le_refl 0
  | cons d ds ih => exact add_nonneg (hτ _) (ih _)

noncomputable def transverse (b : ℝ) (z : Vertex) : ℝ := z.2 - b * z.1
noncomputable def support (b m a : ℝ) (z : Vertex) : ℝ := m * z.1 + a * transverse b z
noncomputable def defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) : ℝ :=
  pathCost τ p ds - support b m a (displacement ds)

@[simp] theorem transverse_add (b : ℝ) (z w : Vertex) :
    transverse b (z + w) = transverse b z + transverse b w := by
  simp [transverse]; ring
@[simp] theorem support_add (b m a : ℝ) (z w : Vertex) :
    support b m a (z + w) = support b m a z + support b m a w := by
  simp [support]; ring

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

theorem minimum_defect (τ : Edge → ℝ) (b m am ap : ℝ) (ha : am ≤ ap)
    (p : Vertex) (ds : List Step) :
    min (defect τ b m ap p ds) (defect τ b m am p ds) =
      defect τ b m ((am + ap) / 2) p ds -
        ((ap - am) / 2) * |transverse b (displacement ds)| := by
  unfold defect support
  by_cases hr : 0 ≤ transverse b (displacement ds)
  · rw [abs_of_nonneg hr, min_eq_left]
    · ring
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha) hr]
  · have hr' : transverse b (displacement ds) ≤ 0 := le_of_not_ge hr
    rw [abs_of_nonpos hr', min_eq_right]
    · ring
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hr']

theorem transverse_chunk_witness (τ : Edge → ℝ) (b m am ap η s : ℝ)
    (ha : am ≤ ap) (hs : 0 < s) (hη : 0 < η)
    (hgap : 4 * η ≤ (ap - am) / 2) (p : Vertex) (ds : List Step)
    (hfull : s ≤ |transverse b (displacement ds)|)
    (hcheap : defect τ b m ((am + ap) / 2) p ds < η * s) :
    defect τ b m ap p ds < -η * s ∨ defect τ b m am p ds < -η * s := by
  have hm := minimum_defect τ b m am ap ha p ds
  have hg : 0 ≤ (ap - am) / 2 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfull hg
  have hprod' := mul_le_mul_of_nonneg_right hgap (le_of_lt hs)
  have : min (defect τ b m ap p ds) (defect τ b m am p ds) < -η * s := by
    nlinarith [mul_pos hη hs]
  exact min_lt_iff.mp this

end PlanarFPP

end OAI
