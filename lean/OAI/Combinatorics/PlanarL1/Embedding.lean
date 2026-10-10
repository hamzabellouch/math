import OAI.Combinatorics.PlanarL1.Schedule
import OAI.Combinatorics.PlanarL1.PlanarMetric

namespace OAI


section

universe u
namespace PlanarL1.Columns.Model.Ambient
open Parameters
variable {k : ℕ} {V : Type u} [Fintype V] {M : Model (k+1)}
variable {q : ℕ} (g : GoodSpacing q) (A : Ambient M) (v : V → M.Point Set.univ A.root)
include g

/-- The actual finite coupled process produces a cut metric with a universal
lower bound. The finite initial units, mesh and number of steps are selected
from the given vertices; they do not enter the distortion constant. -/
lemma exists_uniform_cuts : ∃ C : FiniteL1.CutFamily V, ∀ x y,
    (scheduleGain/(q:ℝ))*dist (v x) (v y) ≤ C.distance x y ∧
      C.distance x y ≤ 2*dist (v x) (v y) := by
  classical
  obtain ⟨ε,hε,N,hcover⟩ := finite_schedule_cover (fun x y => dist (v x) (v y))
    (fun _ _ => dist_nonneg) g.gt_one
  obtain ⟨m,hm,hmany,hmesh⟩ := exists_mesh N
  let σ : Fin q → ℝ := fun i => ε/((i.val+1:ℕ):ℝ)
  have hσ (i : Fin q) : 0<σ i := div_pos hε (Nat.cast_pos.mpr (Nat.zero_lt_succ _))
  let C : Fin q → FiniteL1.CutFamily V := fun i => World.normalizedCuts g A v (hσ i) hm N
  let D : FiniteL1.CutFamily V := FiniteL1.CutFamily.scale (1/(q:ℝ)) (div_nonneg (by norm_num) g.pos.le)
    (FiniteL1.CutFamily.sum C)
  have hupper (i : Fin q) (x y : V) : (C i).distance x y ≤ 2*dist (v x) (v y) :=
    World.normalizedCuts_upper g A v (hσ i) hm N x y
  have hdistance (x y : V) : D.distance x y=(1/(q:ℝ))*∑ i, (C i).distance x y := by
    rw [FiniteL1.CutFamily.distance_scale,FiniteL1.CutFamily.distance_sum]
  refine ⟨D,fun x y => ⟨?_,?_⟩⟩
  · by_cases hxy : 0<dist (v x) (v y)
    · obtain ⟨i,f,hf,hlo,hhi⟩ := hcover x y hxy
      have hl : scheduleGain*dist (v x) (v y) ≤ (C i).distance x y :=
        World.normalizedCuts_lower g A v (hσ i) hm hf hmesh hmany hlo hhi
      have hs : (C i).distance x y ≤ ∑ j, (C j).distance x y :=
        Finset.single_le_sum (fun j _ => (C j).distance_nonneg x y) (Finset.mem_univ i)
      rw [hdistance]
      have hh := mul_le_mul_of_nonneg_left (hl.trans hs) (div_nonneg (show (0:ℝ)≤1 by norm_num) g.pos.le)
      calc
        _ = (1/(q:ℝ))*(scheduleGain*dist (v x) (v y)) := by ring
        _ ≤ _ := hh
    · have he : dist (v x) (v y)=0 := le_antisymm (le_of_not_gt hxy) dist_nonneg
      rw [he,mul_zero]
      exact D.distance_nonneg x y
  · rw [hdistance]
    calc
      _ ≤ (1/(q:ℝ))*∑ i : Fin q, 2*dist (v x) (v y) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hupper i x y))
          (div_nonneg (by norm_num) g.pos.le)
      _ = 2*dist (v x) (v y) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← mul_assoc,one_div,inv_mul_cancel₀ g.pos.ne',one_mul]

/-- A finite-dimensional real L1 embedding of vertices of any connected
terminal noncrossing column model, with a constant depending only on q. -/
lemma exists_L1_embedding : ∃ (Ω : Type u) (measurable : MeasurableSpace Ω)
    (μ : @MeasureTheory.Measure Ω measurable)
    (f : V → @MeasureTheory.Lp Ω ℝ measurable _ 1 μ), ∀ x y,
      dist (v x) (v y) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ (2/(scheduleGain/(q:ℝ)))*dist (v x) (v y) := by
  obtain ⟨C,hC⟩ := A.exists_uniform_cuts g v
  let : MeasurableSpace (Set V) := ⊤
  obtain ⟨f,hf⟩ := C.embedding_of_bounds (fun x y => dist (v x) (v y))
    (div_pos scheduleGain_pos g.pos) (fun x y => (hC x y).1) (fun x y => (hC x y).2)
  exact ⟨Set V,⊤,MeasureTheory.Measure.count,f,hf⟩
end PlanarL1.Columns.Model.Ambient

end



section

namespace PlanarL1.HeightTree.Layout
open Columns
variable {U : Type*} [Fintype U] {T : HeightTree U} {k : ℕ}
noncomputable def ambient (L : T.Layout (k+1)) : Model.Ambient L.model where
  root := L.column T.root
  connected i := by
    obtain ⟨p,_⟩ := L.exists_prefixPath (T.root_ancestor (L.leaf (L.column T.root)))
      (T.root_ancestor (L.leaf i)) le_rfl le_rfl
    exact ⟨p.word⟩
end PlanarL1.HeightTree.Layout

namespace PlanarL1
open Parameters Columns.Model

/-- Theorem 1.1 of the literal source. The spacing is selected once, before
any graph or length data. Its finite cut embedding is converted to real Lp1.
All geometric realization and process hypotheses are discharged above. -/
theorem planar_graph_metrics_embed_L1 : MainStatement := by
  classical
  obtain ⟨q,g⟩ := exists_goodSpacing
  refine ⟨max 1 (2/(scheduleGain/(q:ℝ))),le_max_left _ _,?_⟩
  intro n G length hc hp hs hl
  let o : Fin n := Classical.choice hc.nonempty
  obtain ⟨s,L,hL,hd⟩ := Weighted.EnlargedTree.column_model_of_planar hc hs hl o hp
  cases s with
  | zero => exact (Fin.elim0 (L.column (Weighted.EnlargedTree.tree hc hs hl o).root))
  | succ k =>
    let A := L.ambient
    obtain ⟨Ω,measurable,μ,f,hf⟩ := A.exists_L1_embedding g (fun v => L.point (.inl v))
    refine ⟨Ω,measurable,μ,f,?_⟩
    intro x y
    have he : dist (L.point (.inl x)) (L.point (.inl y))=graphDistance G length x y := hd x y
    have hh := hf x y
    change (L.point (.inl x)).distance (L.point (.inl y)) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ (2/(scheduleGain/(q:ℝ)))*(L.point (.inl x)).distance (L.point (.inl y)) at hh
    rw [hd x y] at hh
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    rw [← he]
    exact dist_nonneg
end PlanarL1


end

end OAI
