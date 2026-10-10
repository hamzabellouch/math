import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathRequiredBaseChild

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pmf_boolean_map_le {A : Type*} (P : PMF A) (f g : A → Bool)
    (h : ∀ a ∈ P.support, f a = true → g a = true) :
    ((P.map f) true).toReal ≤ ((P.map g) true).toReal := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : P a = 0
  · simp only [ha,ite_self,le_refl]
  · by_cases hf : f a = true
    · have hg := h a ((PMF.mem_support_iff _ _).mpr ha) hf
      simp only [hf,hg,↓reduceIte,le_refl]
    · simp only [Ne.symm hf,↓reduceIte,zero_le]

lemma markedGood_map_true (p : PMF (Bool × Bool)) :
    markedGood p = ((p.map Prod.snd) true).toReal := by
  unfold markedGood
  rw [← pmfMean_map p Prod.snd (fun b => if b then 1 else 0)]
  simp [pmfMean]

section TracePathProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def actualPathVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) : ℝ :=
  (((ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => z.2.any (fun c => decide (c.address = path.reverse)))) true).toReal

theorem actualPathVisitProbability_le_marked (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) :
    actualPathVisitProbability H N d k focus parent path ≤
      pathVisitProbability H N d k focus parent path := by
  let c : QueryCall ι τ := ⟨[],focus,parent⟩
  let ν := fun _ : τ => PMF.uniformOfFintype (Fin N)
  let P := ExposureTree.fresh ν (jointMarkedQuery H N (pathRequired path) d k c)
  have ht : P.map (fun z => (z.1,z.2.2)) =
      ExposureTree.fresh ν (tracedGridQuery H N d k c) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_trace]
  have hm : P.map (fun z => (z.1,z.2.1)) =
      ExposureTree.fresh ν (markedGridQueryDepth H N (pathRequired path) d k [] focus parent) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_marked]
  unfold actualPathVisitProbability pathVisitProbability
  rw [markedGood_map_true]
  rw [← ht,← hm,PMF.map_comp,PMF.map_comp]
  apply pmf_boolean_map_le
  intro z hz hh
  obtain ⟨a,ha,hea⟩ := List.any_eq_true.mp hh
  have hit : ∃ a ∈ z.2.2, a.address = path.reverse ++ c.address := by
    exact ⟨a,ha,by simpa only [c,List.append_nil] using of_decide_eq_true hea⟩
  exact jointMarkedQuery_hit H N d k c path ν hz hit

theorem actualPathVisitProbability_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (e : ι) (T : τ) (he : e ∈ H T)
    (hpath : LegalQueryPath H ((H T).erase e) (some T) path) :
    actualPathVisitProbability H N d k ((H T).erase e) (some T) path ≤
      prefixWeight (fun t => (2/(N : ℝ))*b t) k ^ path.length /
        (path.length.factorial : ℝ) :=
  (actualPathVisitProbability_le_marked H N d k _ _ path).trans
    (pathVisitProbability_factorial H N b hb hq path d k hkd hkN hlen e T he hpath)

end TracePathProbability
end SharpTerminalLeave

end

end OAI
