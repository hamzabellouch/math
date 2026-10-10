import Mathlib
import OAI.Combinatorics.KMedian.Process.TaperGraph
import OAI.Combinatorics.KMedian.Reduction.DeletionGeometry
import OAI.Combinatorics.KMedian.Sparse.SparseGraphReal
import OAI.Combinatorics.KMedian.Rounding.RationalTaperData

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {n : ℕ} {X : Type*} [PseudoMetricSpace X]

noncomputable def rationalGraphData (Δ : ℕ) (g P : ℚ) (d : Fin n → Fin n → ℚ)
    (location : Fin n → X) (own : Fin n → Finset (Fin n))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : Fin n, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    GraphData Δ (g:ℝ) (P:ℝ) location own where
  radius i := (rationalRadius g P (d i):ℝ)
  marginal h i := (sourceMarginals g P (d i) (own i) Δ h:ℝ)
  radius_nonneg i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).1
  marginal_nonneg h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.1 h
  marginal_le_one h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.1 h
  incoming_mass i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.1
  incoming_count i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.1
  own_certain i h he := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.1 h he
  lower h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.1 h (by exact_mod_cast he)
  upper h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.1 h (by exact_mod_cast he)
  minimal i R hR he := by
    simp only [hdist] at he
    exact (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.2 R hR he

theorem rational_sparse_graph (Δ : ℕ) (g P : ℚ) (d : Fin n → Fin n → ℚ)
    (location : Fin n → X) (own : Fin n → Finset (Fin n))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : Fin n, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    let D := rationalGraphData Δ g P d location own hg hunit hP hP1 hd hdist htotal hown howncard
    let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
    let μ := SparseGraph.law q
    μ.length ≤ n*n+(n*n)*(n*n)+1 ∧
      (∀ G, 0 < μ.real.weight G → D.Good G) ∧
      (∀ h i, μ.real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → μ.real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
        D.marginal h i*D.marginal l j) := by
  dsimp only
  let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
  have hall := fun i => rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)
  have hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1 := fun h i => ⟨(hall i).2.1 h,(hall i).2.2.1 h⟩
  have hs : ∀ i, (∑ h, q h i)=(Δ:ℚ) := fun i => (hall i).2.2.2.2.1
  have hh := SparseGraph.real_law_spec q Δ hq hs
  refine ⟨(SparseGraph.law_spec q Δ hq hs).1,?_,hh.2.1,hh.2.2.1⟩
  intro G hG
  refine ⟨hh.1 G hG,?_,?_⟩
  · intro i h he
    exact hh.2.2.2.1 G hG h i ((hall i).2.2.2.2.2.1 h he)
  · intro h i hedge
    change (0:ℝ) < (q h i:ℝ)
    have hn : q h i≠0 := fun he => hh.2.2.2.2 G hG h i he hedge
    exact_mod_cast lt_of_le_of_ne (hq h i).1 (Ne.symm hn)

end MetricKMedian.Taper
end
end

end OAI
