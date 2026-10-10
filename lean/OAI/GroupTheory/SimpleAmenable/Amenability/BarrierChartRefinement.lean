import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierSignalSystem

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierChartRefinement
open Classical Set

theorem barrierComponent_cut_sign {a : ℕ} {B : Set (ℝ×ℝ)} {j : Fin 4} {c : CutRing}
    (hline : ∀x  ∈  squareInterior,cutForm a j x=ordinary c → x ∈ B)
    {p q : GenericSquare a} (hp : p.val ∈ barrierRegion B)
    (hq : q.val ∈ connectedComponentIn (barrierRegion B) p.val) :
    (cutForm a j p.val < ordinary c ↔ cutForm a j q.val < ordinary c) := by
  have hpc := mem_connectedComponentIn hp
  have no_cross (x y : ℝ×ℝ)
      (hx : x ∈ connectedComponentIn (barrierRegion B) p.val)
      (hy : y ∈ connectedComponentIn (barrierRegion B) p.val)
      (hxc : cutForm a j x < ordinary c) (hyc : ordinary c ≤ cutForm a j y) : False := by
    obtain ⟨z,hz,hzc⟩ := isPreconnected_connectedComponentIn.intermediate_value hx hy
      (cutForm_continuous a j).continuousOn ⟨hxc.le,hyc⟩
    have hz' := connectedComponentIn_subset (barrierRegion B) p.val hz
    exact hz'.2 (hline z hz'.1 hzc)
  constructor
  · intro h
    by_contra hn
    exact no_cross p.val q.val hpc hq h (le_of_not_gt hn)
  · intro h
    by_contra hn
    exact no_cross q.val p.val hq hpc h (le_of_not_gt hn)

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem component_cut_sign {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N)
    (b₁ b₂ : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs₁ : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs₂ : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    {j : Fin 4} {c : CutRing} (hband : |conjugate c| ≤ N)
    {p q : GenericSquare a}
    (hq : q ∈ barrierComponentCell (sampledBarriers ha i N
      (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂) p.val) :
    squareSign (j,c) p=squareSign (j,c) q := by
  apply decide_eq_decide.mpr
  apply barrierComponent_cut_sign _
    (generic_mem_barrierRegion (sampledBarriers_supported ha i N _ b₂) p) hq
  intro x hx hxc
  have hc : c ∈ barrierCandidate a j N := ⟨by linarith, x,hx,hxc⟩
  exact S.central_line_barrier i hN b₁ b₂ hs₁ hs₂ hc hband x hx hxc

theorem component_step_eventually {m : ℕ} (f : Fin m → GenericSquare a → Fin m × (CutRing×CutRing))
    (hf : ∀i,HasSquareArrangement (f i)) :
    ∃N₀ : ℝ,∃hN₀ : 0 < N₀,∀N : ℝ,∀hN : N₀ ≤ N, ∀b₁ b₂ :
      ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool,
      (∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j)) →
      (∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j)) →
      ∀i (p q : GenericSquare a),
      q ∈ barrierComponentCell (sampledBarriers ha i N
        (fun j => S.marks (N:=N) (lt_of_lt_of_le hN₀ hN) j (b₁ j)) b₂) p.val → f i p=f i q := by
  choose T hT using hf
  let C : ℝ := ∑i,∑l ∈ T i,|conjugate l.2|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun l _ => abs_nonneg _))
  refine ⟨C+1,by linarith,?_⟩
  intro N hN b₁ b₂ hs₁ hs₂ i p q hq
  apply hT i p q
  intro l hl
  have hi : (∑l ∈ T i,|conjugate l.2|) ≤ C :=
    Finset.single_le_sum (f:=fun k => ∑l∈T k,|conjugate l.2|) (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg _)) (Finset.mem_univ i)
  have hl' : |conjugate l.2| ≤ C := (Finset.single_le_sum (fun l _ => abs_nonneg _) hl).trans hi
  exact S.component_cut_sign i (by linarith) b₁ b₂ hs₁ hs₂ (by linarith : |conjugate l.2| ≤ N) hq

theorem component_affine_eventually {m : ℕ} (g : polygonFullGroup a m) :
    ∃N₀ : ℝ,∃hN₀ : 0 < N₀,∀N : ℝ,∀hN : N₀ ≤ N, ∀b₁ b₂ :
      ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool,
      (∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j)) →
      (∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j)) →
      ∀i (p q : GenericSquare a),
      q ∈ barrierComponentCell (sampledBarriers ha i N
        (fun j => S.marks (N:=N) (lt_of_lt_of_le hN₀ hN) j (b₁ j)) b₂) p.val →
      fullGroupAffineData g i p=fullGroupAffineData g i q :=
  S.component_step_eventually (fullGroupAffineData g) (fullGroupAffineData_arrangement g)

end BarrierSignalSystem
end BarrierChartRefinement

section BarrierCrossings
open Classical Set

theorem barrierIntersection_lattice {a : ℕ} (ha : 0 < a) {i j : Fin 4} (hij : i ≠ j)
    {c d : CutRing} {p : ℝ×ℝ} (hi : cutForm a i p=ordinary c)
    (hj : cutForm a j p=ordinary d) : InFlagLattice (commonVertexDenominator a) p := by
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha i j hij c d p hi hj
  have hD : (commonVertexDenominator a : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha)
  refine ⟨(u,v),?_⟩
  apply Prod.ext  <;> simp only [scaledOrdinary,hu,hv]  <;> field_simp

noncomputable def barrierInteriorSite {a m : ℕ} (ha : 0 < a) (i : Fin m) (j : Fin 4)
    {p : ℝ×ℝ} (hp : p ∈ squareInterior)
    (hl : InFlagLattice (commonVertexDenominator a) p) :
    FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) :=
  ⟨(i,⟨p,(barrierFlagDirection_spec ha j).1,
    ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩,
    fun h => (ne_of_gt hp.1.1 h).elim,fun h => (ne_of_lt hp.1.2 h).elim,
    fun h => (ne_of_gt hp.2.1 h).elim,fun h => (ne_of_lt hp.2.2 h).elim⟩⟩),hl⟩

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem crossing_in_subdivision {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N)
    {j k : Fin 4} (hjk : j ≠ k) {c d : CutRing} (hc : c ∈ barrierCandidate a j N)
    (hcQ : |conjugate c| ≤ 4*N+Q) (hd : |conjugate d| ≤ B)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b)
    {t : ℝ} (ht : t ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c))
    (hk : cutForm a k (barrierLinePoint a j c t)=ordinary d) :
    t ∈ barrierSubdivision ha i j c (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b) := by
  by_cases hL : t=barrierLineLower a j c
  · simp [barrierSubdivision,hL]
  by_cases hU : t=barrierLineUpper a j c
  · simp [barrierSubdivision,hU]
  have ht' : t ∈ Ioo (barrierLineLower a j c) (barrierLineUpper a j c) :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hL),lt_of_le_of_ne ht.2 hU⟩
  have hp := (barrierLinePoint_interior_iff hc t).mpr ht'
  let z := barrierInteriorSite ha i j hp
    (barrierIntersection_lattice ha hjk (cutForm_barrierLinePoint a j c t) hk)
  have hzpoint : barrierSitePoint z=barrierLinePoint a j c t := rfl
  have hzt : z.val.1=i := rfl
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := cutForm_barrierLinePoint a j c t
  have hzbit := S.intersection_first_true hN hjk hcQ hd z hzline hk b hs
  have hzmem := (S.mem_marks_iff (lt_of_lt_of_le zero_lt_one hN) j b hs z).mpr hzbit
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨z,Finset.mem_filter.mpr ⟨hzmem,hzt,hp,hzline⟩,?_⟩
  exact barrierLineParameter_point a j c t

end BarrierSignalSystem

theorem barrierLineParameter_add (j : Fin 4) (p q : ℝ×ℝ) :
    barrierLineParameter j (p+q)=barrierLineParameter j p+barrierLineParameter j q := by
  fin_cases j  <;> simp [barrierLineParameter]

theorem barrierLinePoint_translate (a : ℕ) (j : Fin 4) (c : CutRing)
    (u : CutRing×CutRing) (t : ℝ) :
    barrierLinePoint a j (c+integralCutForm a j u)
      (t+barrierLineParameter j (ordinary u.1,ordinary u.2))=
    barrierLinePoint a j c t+(ordinary u.1,ordinary u.2) := by
  have hp : cutForm a j (barrierLinePoint a j c t+(ordinary u.1,ordinary u.2)) =
      ordinary (c+integralCutForm a j u) := by
    rw [cutForm_add,cutForm_barrierLinePoint,cutForm_ordinary,map_add]
  have hparam : barrierLineParameter j
      (barrierLinePoint a j c t+(ordinary u.1,ordinary u.2)) =
      t+barrierLineParameter j (ordinary u.1,ordinary u.2) := by
    rw [barrierLineParameter_add,barrierLineParameter_point]
  rw [←hparam]
  exact barrierLinePoint_parameter hp

end BarrierCrossings

end SimpleAmenable
end
end

end OAI
