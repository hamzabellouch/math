import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleDensity
import OAI.Combinatorics.ContingencyTables.Dense.GridMinCut

namespace OAI

/-! # Actual weighted bin-cut bound for the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication GridBoundary

variable {I J : Type*} [Fintype I] [Fintype J]

lemma closedBin_distances (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (x : Fin (dimension A) → ℝ) (hx : ClosedBin (corner v) x) :
    ∀ i,|x i-realCorner v i| ≤ 1 := by
  intro i
  change |x i-(corner v i:ℝ)| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith [(hx i).1,(hx i).2]

lemma tube_distances (A : Instance I J) {K : ℕ} {Q : (Fin (dimension A) → ℤ) → Prop}
    (edge : CutEdge K Q) (r : ℝ) (x : Fin (dimension A) → ℝ) (hx : x ∈ edgeTube edge r) :
    (∀ i,|x i-realCorner edge.val.1 i| ≤ 1+r) ∧
      (∀ i,|x i-realCorner edge.val.2.1 i| ≤ 1+r) := by
  have hcoord (i : Fin (dimension A)) := hx i (Set.mem_univ i)
  constructor
  · intro i
    have hi := hcoord i
    dsimp [tubeLower,tubeUpper] at hi
    change |x i-(corner edge.val.1 i:ℝ)| ≤ 1+r
    by_cases he : i=edge.val.2.2
    · subst i
      simp only [ite_true] at hi
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · simp only [ite_eq_right he] at hi
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
  · intro i
    have hi := hcoord i
    dsimp [tubeLower,tubeUpper] at hi
    change |x i-(corner edge.val.2.1 i:ℝ)| ≤ 1+r
    by_cases he : i=edge.val.2.2
    · have hadj : (corner edge.val.2.1 i:ℝ)=(corner edge.val.1 i:ℝ)+1 := by
        simpa only [he,Int.cast_add,Int.cast_one] using
          congrArg (fun z : ℤ => (z:ℝ)) edge.property.1.1
      simp only [ite_eq_left he] at hi
      rw [hadj]
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · have heq : corner edge.val.2.1 i=corner edge.val.1 i :=
        congrArg Subtype.val (edge.property.1.2 i he)
      simp only [ite_eq_right he] at hi
      rw [heq]
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩

lemma tube_comparison (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} {Q : (Fin (dimension A) → ℤ) → Prop} (edge : CutEdge K Q)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : Fin (dimension A) → ℝ)
    (hx : x ∈ edgeTube edge r) :
    rho A C a z x ≤ 4*min (V A C a z (realCorner edge.val.1))
      (V A C a z (realCorner edge.val.2.1)) := by
  obtain ⟨hlo,hhi⟩ := tube_distances A edge r x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  apply le_min
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A C a hC ha haH z x _ (1+r) (by positivity) hlo).trans (by linarith)
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A C a hC ha haH z x _ (1+r) (by positivity) hhi).trans (by linarith)

lemma interpolation_bounds (d K q : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hq : q ≤ d) :
    0 < denseInterpolation d K ∧ denseInterpolation d K < 1 ∧
      denseInterpolation d K*K ≤ 1/4 ∧
      (q-1:ℕ)*(2*(denseInterpolation d K*K)) ≤ (1/2:ℝ) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hqR : (q-1:ℕ) ≤ (d:ℝ) := by exact_mod_cast (Nat.sub_le q 1).trans hq
  have hden : (0:ℝ) < 4*d*K := by positivity
  have hr : denseInterpolation d K*K=1/(4*(d:ℝ)) := by
    unfold denseInterpolation
    field_simp [ne_of_gt (show (0:ℝ)<d by linarith),ne_of_gt (show (0:ℝ)<K by linarith)]
  refine ⟨by unfold denseInterpolation; positivity,?_,?_,?_⟩
  · unfold denseInterpolation
    rw [div_lt_one hden]
    nlinarith [mul_le_mul hdR hKR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ d)]
  · rw [hr,div_le_div_iff₀ (by positivity : (0:ℝ)<4*d) (by norm_num : (0:ℝ)<4)]
    linarith
  · rw [hr]
    have he : (q-1:ℕ)*(2*(1/(4*(d:ℝ))))=((q-1:ℕ):ℝ)/(2*d) := by ring
    rw [he,div_le_div_iff₀ (by positivity : (0:ℝ)<2*d) (by norm_num : (0:ℝ)<2)]
    linarith

/-- The companion bin weights satisfy the source cut bound directly
from their actual forest density and the precise published PL input. -/
theorem weighted_min_cut (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (Q : (Fin (dimension A) → ℤ) → Prop)
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun x => ¬Q x))) :
    (1/(128*(A.d:ℝ)*K))*min
        (∑ v : Selected K Q,V A C a z (realCorner v.val))
        (∑ v : Selected K (fun x => ¬Q x),V A C a z (realCorner v.val)) ≤
      ∑ e : CutEdge K Q,min (V A C a z (realCorner e.val.1))
        (V A C a z (realCorner e.val.2.1)) := by
  obtain ⟨ht,ht1,hr,hsize⟩ := interpolation_bounds A.d K (dimension A) A.hd hK
    (ForestScaledPenalty.free_card_le A)
  have hh := GridBoundary.weighted_min_cut hPL Q (denseInterpolation A.d K) ht ht1 hr hsize
    (rho A C a z) (fun v => V A C a z (realCorner v))
    (fun v => DenseWeights.binWeight_pos _ _ _) (rho_continuous A C a z).continuousOn
    (fun x _ => rho_positive A C a z x)
    (fun x _ y _ t ht ht1 => rho_logConcave A C a hC ha z x (Set.mem_univ _) y (Set.mem_univ _) t ht ht1)
    (fun v x hx => by
      have hclosed : ClosedBin (corner v) x := fun i => ⟨(hx i).1.le,(hx i).2.le⟩
      exact (bin_comparison A C a hC ha haH z (realCorner v) x
        (fun i => by simpa only [abs_sub_comm] using closedBin_distances A v x hclosed i)).1)
    (fun e x hx => tube_comparison A C a hC ha haH z e (denseInterpolation A.d K*K)
      (by positivity) (by linarith) x hx.1) hne hne'
  have hg := two_rpow_gain (denseInterpolation A.d K) ht.le
  have hm : 0 ≤ min (∑ v : Selected K Q,V A C a z (realCorner v.val))
      (∑ v : Selected K (fun x => ¬Q x),V A C a z (realCorner v.val)) := by
    apply le_min <;> exact Finset.sum_nonneg (fun _ _ => (DenseWeights.binWeight_pos _ _ _).le)
  have he : 1/(128*(A.d:ℝ)*K)=denseInterpolation A.d K/32 := by
    unfold denseInterpolation
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right (by linarith : denseInterpolation A.d K/32 ≤
    ((2:ℝ)^denseInterpolation A.d K-1)/16) hm).trans hh

end ContingencyTables.CompanionOracleDensity

end OAI
