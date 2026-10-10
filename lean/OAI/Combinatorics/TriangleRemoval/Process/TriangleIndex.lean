import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeNoiseExit
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeNoiseRadius
import OAI.Combinatorics.TriangleRemoval.Process.CommonNeighborsComplete
import OAI.Combinatorics.TriangleRemoval.Asymptotics.DensityEdgeSafe

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

abbrev TriangleIndex (n : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard 3)
def triangleRequired {n : ℕ} (t : TriangleIndex n) : Graph n := t.val.powersetCard 2

@[simp] theorem triangle_copyCount {n : ℕ} (G : Graph n) :
    copyCount (triangleRequired (n := n)) G = ((triangles G).card : ℝ) := by
  unfold copyCount triangleRequired
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) (fun (t : Finset (Fin n)) => intact (t.powersetCard 2) G)]
  simp [intact,triangles]

@[simp] theorem triangle_copyEdgeLoad {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    copyEdgeLoad (triangleRequired (n := n)) G e = (triangleDegree G e : ℝ) := by
  unfold copyEdgeLoad triangleRequired
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) (fun (t : Finset (Fin n)) => if e ∈ t.powersetCard 2 then intact (t.powersetCard 2) G else 0)]
  simp only [triangleDegree,incidentTriangles,triangles,Finset.filter_filter]
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  unfold intact
  split_ifs <;> simp_all

noncomputable def earlyTriangleScale (n i : ℕ) : ℝ := earlyTemplateScale 3 3 n i/6
noncomputable def triangleNoiseLoad (n i : ℕ) : ℝ := 2*earlyTemplateScale 1 2 n i

def PrefixTriangleNoise (n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ¬ RelativeNoiseExit (triangleRequired (n := n)) (triangleNoiseLoad n)
    (earlyTriangleScale n) 2 (codegreeNoiseRadius n) (prefixTime n) ω

lemma earlyTriangleScale_regular : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n (i+1) ≤ earlyTriangleScale n i) ∧
    (∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1)) ∧
    relativeScaleBudget (earlyTriangleScale n) (prefixTime n) ≤ 6*Real.log n := by
  filter_upwards [earlyTemplateScale_regular 3 3,earlyTemplateScale_log_budget 3 3] with n hr hb
  refine ⟨fun i hi => div_pos (hr.1 i hi) (by norm_num),?_,?_,?_⟩
  · intro i hi
    exact div_le_div_of_nonneg_right (hr.2.1 i hi) (by norm_num)
  · intro i hi
    have hh := div_le_div_of_nonneg_right (hr.2.2 i hi) (by norm_num : (0 : ℝ) ≤ 6)
    simpa only [earlyTriangleScale,mul_div_assoc] using hh
  · convert hb using 1
    · unfold relativeScaleBudget earlyTriangleScale
      congr 1
      ext i
      ring
    · norm_num

lemma completeGraph_early_mass {n : ℕ} (hn : 0 < n) :
    ((completeGraph n).card : ℝ) = (n : ℝ)^2*earlyDensity n 0/2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [card_completeGraph,Nat.cast_choose_two]
  simp only [earlyDensity,Nat.cast_zero,mul_zero,zero_div,sub_zero]
  field_simp

lemma triangleDegree_complete {n : ℕ} (e : Finset (Fin n)) (he : e ∈ completeGraph n) :
    triangleDegree (completeGraph n) e = n-2 := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp he)
  rw [triangleDegree_eq_codegree (Finset.Subset.refl _) he,currentCodegree_complete u v huv]

lemma triangleCount_complete_formula {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ) = (n : ℝ)*(n-1)*(n-2)/6 := by
  have hh := triangle_degree_sum (completeGraph n)
  have he : (∑ e ∈ completeGraph n, (triangleDegree (completeGraph n) e : ℝ)) =
      ((completeGraph n).card : ℝ)*(n-2) := by
    calc
      _ = ∑ _e ∈ completeGraph n, ((n-2 : ℕ) : ℝ) := Finset.sum_congr rfl (fun e he => by rw [triangleDegree_complete e he])
      _ = _ := by simp [Nat.cast_sub hn]; ring
  rw [he,card_completeGraph,Nat.cast_choose_two] at hh
  nlinarith only [hh]

lemma initial_triangle_relative_error {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (completeGraph n)).card : ℝ)/earlyTriangleScale n 0-1 = -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hs : earlyTriangleScale n 0 = ((n : ℝ)-1)^3/6 := by
    unfold earlyTriangleScale earlyTemplateScale earlyDensity
    simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero]
    field_simp
  rw [triangleCount_complete_formula hn,hs]
  field_simp
  ring

lemma initial_triangle_ratio_le_two {n : ℕ} (hn : 2 ≤ n) :
    copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0 ≤ 2 := by
  rw [triangle_copyCount]
  have hh := initial_triangle_relative_error hn
  have hz : 0 ≤ 1/((n : ℝ)-1)^2 := by positivity
  rw [neg_div] at hh
  linarith

lemma densityEdgeSafe_triangle_load {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ p) (hη : η ≤ 1) (h : densityEdgeSafe n p η G) :
    copyLoadSafe (triangleRequired (n := n)) (2*((n : ℝ)*p^2)) G := by
  intro e he
  rw [triangle_copyEdgeLoad]
  have hb := (abs_le.mp (h.2.2 e he)).2
  have hd : 0 ≤ (n : ℝ)*p^2 := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hp 2)
  have hh := mul_le_mul_of_nonneg_right hη hd
  linarith

end SharpTerminalLeave
end
end

end OAI
