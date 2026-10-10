import Mathlib
import OAI.Analysis.HardSphere.Paths.LevelList

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma occurrenceHit_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (ω ω' : Noise) (R : ℝ) :
    occurrenceHit K R (occurrenceList n d ω) (occurrenceList n d ω') ≤
      20*∑ u ∈ Finset.range (n/2+1),
        nearPotential u (fun j ↦ position ω' j u) (3*R+5) ω := by
  have h := oneSideHit_le K n hn hnK d hd ω ω' R
  have h' := oneSideHit_le K n hn hnK d hd ω' ω R
  simp_rw [nearPotential_swap _ _ ω ω'] at h'
  unfold occurrenceHit
  linarith

lemma occurrenceSoft_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (ω ω' : Noise) (B : ℝ) (hB : 0 < B) :
    occurrenceSoft K B (occurrenceList n d ω) (occurrenceList n d ω') ≤
      (10*Real.exp (5/(3*B)))*∑ u ∈ Finset.range (n/2+1),
        Real.exp (-twoCopyDistance u (ω,ω')/(3*B)) := by
  have h := level_sum_le n hn d hd ω
    (fun x ↦ Real.exp (-distanceToList K x (occurrenceList n d ω')/B))
    (fun t ↦ Real.exp (5/(3*B))*Real.exp (-twoCopyDistance (min t (n-t)) (ω,ω')/(3*B)))
    (fun _ ↦ by positivity) (by
      intro t ht x hx
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hdev := distanceToList_deviation_le K n hn hnK d hd ω ω' t ht x hx
      have hBp : 0 < 3*B := by positivity
      rw [← add_div]
      apply (le_div_iff₀ hBp).mpr
      have he : (-distanceToList K x (occurrenceList n d ω')/B)*(3*B) =
          -3*distanceToList K x (occurrenceList n d ω') := by field_simp
      rw [he]
      linarith)
  have hf := folded_sum_le n
    (fun u ↦ Real.exp (-twoCopyDistance u (ω,ω')/(3*B))) (fun _ ↦ (Real.exp_pos _).le)
  change occurrenceSoft K B _ _ ≤ _ at h
  simp_rw [← Finset.mul_sum] at h
  have hpos : 0 < Real.exp (5/(3*B)) := Real.exp_pos _
  nlinarith

def skeletonHitConstant : ℝ := hitConstant/720
lemma skeletonHitConstant_pos : 0 < skeletonHitConstant := div_pos hitConstant_pos (by norm_num)

theorem skeleton_hit_moment (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (R : ℕ) :
    (∫⁻ z : Noise × Noise, ENNReal.ofReal (Real.exp
      ((skeletonHitConstant/(1+(R:ℝ))^2) *
        occurrenceHit K (R:ℝ) (occurrenceList n d z.1) (occurrenceList n d z.2)))
      ∂law.prod law) ≤ 2 := by
  have hcoeff : skeletonHitConstant/(1+(R:ℝ))^2*20 ≤
      hitConstant/(1+((3*R+5:ℕ):ℝ))^2 := by
    have hR : 0 ≤ (R:ℝ) := by positivity
    have hden : (1+((3*R+5:ℕ):ℝ))^2 ≤ 36*(1+(R:ℝ))^2 := by
      push_cast
      nlinarith
    calc
      _ = hitConstant/(36*(1+(R:ℝ))^2) := by
        unfold skeletonHitConstant
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_left hitConstant_pos.le (by positivity) hden
  refine le_trans (lintegral_mono (fun z ↦ ?_)) (two_copy_hit_moment (n/2) (3*R+5))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h := occurrenceHit_le K n hn hnK d hd z.1 z.2 (R:ℝ)
  have ha : 0 ≤ skeletonHitConstant/(1+(R:ℝ))^2 := by
    exact div_nonneg skeletonHitConstant_pos.le (sq_nonneg _)
  calc
    _ ≤ (skeletonHitConstant/(1+(R:ℝ))^2) *
      (20*∑ u ∈ Finset.range (n/2+1),
        nearPotential u (fun j ↦ position z.2 j u) (3*(R:ℝ)+5) z.1) :=
      mul_le_mul_of_nonneg_left h ha
    _ = (skeletonHitConstant/(1+(R:ℝ))^2*20) *
      ∑ u ∈ Finset.range (n/2+1),
        nearPotential u (fun j ↦ position z.2 j u) ((3*R+5:ℕ):ℝ) z.1 := by
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff
      (Finset.sum_nonneg (fun u _ ↦ nearPotential_nonneg _ _ _ _))

theorem skeleton_soft_moment (B : ℝ) (hB : 0 < B) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ K n : ℕ, 0 < n → 8*n ≤ K →
      ∀ d : Fin 2 → ℤ, (∀j, |d j| ≤ n) →
      (∫⁻ z : Noise × Noise, ENNReal.ofReal (Real.exp
        (ξ*occurrenceSoft K B (occurrenceList n d z.1) (occurrenceList n d z.2)))
        ∂law.prod law) ≤ 2 := by
  obtain ⟨η,hη,hm⟩ := two_copy_soft_moment (3*B) (by positivity)
  let C : ℝ := 10*Real.exp (5/(3*B))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨η/C,div_pos hη hC,fun K n hn hnK d hd ↦ ?_⟩
  refine le_trans (lintegral_mono (fun z ↦ ?_)) (hm (n/2))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (η/C)*(C*∑ u ∈ Finset.range (n/2+1),
      Real.exp (-twoCopyDistance u z/(3*B))) :=
      mul_le_mul_of_nonneg_left (occurrenceSoft_le K n hn hnK d hd z.1 z.2 B hB)
        (div_pos hη hC).le
    _ = _ := by field_simp

instance listVertexMeasurableSpace : MeasurableSpace (List Vertex) := ⊤
instance listVertexDiscreteMeasurableSpace : DiscreteMeasurableSpace (List Vertex) := ⟨fun _ ↦ trivial⟩

@[fun_prop] lemma measurable_levelList (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) :
    Measurable (fun ω ↦ levelList n d ω t) := by
  cases t with
  | zero =>
    exact (measurable_of_countable (fun a : Vertex ↦ [a])).comp
      (measurable_baseVertex n d 0)
  | succ t =>
    exact (measurable_of_countable (fun a : Vertex × Vertex ↦ refineStep a.1 a.2)).comp
      ((measurable_baseVertex n d t).prodMk (measurable_baseVertex n d (t+1)))

@[fun_prop] lemma measurable_occurrenceList (n : ℕ) (d : Fin 2 → ℤ) :
    Measurable (occurrenceList n d) := by
  have hl (ts : List ℕ) : Measurable (fun ω ↦ ts.flatMap (levelList n d ω)) := by
    induction ts with
    | nil => exact measurable_const
    | cons t ts ih =>
      simpa only [List.flatMap_cons,Function.comp_def] using
        (measurable_of_countable (fun p : List Vertex × List Vertex ↦ p.1 ++ p.2)).comp
          ((measurable_levelList n d t).prodMk ih)
  exact hl (List.range (n+1))

def skeletonLaw (n : ℕ) (d : Fin 2 → ℤ) : Measure (List Vertex) :=
  law.map (occurrenceList n d)

instance skeletonLaw_isProbability (n : ℕ) (d : Fin 2 → ℤ) :
    IsProbabilityMeasure (skeletonLaw n d) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_occurrenceList n d).aemeasurable).mpr inferInstance

end HardSphere.DyadicSkeleton
end
end

end OAI
