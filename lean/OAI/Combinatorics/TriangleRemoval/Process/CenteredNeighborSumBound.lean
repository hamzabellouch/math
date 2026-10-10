import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.HistoryGraphNested

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma centered_neighbor_sum_bound {n : ℕ} {G : Graph n} (_hG : G ⊆ completeGraph n)
    (u v : Fin n) {s η : ℝ} (_hη : 0 ≤ η) (_hs : 0 ≤ s)
    (hrow : ∀ a b, {a,b} ∈ G → |(currentCodegree G a b : ℝ)-s| ≤ η*s) :
    |centeredCodegreeNeighborSum G u v s| ≤ 2*η*s*(currentCodegree G u v : ℝ) := by
  unfold centeredCodegreeNeighborSum
  calc
    _ ≤ ∑ w ∈ commonNeighbors G u v,
      |(currentCodegree G u w : ℝ)+currentCodegree G v w-2*s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ commonNeighbors G u v, 2*η*s := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨huw,hvw⟩ := (mem_commonNeighbors G u v w).mp hw
      have hh := abs_add_le ((currentCodegree G u w : ℝ)-s) ((currentCodegree G v w : ℝ)-s)
      have he : (currentCodegree G u w : ℝ)+currentCodegree G v w-2*s =
          ((currentCodegree G u w : ℝ)-s)+((currentCodegree G v w : ℝ)-s) := by ring
      rw [he]
      linarith only [hh,hrow u w huw,hrow v w hvw]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,currentCodegree]; ring

lemma normalized_pair_drift_factor {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (huv : u ≠ v) (s t : ℝ) (hs : s ≠ 0) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s =
      edgeStabilityScalar s t (triangles G).card (if {u,v} ∈ G then 1 else 0)*
        ((currentCodegree G u v : ℝ)/s)-
      centeredCodegreeNeighborSum G u v s/((triangles G).card*t) := by
  rw [normalized_codegree_centered_drift hG u v huv]
  unfold edgeStabilityScalar edgeStabilityRate
  field_simp [hs]
  ring

lemma normalized_pair_drift_bound {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (huv : u ≠ v) {s t S lam r η : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hS : 0 < S) (hl : 0 ≤ lam)
    (hscale : t = s*(1-lam)^2) (hratio : s ≤ 2*t)
    (hident : s = lam*S) (hr : r ≤ 1/2)
    (hQerr : |(triangles G).card/S-1| ≤ r) (hη : 0 ≤ η)
    (hrow : ∀ a b, {a,b} ∈ G → |(currentCodegree G a b : ℝ)-s| ≤ η*s)
    (hcap : (currentCodegree G u v : ℝ) ≤ 2*s) :
    |pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s| ≤
      16*r*lam+4*lam^2+8*lam/s+16*η*lam := by
  have hκ0 : (0 : ℝ) ≤ if {u,v} ∈ G then 1 else 0 := by split_ifs <;> norm_num
  have hκ1 : (if {u,v} ∈ G then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hb := edge_stability_coefficients hs ht hS hl hscale hratio hident hr hQerr hκ0 hκ1
  have hQ := (triangle_relative_inverse_bound hS hr hQerr).1
  have hc : 0 ≤ (currentCodegree G u v : ℝ)/s := by positivity
  have hc' : (currentCodegree G u v : ℝ)/s ≤ 2 := (div_le_iff₀ hs).mpr hcap
  have hneigh : |centeredCodegreeNeighborSum G u v s| ≤ 4*η*s^2 := by
    apply (centered_neighbor_sum_bound hG u v hη hs.le hrow).trans
    exact (mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 2*η*s)).trans_eq (by ring)
  have hquot : |centeredCodegreeNeighborSum G u v s/((triangles G).card*t)| ≤ 16*η*lam := by
    rw [abs_div,abs_of_pos (mul_pos hQ ht)]
    calc
      _ ≤ (4*η*s^2)/((triangles G).card*t) := div_le_div_of_nonneg_right hneigh (mul_pos hQ ht).le
      _ = 4*η*edgeStabilityRate s t (triangles G).card := by unfold edgeStabilityRate; ring
      _ ≤ 4*η*(4*lam) := mul_le_mul_of_nonneg_left hb.1.2 (by positivity)
      _ = _ := by ring
  rw [normalized_pair_drift_factor hG u v huv s t hs.ne']
  calc
    _ ≤ |edgeStabilityScalar s t (triangles G).card (if {u,v} ∈ G then 1 else 0)*
          ((currentCodegree G u v : ℝ)/s)|+
        |centeredCodegreeNeighborSum G u v s/((triangles G).card*t)| := abs_sub _ _
    _ ≤ (8*r*lam+2*lam^2+4*lam/s)*2+16*η*lam := by
      apply add_le_add _ hquot
      rw [abs_mul,abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left hc' (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hb.2 (by norm_num))
    _ = _ := by ring

theorem prefix_pair_compensator_bound : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ u v : Fin n, u ≠ v →
    (∀ i < j, (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ) ≤ 2*earlyTemplateScale 1 2 n i) →
    |historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω| ≤
      16*prefixTriangleRadius n*Real.log n+4/prefixD n+24*Real.log n/(n : ℝ)+
        16*prefixEdgeRadius n*Real.log n := by
  filter_upwards [prefix_triangle_tracking,earlyTemplateScale_regular 1 2,
    earlyTriangleScale_regular,prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n htrack hreg htri hr hp hn
  intro ω hω hnoise j hj hsafe u v huv hcap
  have hn0 : 0 < n := by omega
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm (i : ℕ) (hi : i < j) :
      |pmfMean (step (ω (historyIndex (prefixTime n) i))) (prefixNormalizedCodegree u v (i+1))-
        prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))| ≤
        16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)^2+
        8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        16*prefixEdgeRadius n*(6/(n : ℝ)^2/earlyDensity n i) := by
    have hs := hsafe i hi
    have hc := htrack ω hω hnoise i (by omega) (fun k hk => hsafe k (by omega))
    have hg := early_codegree_grid hn0 hp (by omega : i < prefixTime n)
    have hrow (a b : Fin n) (he : {a,b} ∈ ω (historyIndex (prefixTime n) i)) :
        |(currentCodegree (ω (historyIndex (prefixTime n) i)) a b : ℝ)-earlyTemplateScale 1 2 n i| ≤
          prefixEdgeRadius n*earlyTemplateScale 1 2 n i := by
      have hh := hs.2.2 {a,b} he
      rw [triangleDegree_eq_codegree hs.1 he] at hh
      simpa only [earlyTemplateScale,pow_one] using hh
    change |pmfMean (step (ω (historyIndex (prefixTime n) i))) (fun H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n (i+1))-
      (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ)/earlyTemplateScale 1 2 n i| ≤ _
    simpa only [earlyTemplateScale,pow_one] using
      normalized_pair_drift_bound hs.1 u v huv (hreg.1 i (by omega)) (hreg.1 (i+1) (by omega))
        (htri.1 i (by omega)) hg.2.2.1 hg.1 (hreg.2.2 i (by omega)) hg.2.1 hr.2 hc hη hrow (hcap i hi)
  unfold historyCompensator historyCounter
  rw [Nat.min_eq_left hj]
  have hg := early_grid_sum_bounds hn0 hp j hj
  calc
    _ ≤ ∑ i ∈ Finset.range j, |pmfMean (step (ω (historyIndex (prefixTime n) i))) (prefixNormalizedCodegree u v (i+1))-
        prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        (16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)^2+
        8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        16*prefixEdgeRadius n*(6/(n : ℝ)^2/earlyDensity n i)) :=
      Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    _ = 16*prefixTriangleRadius n*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i)+
        4*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2)+
        8*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2))+
        16*prefixEdgeRadius n*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hg.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hr.1)
      have h₂ := mul_le_mul_of_nonneg_left hg.2.2 (by norm_num : (0 : ℝ) ≤ 4)
      have h₃ := mul_le_mul_of_nonneg_left hg.2.1 (by norm_num : (0 : ℝ) ≤ 8)
      have h₄ := mul_le_mul_of_nonneg_left hg.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hη)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ h₄ ⊢
      norm_num at h₃
      nlinarith only [h₁,h₂,h₃,h₄]

end SharpTerminalLeave
end
end

end OAI
