import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PowerEulerError
import OAI.Combinatorics.TriangleRemoval.Process.TriangleIndex

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem densityEdgeSafe_triangle_euler_error {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))-(triangles G).card+
      3*(6/(n : ℝ)^2/p)*(triangles G).card| ≤ 6*η^2*((n : ℝ)*p^2)+2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast ht.card_pos
  have hm : (0 : ℝ) < G.card := by exact_mod_cast (graph_nonempty_of_triangles ht).card_pos
  have he : 9/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p) := by
    rw [h.2.1]
    field_simp
    ring
  have hv := triangle_degree_variance_le (graph_nonempty_of_triangles ht) ((n : ℝ)*p^2)
    (η*((n : ℝ)*p^2)) (by positivity) h.2.2
  have hlo := (densityEdgeSafe_triangle_bounds h).1
  have hhalf : (n : ℝ)^3*p^3/12 ≤ (triangles G).card := by
    have hh := mul_le_mul_of_nonneg_left hη1 (show 0 ≤ (n : ℝ)^3*p^3/6 by positivity)
    nlinarith only [hlo,hh]
  have hVbound : triangleDegreeVariance G/(triangles G).card ≤ 6*η^2*((n : ℝ)*p^2) := by
    apply (div_le_iff₀ hq).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 6*η^2*((n : ℝ)*p^2) by positivity)
    rw [h.2.1] at hv
    nlinarith only [hv,hh]
  have hVnonneg : 0 ≤ triangleDegreeVariance G/(triangles G).card :=
    div_nonneg (triangleDegreeVariance_nonneg G) hq.le
  rw [step_mean_triangle_count_centered ht]
  have he' : 9*(triangles G).card/(G.card : ℝ) = 3*(6/(n : ℝ)^2/p)*(triangles G).card := by
    rw [mul_div_right_comm,he]
  rw [he']
  apply abs_le.mpr
  constructor <;> linarith only [hVbound,hVnonneg]

lemma relative_power_absolute_drift_bound {X Y s t r a B : ℝ} {b : ℕ}
    (hX : 0 ≤ X) (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hscale : t = s*(1-r)^b) (hratio : s ≤ 2*t) (hcap : X ≤ B*s)
    (ha : 0 ≤ a) (h : |Y-X+(b : ℝ)*r*X| ≤ a*s) :
    |Y/t-X/s| ≤ 2*(a+B*(b : ℝ)^2*r^2) := by
  have hpow := power_euler_error b hr hr1
  have he : Y/t-X/s = ((Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r))/t := by
    apply (eq_div_iff ht.ne').mpr
    field_simp [hs.ne']
    rw [hscale]
    ring
  have hB : 0 ≤ B := (mul_nonneg_iff_of_pos_right hs).mp (hX.trans hcap)
  have hnum : |(Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r)| ≤
      (a+B*(b : ℝ)^2*r^2)*s := by
    calc
      _ ≤ |Y-X+(b : ℝ)*r*X|+|X*((1-r)^b-1+(b : ℝ)*r)| := abs_sub _ _
      _ ≤ a*s+X*((b : ℝ)^2*r^2) := by
        apply add_le_add h
        rw [abs_mul,abs_of_nonneg hX]
        exact mul_le_mul_of_nonneg_left hpow hX
      _ ≤ a*s+(B*s)*((b : ℝ)^2*r^2) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcap (by positivity))
      _ = _ := by ring
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ a+B*(b : ℝ)^2*r^2 by positivity)
  exact hnum.trans (by nlinarith only [hm])

lemma early_triangle_drift_single {n : ℕ} {i : ℕ} {G : Graph n} {η : ℝ}
    (hn : 0 < n) (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i < prefixTime n)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (h : densityEdgeSafe n (earlyDensity n i) η G) :
    |pmfMean (step G) (fun H => ((triangles H).card : ℝ))/earlyTriangleScale n (i+1)-
      (triangles G).card/earlyTriangleScale n i| ≤
      12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2 := by
  let p := earlyDensity n i
  let lam := 6/(n : ℝ)^2/p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := early_density_positive hn hp hi.le
  have hp1 := early_density_positive hn hp (show i+1 ≤ prefixTime n by omega)
  have hstep := earlyDensity_succ n i
  have hl : 0 ≤ lam := by dsimp [lam]; positivity
  have hl1 : lam ≤ 1 := by
    apply (div_le_iff₀ hp0).mpr
    dsimp only [p] at hp0 ⊢
    linarith only [hstep,hp1]
  have hs : 0 < earlyTriangleScale n i := by unfold earlyTriangleScale earlyTemplateScale; change 0 < (n : ℝ)^3*p^3/6; positivity
  have ht : 0 < earlyTriangleScale n (i+1) := by unfold earlyTriangleScale earlyTemplateScale; positivity
  have hscale : earlyTriangleScale n (i+1) = earlyTriangleScale n i*(1-lam)^3 := by
    have he : earlyDensity n (i+1) = p*(1-lam) := by
      have he : earlyDensity n (i+1) = p-6/(n : ℝ)^2 := by dsimp [p]; linarith only [hstep]
      rw [he]
      dsimp [lam]
      field_simp
    unfold earlyTriangleScale earlyTemplateScale
    rw [he,mul_pow]
    dsimp [p]
    ring
  have hcap : ((triangles G).card : ℝ) ≤ 2*earlyTriangleScale n i := by
    have hu := (densityEdgeSafe_triangle_bounds h).2
    have hh := mul_le_mul_of_nonneg_left (show 1+η ≤ 2 by linarith) hs.le
    exact hu.trans (by dsimp only [earlyTriangleScale,earlyTemplateScale] at hh ⊢; nlinarith only [hh])
  have hd := densityEdgeSafe_triangle_euler_error hn hp0 hη hη1 h
  have he : (6*η^2*lam+2*lam/((n : ℝ)*p^2))*earlyTriangleScale n i = 6*η^2*((n : ℝ)*p^2)+2 := by
    dsimp [lam,earlyTriangleScale,earlyTemplateScale]
    change (6*η^2*(6/(n : ℝ)^2/p)+2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2))*((n : ℝ)^3*p^3/6) = _
    field_simp
  rw [← he] at hd
  have hh := relative_power_absolute_drift_bound (Nat.cast_nonneg (triangles G).card) hs ht hl hl1
    hscale hreg hcap (by positivity : 0 ≤ 6*η^2*lam+2*lam/((n : ℝ)*p^2)) hd
  norm_num only [Nat.cast_ofNat] at hh
  dsimp only [lam,p] at hh
  convert hh using 1
  ring

lemma early_grid_sum_bounds {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (j : ℕ) (hj : j ≤ prefixTime n) :
    (∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) ≤ Real.log n ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) ≤ 1/(2*prefixD n) ∧
    (∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) ≤ 6/(n : ℝ)*Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p := earlyDensity n
  let h : ℝ := 6/(n : ℝ)^2
  let lam : ℕ → ℝ := fun i => h/p i
  have hpos : ∀ i ≤ prefixTime n, 0 < p i := fun i hi => early_density_positive hn hp hi
  have hstep : ∀ i, p i = p (i+1)+h := fun i => earlyDensity_succ n i
  have hlog : (∑ i ∈ Finset.range j, lam i) ≤ Real.log n := by
    have hh := (density_log_sum_bounds p h j (fun i hi => hpos i (hi.trans hj))
      (fun i _ => hstep i)).1
    have hp0 := Real.log_nonpos (hpos 0 (Nat.zero_le _)).le (earlyDensity_le_one n 0)
    have hln := early_density_log_bound hn hp hj
    dsimp only [lam] at hh ⊢
    linarith only [hh,hp0,hln]
  have hlD : (∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) ≤ 1/(2*prefixD n) := by
    have hh := inverse_square_grid_sum p (n : ℝ) h j hnR (by dsimp [h]; positivity)
      (fun i hi => hpos i (hi.trans hj)) (fun i _ => hstep i)
    have he : (∑ i ∈ Finset.range j, 2*h/((n : ℝ)*p i^3)) =
        2*(∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have := hpos i ((Finset.mem_range.mp hi).le.trans hj)
      dsimp only [lam]
      field_simp
    rw [he] at hh
    have hDj := earlyCodegreeScale_ge_prefixD n j hj (le_trans (by positivity) hp)
    have hD : 0 < prefixD n := by unfold prefixD; have := early_density_positive hn hp (show prefixTime n ≤ prefixTime n by rfl); rw [earlyDensity_prefix] at this; positivity
    have hDj' : prefixD n ≤ (n : ℝ)*p j^2 := by simpa only [earlyTemplateScale,pow_one] using hDj
    have hr := one_div_le_one_div_of_le hD hDj'
    have ht : 0 ≤ 1/((n : ℝ)*p 0^2) := by positivity
    have he' : 1/prefixD n = 2*(1/(2*prefixD n)) := by ring
    rw [he'] at hr
    linarith only [hh,hr,ht]
  have hsq : (∑ i ∈ Finset.range j, (lam i)^2) ≤ 6/(n : ℝ)*Real.log n := by
    have hlmax (i : ℕ) (hi : i < j) : lam i ≤ 6/(n : ℝ) := by
      have hp' := hp.trans (earlyDensity_antitone n (hi.le.trans hj))
      change 1/(n : ℝ) ≤ p i at hp'
      apply (div_le_iff₀ (hpos i (hi.le.trans hj))).mpr
      dsimp only [h]
      have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 6/(n : ℝ) by positivity)
      convert hm using 1
      field_simp
    calc
      _ ≤ ∑ i ∈ Finset.range j, (6/(n : ℝ))*lam i := by
        apply Finset.sum_le_sum
        intro i hi
        have hli : 0 ≤ lam i := by dsimp [lam,h]; exact div_nonneg (by positivity) (hpos i ((Finset.mem_range.mp hi).le.trans hj)).le
        nlinarith only [mul_le_mul_of_nonneg_right (hlmax i (Finset.mem_range.mp hi)) hli]
      _ = 6/(n : ℝ)*(∑ i ∈ Finset.range j, lam i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  exact ⟨hlog,hlD,hsq⟩

theorem early_triangle_drift_bound {n : ℕ} (η : ℝ) (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : ∀ i < prefixTime n, earlyTriangleScale n i ≤ 2*earlyTriangleScale n (i+1))
    (j : ℕ) (hj : j ≤ prefixTime n) (ω : History (Graph n) (prefixTime n))
    (hsafe : ∀ i < j, densityEdgeSafe n (earlyDensity n i) η (ω (historyIndex (prefixTime n) i))) :
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => (triangles G).card/earlyTriangleScale n i)
        (prefixTime n) j ω| ≤ 12*η^2*Real.log n+2/prefixD n+216*Real.log n/(n : ℝ) := by
  have hb := early_grid_sum_bounds hn hp j hj
  rw [history_relative_drift_sum (fun _ => step) (fun G : Graph n => ((triangles G).card : ℝ))
    (earlyTriangleScale n) (prefixTime n) j hj ω]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |pmfMean (step (ω (historyIndex (prefixTime n) i))) (fun G => ((triangles G).card : ℝ))/earlyTriangleScale n (i+1)-
          (triangles (ω (historyIndex (prefixTime n) i))).card/earlyTriangleScale n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        (12*η^2*(6/(n : ℝ)^2/earlyDensity n i)+
        4*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)+
        36*(6/(n : ℝ)^2/earlyDensity n i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij := Finset.mem_range.mp hi
      exact early_triangle_drift_single hn hp (by omega) hη hη1 (hreg i (by omega)) (hsafe i hij)
    _ = 12*η^2*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i)+
        4*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2))+
        36*(∑ i ∈ Finset.range j, (6/(n : ℝ)^2/earlyDensity n i)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 12*η^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hb.2.1 (by norm_num : (0 : ℝ) ≤ 4)
      have h₃ := mul_le_mul_of_nonneg_left hb.2.2 (by norm_num : (0 : ℝ) ≤ 36)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ ⊢
      norm_num only [invOf_eq_inv,inv_div,inv_one] at h₂
      nlinarith only [h₁,h₂,h₃]

end SharpTerminalLeave
end
end

end OAI
