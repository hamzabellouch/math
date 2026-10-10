import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeVertexCount
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeRadius

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma power_euler_error (b : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |(1-r)^b-1+(b : ℝ)*r| ≤ (b : ℝ)^2*r^2 := by
  have hber : ∀ b : ℕ, 0 ≤ (1-r)^b-1+(b : ℝ)*r := by
    intro b
    have hh := one_add_mul_le_pow (show -2 ≤ -r by linarith) b
    simp only [← sub_eq_add_neg,mul_neg] at hh
    linarith only [hh]
  have hupper : ∀ b : ℕ, (1-r)^b-1+(b : ℝ)*r ≤ (b : ℝ)^2*r^2 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1-r by linarith)
      have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      have hcube : 0 ≤ (b : ℝ)^2*r^3 := by positivity
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      nlinarith only [hm,hcube,mul_nonneg hn (sq_nonneg r),sq_nonneg r]
  rw [abs_of_nonneg (hber b)]
  exact hupper b

lemma densityEdgeSafe_rate_error {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) :
    |(n : ℝ)*p^2/(triangles G).card-6/(n : ℝ)^2/p| ≤
      2*η*(6/(n : ℝ)^2/p) ∧
    1/(triangles G).card ≤ 2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  let Q₀ : ℝ := (n : ℝ)^3*p^3/6
  let lam : ℝ := 6/(n : ℝ)^2/p
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 0 < (n : ℝ)*p^2 := by positivity
  have hid : lam*Q₀ = (n : ℝ)*p^2 := by dsimp [lam,Q₀]; field_simp
  obtain ⟨hlo,hhi⟩ := densityEdgeSafe_triangle_bounds h
  change Q₀*(1-η) ≤ _ at hlo
  change _ ≤ Q₀*(1+η) at hhi
  have hhalf : Q₀/2 ≤ (triangles G).card := by nlinarith [mul_le_mul_of_nonneg_left hη1 hQ₀.le]
  have habs : |Q₀-(triangles G).card| ≤ η*Q₀ := by apply abs_le.mpr; constructor <;> nlinarith only [hlo,hhi]
  constructor
  · have he : (n : ℝ)*p^2/(triangles G).card-lam = lam*(Q₀-(triangles G).card)/(triangles G).card := by rw [← hid]; field_simp
    change |(n : ℝ)*p^2/(triangles G).card-lam| ≤ 2*η*lam
    rw [he,abs_div,abs_mul,abs_of_pos hlam,abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have hm := mul_le_mul_of_nonneg_left habs hlam.le
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*η*lam by positivity)
    nlinarith only [hm,hh]
  · apply (div_le_div_iff₀ hq hD).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*lam by positivity)
    dsimp only [lam] at hid hh
    nlinarith only [hid,hh]

theorem densityEdgeSafe_copy_euler_error {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (b : ℕ) (hsize : ∀ a, (required a).card = b)
    {p η : ℝ} {G : Graph n} (hn : 0 < n) (hp : 0 < p)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    |pmfMean (step G) (copyCount required)-copyCount required G+
      (b : ℝ)*(6/(n : ℝ)^2/p)*copyCount required G| ≤
      (4*(b : ℝ)*η*(6/(n : ℝ)^2/p)+
        2*(b : ℝ)^2*(6/(n : ℝ)^2/p)/((n : ℝ)*p^2))*copyCount required G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  have hX := copyCount_nonneg required G
  have hD : 0 < (n : ℝ)*p^2 := by positivity
  have hr := densityEdgeSafe_rate_error hn hp hη hη1 h
  have hd := copyCount_drift_error required G b (n*p^2) (η*(n*p^2)) hsize h.2.2 hQ
  let lam := 6/(n : ℝ)^2/p
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hrate : (n : ℝ)*p^2/(triangles G).card ≤ 2*lam := by
    have hh := mul_le_mul_of_nonneg_left hr.2 hD.le
    have he : ((n : ℝ)*p^2)*(1/(triangles G).card) = (n : ℝ)*p^2/(triangles G).card := by ring
    rw [he,mul_div_cancel₀ _ hD.ne'] at hh
    exact hh
  have hcoef : ((b : ℝ)*(η*(n*p^2))+(b : ℝ)^2)/(triangles G).card ≤
      2*(b : ℝ)*η*lam+2*(b : ℝ)^2*lam/((n : ℝ)*p^2) := by
    have h₁ := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (b : ℝ)*η by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hr.2 (sq_nonneg (b : ℝ))
    dsimp only [lam] at h₁ ⊢
    simp only [div_eq_mul_inv] at h₁ h₂ ⊢
    nlinarith only [h₁,h₂]
  calc
    _ ≤ |pmfMean (step G) (copyCount required)-copyCount required G+
        ((b : ℝ)*(n*p^2)/(triangles G).card)*copyCount required G|+
        |((b : ℝ)*(lam-(n*p^2)/(triangles G).card))*copyCount required G| := by
      convert abs_add_le (pmfMean (step G) (copyCount required)-copyCount required G+
        ((b : ℝ)*(n*p^2)/(triangles G).card)*copyCount required G)
        (((b : ℝ)*(lam-(n*p^2)/(triangles G).card))*copyCount required G) using 1
      congr 1
      dsimp only [lam]
      ring
    _ ≤ (2*(b : ℝ)*η*lam+2*(b : ℝ)^2*lam/((n : ℝ)*p^2))*copyCount required G+
        (b : ℝ)*(2*η*lam)*copyCount required G := by
      apply add_le_add (hd.trans (mul_le_mul_of_nonneg_right hcoef hX))
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg b),abs_sub_comm,
        abs_of_nonneg hX]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr.1 (Nat.cast_nonneg b)) hX
    _ = _ := by dsimp [lam]; ring

lemma relative_power_drift_bound {X Y s t r a B : ℝ} {b : ℕ}
    (hX : 0 ≤ X) (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hscale : t = s*(1-r)^b) (hratio : s ≤ 2*t) (hcap : X ≤ B*s)
    (ha : 0 ≤ a) (h : |Y-X+(b : ℝ)*r*X| ≤ a*X) :
    |Y/t-X/s| ≤ 2*B*(a+(b : ℝ)^2*r^2) := by
  have hpow := power_euler_error b hr hr1
  have he : Y/t-X/s = ((Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r))/t := by
    apply (eq_div_iff ht.ne').mpr
    field_simp [hs.ne']
    rw [hscale]
    ring
  have hnum : |(Y-X+(b : ℝ)*r*X)-X*((1-r)^b-1+(b : ℝ)*r)| ≤
      (a+(b : ℝ)^2*r^2)*X := by
    calc
      _ ≤ |Y-X+(b : ℝ)*r*X|+|X*((1-r)^b-1+(b : ℝ)*r)| := abs_sub _ _
      _ ≤ a*X+X*((b : ℝ)^2*r^2) := by
        apply add_le_add h
        rw [abs_mul,abs_of_nonneg hX]
        exact mul_le_mul_of_nonneg_left hpow hX
      _ = _ := by ring
  have hB : 0 ≤ B := (mul_nonneg_iff_of_pos_right hs).mp (hX.trans hcap)
  have hX' : X ≤ 2*B*t := hcap.trans (by nlinarith only [mul_le_mul_of_nonneg_left hratio hB])
  rw [he,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  exact hnum.trans (by nlinarith only [mul_le_mul_of_nonneg_left hX' (show 0 ≤ a+(b : ℝ)^2*r^2 by positivity)])

lemma history_relative_drift_sum {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : α → ℝ) (s : ℕ → ℝ)
    (T j : ℕ) (hj : j ≤ T) (ω : History α T) :
    f (ω (historyIndex T j))/s j-f (ω (historyIndex T 0))/s 0-
      historyNoise K (fun k a => f a/s k) T j ω =
    ∑ k ∈ Finset.range j,
      (pmfMean (K k (ω (historyIndex T k))) f/s (k+1)-f (ω (historyIndex T k))/s k) := by
  unfold historyNoise historyIncrement
  simp only [Nat.min_eq_left hj,div_eq_mul_inv,pmfMean_mul_const]
  have he := Finset.sum_range_sub' (fun k => f (ω (historyIndex T k))*(s k)⁻¹) j
  have hh : (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k))*(s k)⁻¹-f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹))+
      (∑ k ∈ Finset.range j,
        (f (ω (historyIndex T (k+1)))*(s (k+1))⁻¹-
          pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹)) =
      -(∑ k ∈ Finset.range j,
        (pmfMean (K k (ω (historyIndex T k))) f*(s (k+1))⁻¹-
          f (ω (historyIndex T k))*(s k)⁻¹)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  linarith only [hh]

theorem early_relative_drift_bound {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (a b : ℕ) (hsize : ∀ x, (required x).card = b)
    (η : ℝ) (hn : 0 < n) (hp : 1/(n : ℝ) ≤ prefixDensity n)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hreg : ∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1))
    (j : ℕ) (hj : j ≤ prefixTime n) (ω : History (Graph n) (prefixTime n))
    (hsafe : ∀ i < j, densityEdgeSafe n (earlyDensity n i) η (ω (historyIndex (prefixTime n) i)))
    (hcap : ∀ i < j, copyCount required (ω (historyIndex (prefixTime n) i)) ≤
      2*earlyTemplateScale a b n i) :
    |copyCount required (ω (historyIndex (prefixTime n) j))/earlyTemplateScale a b n j-
      copyCount required (ω (historyIndex (prefixTime n) 0))/earlyTemplateScale a b n 0-
      historyNoise (fun _ => step) (fun i G => copyCount required G/earlyTemplateScale a b n i)
        (prefixTime n) j ω| ≤
      16*(b : ℝ)*η*Real.log n+4*(b : ℝ)^2/prefixD n+
        24*(b : ℝ)^2*Real.log n/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p := earlyDensity n
  let h : ℝ := 6/(n : ℝ)^2
  let lam : ℕ → ℝ := fun i => h/p i
  have hpos : ∀ i ≤ prefixTime n, 0 < p i := fun i hi => early_density_positive hn hp hi
  have hstep : ∀ i, p i = p (i+1)+h := fun i => earlyDensity_succ n i
  have hspos : ∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i := by
    intro i hi
    dsimp [earlyTemplateScale]
    have := hpos i hi
    positivity
  have hsingle (i : ℕ) (hi : i < j) :
      |pmfMean (step (ω (historyIndex (prefixTime n) i))) (copyCount required)/
          earlyTemplateScale a b n (i+1)-
        copyCount required (ω (historyIndex (prefixTime n) i))/earlyTemplateScale a b n i| ≤
      4*(4*(b : ℝ)*η*lam i+2*(b : ℝ)^2*lam i/((n : ℝ)*p i^2)+(b : ℝ)^2*(lam i)^2) := by
    have hiT : i < prefixTime n := hi.trans_le hj
    have hp0 := hpos i hiT.le
    have hp1 := hpos (i+1) (by omega)
    have hl : 0 ≤ lam i := by dsimp [lam,h]; positivity
    have hl1 : lam i ≤ 1 := by
      apply (div_le_iff₀ hp0).mpr
      have hh := hstep i
      linarith only [hh,hp1]
    have hscale : earlyTemplateScale a b n (i+1) = earlyTemplateScale a b n i*(1-lam i)^b := by
      have he : p (i+1) = p i*(1-lam i) := by dsimp [lam]; field_simp; linarith only [hstep i]
      change (n : ℝ)^a*p (i+1)^b = ((n : ℝ)^a*p i^b)*(1-lam i)^b
      rw [he,mul_pow]; ring
    have hd := densityEdgeSafe_copy_euler_error required b hsize hn hp0 hη hη1 (hsafe i hi)
    simpa only [lam,h,show (2 : ℝ)*2 = 4 by norm_num] using relative_power_drift_bound (copyCount_nonneg _ _)
      (hspos i hiT.le) (hspos (i+1) (by omega)) hl hl1 hscale (hreg i hiT) (hcap i hi)
      (by positivity) hd
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
  rw [history_relative_drift_sum _ _ _ _ _ hj]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |pmfMean (step (ω (historyIndex (prefixTime n) i))) (copyCount required)/earlyTemplateScale a b n (i+1)-
          copyCount required (ω (historyIndex (prefixTime n) i))/earlyTemplateScale a b n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j,
        4*(4*(b : ℝ)*η*lam i+2*(b : ℝ)^2*lam i/((n : ℝ)*p i^2)+(b : ℝ)^2*(lam i)^2) :=
      Finset.sum_le_sum (fun i hi => hsingle i (Finset.mem_range.mp hi))
    _ = 16*(b : ℝ)*η*(∑ i ∈ Finset.range j, lam i)+
        8*(b : ℝ)^2*(∑ i ∈ Finset.range j, lam i/((n : ℝ)*p i^2))+
        4*(b : ℝ)^2*(∑ i ∈ Finset.range j, (lam i)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16*(b : ℝ)*η by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hlD (show 0 ≤ 8*(b : ℝ)^2 by positivity)
      have h₃ := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*(b : ℝ)^2 by positivity)
      simp only [div_eq_mul_inv,mul_inv_rev] at h₂ h₃ ⊢
      norm_num only [invOf_eq_inv,inv_div,inv_one] at h₂
      nlinarith only [h₁,h₂,h₃]

end SharpTerminalLeave
end
end

end OAI
