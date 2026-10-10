import OAI.Geometry.HeilbronnTriangle.AnisotropicGeometry
import OAI.Geometry.HeilbronnTriangle.AnisotropicDyadic
import OAI.Geometry.HeilbronnTriangle.PlaneFiberAssembly
import OAI.Geometry.HeilbronnTriangle.IntegerNormalGroups
import OAI.Geometry.HeilbronnTriangle.AnisotropicPlaneData

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

abbrev Triple := PlaneFiberAssembly.Triple

theorem thick_fiber_card_le
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ)
    (R₁ R₂ R₃ : ℝ) (h₂₁ : R₂ ≤ R₁) (h₃₂ : R₃ ≤ R₂)
    (hlarge : d.second ≤ R₃)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 / length y ^ 3 := by
  have h := PlaneFiberAssembly.triple_count_of_plane_counts S y t R₁ R₂ R₃
    (36 * Real.pi * R₁ ^ 2 / length y)
    (9 * Real.pi * R₂ ^ 2 / length y)
    (9 * Real.pi * R₃ ^ 2 / length y)
    (by positivity) (by positivity) hdet hcross hplane hnorm
    (fun T center hT => affine_plane_card_le y d T center R₁
      (hlarge.trans (h₃₂.trans h₂₁)) (fun v hv => (hT v hv).2)
      (fun v hv w hw => by rw [sub_dotProduct, (hT v hv).1, (hT w hw).1, sub_self]))
    (fun T hT => d.large_count T R₂ (hlarge.trans h₃₂) hT)
    (fun T hT => d.large_count T R₃ hlarge hT)
  convert h using 1; ring

theorem thin_fiber_card_le
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ)
    (R₁ R₂ R₃ : ℝ) (h₂₁ : R₂ ≤ R₁)
    (hlarge : d.second ≤ R₂) (hfirst : d.first ≤ R₃) (hthin : R₃ < d.second)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 972 * Real.pi ^ 2 * R₁ ^ 2 * R₂ ^ 2 * R₃ /
      (length y ^ 2 * d.first) := by
  have h := PlaneFiberAssembly.triple_count_of_plane_counts S y t R₁ R₂ R₃
    (36 * Real.pi * R₁ ^ 2 / length y)
    (9 * Real.pi * R₂ ^ 2 / length y) (3 * R₃ / d.first)
    (by positivity) (by positivity) hdet hcross hplane hnorm
    (fun T center hT => affine_plane_card_le y d T center R₁
      (hlarge.trans h₂₁) (fun v hv => (hT v hv).2)
      (fun v hv w hw => by rw [sub_dotProduct, (hT v hv).1, (hT w hw).1, sub_self]))
    (fun T hT => d.large_count T R₂ hlarge hT)
    (fun T hT => d.small_count T R₃ hfirst hthin hT)
  convert h using 1; ring

theorem scales_le_of_nonempty
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ) (ht : t ≠ 0)
    (R₂ R₃ : ℝ) (h₃₂ : R₃ ≤ R₂) (hS : S.Nonempty)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    d.first ≤ R₃ ∧ d.second ≤ R₂ := by
  obtain ⟨x, hx⟩ := hS
  have hc : x.2.1 ⨯₃ x.2.2 ≠ 0 := by
    intro hc
    apply ht
    have h := hdet x hx
    simpa [hc] using h.symm
  have hv : x.2.2 ≠ 0 := by
    intro hv
    apply hc
    simp [hv]
  refine ⟨(d.first_le _ (hplane x hx).2 hv).trans (hnorm x hx).2, ?_⟩
  exact (d.second_le _ _ (hplane x hx).1 (hplane x hx).2 hc).trans
    (max_le (hnorm x hx).1 ((hnorm x hx).2.trans h₃₂))

theorem thin_shell_sum_le
    (S : Finset IntVector) (first weight : IntVector → ℝ)
    (R₁ R₂ R₃ U Y C₀ C₁ : ℝ)
    (hU : 0 < U) (hY : 0 < Y) (hR₃ : 0 ≤ R₃) (hUR : U ≤ R₃)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcard : (S.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2)
    (hrange : ∀ y ∈ S, U ≤ first y ∧ Y ≤ length y)
    (hweight : ∀ y ∈ S, weight y ≤
      C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y)) :
    ∑ y ∈ S, weight y ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by
  have hB : 0 ≤ C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by positivity
  calc
    ∑ y ∈ S, weight y ≤
        ∑ _y ∈ S, C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by
      apply Finset.sum_le_sum
      intro y hy
      apply (hweight y hy).trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hY.le (hrange y hy).2 2)
        (hrange y hy).1 hU.le (sq_nonneg _)
    _ = (S.card : ℝ) * (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) := by simp
    _ ≤ (C₀ * U ^ 2 * Y ^ 2) *
        (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) :=
      mul_le_mul_of_nonneg_right hcard hB
    _ = (C₀ * C₁) * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
        (R₂ ^ 2 / Y) * (R₃ / U) := by field_simp
    _ ≤ (C₀ * C₁) * (R₁ * R₂ * R₃) ^ 2 :=
      thin_normal_group_numeric hU hY hR₃ hUR (mul_nonneg hC₀ hC₁)

theorem thin_normal_sum_le
    (S : Finset IntVector) (first weight : IntVector → ℝ)
    (R₁ R₂ R₃ C₀ C₁ : ℝ)
    (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃)
    (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hweight0 : ∀ y ∈ S, 0 ≤ weight y)
    (hrange : ∀ y ∈ S, 1 ≤ first y ∧ first y ≤ R₃ ∧
      1 ≤ length y ∧ length y ≤ R₂ * R₃)
    (hweight : ∀ y ∈ S, weight y ≤
      C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y))
    (hgroup : ∀ (T : Finset IntVector), T ⊆ S → ∀ U Y : ℝ,
      1 ≤ U → 1 ≤ Y →
      (∀ y ∈ T, U ≤ first y ∧ first y ≤ 2 * U ∧
        Y ≤ length y ∧ length y ≤ 2 * Y) →
      (T.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2) :
    ∑ y ∈ S, weight y ≤
      2 * C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  classical
  have hprod : 1 ≤ R₂ * R₃ := by nlinarith
  have hA : 0 ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by positivity
  have h := sum_le_of_dyadic_shell_estimates S first length weight h₃ hprod hA
    hweight0 hrange (by
      intro i j
      let T := S.filter fun y => (2 : ℝ) ^ i ≤ first y ∧ first y < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ length y ∧ length y < 2 ^ (j + 1)
      have hU : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hY : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hT (y : IntVector) (hy : y ∈ T) :
          (2 : ℝ) ^ i ≤ first y ∧ first y ≤ 2 * 2 ^ i ∧
          (2 : ℝ) ^ j ≤ length y ∧ length y ≤ 2 * 2 ^ j := by
        obtain ⟨_, h₁, h₂, h₃, h₄⟩ := Finset.mem_filter.mp hy
        exact ⟨h₁, by simpa [pow_succ, mul_comm] using h₂.le,
          h₃, by simpa [pow_succ, mul_comm] using h₄.le⟩
      change ∑ y ∈ T, weight y ≤ _
      by_cases hne : T.Nonempty
      · obtain ⟨y, hy⟩ := hne
        exact thin_shell_sum_le T first weight R₁ R₂ R₃ _ _ C₀ C₁
          (by positivity) (by positivity) (by linarith)
          ((hT y hy).1.trans (hrange y (hTS hy)).2.1) hC₀ hC₁
          (hgroup T hTS _ _ hU hY hT)
          (fun z hz => ⟨(hT z hz).1, (hT z hz).2.2.1⟩)
          (fun z hz => hweight z (hTS hz))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simpa using hA)
  calc
    ∑ y ∈ S, weight y ≤
        (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
          ((Real.log (2 * R₃) / Real.log 2) *
          (Real.log (2 * (R₂ * R₃)) / Real.log 2)) := by
      simpa only [mul_assoc] using h
    _ ≤ (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
        (2 * (Real.log (2 * R₁) / Real.log 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadic_log_product_le h₂ h₃ h₂₁ h₃₁) hA
    _ = _ := by ring

theorem triple_card_le_of_normal_assignment
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    (S : Finset Triple) (normal : Triple → IntVector) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hprim : ∀ x ∈ S, IsPrimitive (normal x))
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • normal x)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ normal x = 0 ∧ x.2.2 ⬝ᵥ normal x = 0)
    (hnormal : ∀ x ∈ S, length (normal x) ≤ R₂ * R₃)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 35721000 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 *
      (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  classical
  let Y := S.image normal
  let F (y : IntVector) := S.filter (fun x => normal x = y)
  let weight (y : IntVector) : ℝ := (F y).card
  let data (y : IntVector) (hy : IsPrimitive y) : PlaneData y :=
    Classical.choice (hplanes y hy)
  let first (y : IntVector) := if hy : IsPrimitive y then (data y hy).first else 1
  let second (y : IntVector) := if hy : IsPrimitive y then (data y hy).second else 1
  have hY (y : IntVector) (hy : y ∈ Y) : IsPrimitive y ∧
      1 ≤ length y ∧ length y ≤ R₂ * R₃ ∧ (F y).Nonempty := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨hprim x hx, LatticeBox.one_le_norm_realVector (hprim x hx).ne_zero,
      hnormal x hx, ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩⟩
  have hFdet (y : IntVector) : ∀ x ∈ F y,
      x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t :=
    fun x hx => hdet x (Finset.mem_filter.mp hx).1
  have hFcross (y : IntVector) : ∀ x ∈ F y,
      ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y := by
    intro x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    simpa only [hxy] using hcross x hxS
  have hFplane (y : IntVector) : ∀ x ∈ F y,
      x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0 := by
    intro x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    simpa only [hxy] using hplane x hxS
  have hFnorm (y : IntVector) : ∀ x ∈ F y, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃ :=
    fun x hx => hnorm x (Finset.mem_filter.mp hx).1
  have hscale (y : IntVector) (hy : y ∈ Y) :
      1 ≤ first y ∧ first y ≤ R₃ ∧ second y ≤ R₂ := by
    have hp := (hY y hy).1
    have hs := scales_le_of_nonempty (F y) y (data y hp) t ht R₂ R₃ h₃₂
      (hY y hy).2.2.2 (hFdet y) (hFplane y) (fun x hx => (hFnorm y x hx).2)
    simpa only [first, second, dite_eq_left hp] using
      And.intro (data y hp).one_le_first hs
  let E := Y.filter (fun y => second y ≤ R₃)
  let T := Y.filter (fun y => ¬ second y ≤ R₃)
  have h₂ : 1 ≤ R₂ := h₃.trans h₃₂
  have h₁ : 1 ≤ R₁ := h₂.trans h₂₁
  have hRprod : 1 ≤ R₂ * R₃ := by nlinarith
  have hthin : ∑ y ∈ T, weight y ≤
      2 * (18000 * Real.pi) * (972 * Real.pi ^ 2) * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    apply thin_normal_sum_le T first weight R₁ R₂ R₃ _ _ h₂ h₃ h₂₁ (h₃₂.trans h₂₁)
      (by positivity) (by positivity)
    · intro y hy
      exact Nat.cast_nonneg _
    · intro y hy
      have hyY := (Finset.mem_filter.mp hy).1
      exact ⟨(hscale y hyY).1, (hscale y hyY).2.1,
        (hY y hyY).2.1, (hY y hyY).2.2.1⟩
    · intro y hy
      obtain ⟨hyY, hyt⟩ := Finset.mem_filter.mp hy
      have hp := (hY y hyY).1
      have hlarge : (data y hp).second ≤ R₂ := by
        simpa only [second, dite_eq_left hp] using (hscale y hyY).2.2
      have hfirst : (data y hp).first ≤ R₃ := by
        simpa only [first, dite_eq_left hp] using (hscale y hyY).2.1
      have hlow : R₃ < (data y hp).second := by
        simpa only [second, dite_eq_left hp] using lt_of_not_ge hyt
      simpa only [first, dite_eq_left hp, weight] using
        thin_fiber_card_le (F y) y (data y hp) t R₁ R₂ R₃ h₂₁
          hlarge hfirst hlow (hFdet y) (hFcross y) (hFplane y) (hFnorm y)
    · intro A hAT U Z hU hZ hA
      apply normal_shell_card_le hplanes hU (by linarith) A
      intro y hy
      have hyY := (Finset.mem_filter.mp (hAT hy)).1
      have hp := (hY y hyY).1
      refine ⟨hp, (hA y hy).2.2.2, data y hp, ?_, ?_⟩
      · simpa only [first, dite_eq_left hp] using (hA y hy).1
      · simpa only [first, dite_eq_left hp] using (hA y hy).2.1
  have heasy : ∑ y ∈ E, weight y ≤
      (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
        ((125 / Real.log 2) * Real.log (2 * (R₂ * R₃))) := by
    calc
      ∑ y ∈ E, weight y ≤ ∑ y ∈ E,
          (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) / length y ^ 3 := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨hyY, hye⟩ := Finset.mem_filter.mp hy
        have hp := (hY y hyY).1
        have hlarge : (data y hp).second ≤ R₃ := by
          simpa only [second, dite_eq_left hp] using hye
        exact thick_fiber_card_le (F y) y (data y hp) t R₁ R₂ R₃ h₂₁ h₃₂
          hlarge (hFdet y) (hFcross y) (hFplane y) (hFnorm y)
      _ = (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          ∑ y ∈ E, 1 / length y ^ 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (LatticeBox.reciprocal_cube_sum_le_log hRprod E (by
          intro y hy
          have h := hY y (Finset.mem_filter.mp hy).1
          exact ⟨h.1.ne_zero, h.2.2.1⟩)) (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogprod : 0 ≤ Real.log (2 * (R₂ * R₃)) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    exact Real.log_nonneg (by nlinarith)
  have hlog3 : 1 ≤ Real.log (2 * R₃) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * R₃)
  have hlogbound : Real.log (2 * (R₂ * R₃)) / Real.log 2 ≤
      2 * (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    exact (le_mul_of_one_le_left hlogprod hlog3).trans
      (dyadic_log_product_le h₂ h₃ h₂₁ (h₃₂.trans h₂₁))
  have heasy' : ∑ y ∈ E, weight y ≤
      250 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    calc
      ∑ y ∈ E, weight y ≤ _ := heasy
      _ = (125 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          (Real.log (2 * (R₂ * R₃)) / Real.log 2) := by ring
      _ ≤ (125 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          (2 * (Real.log (2 * R₁) / Real.log 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ = _ := by ring
  have hcard : (S.card : ℝ) = ∑ y ∈ Y, weight y := by
    dsimp only [weight, F]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := Y) (f := normal) (fun x hx => Finset.mem_image_of_mem normal hx))
  have hsplit : (∑ y ∈ E, weight y) + (∑ y ∈ T, weight y) =
      ∑ y ∈ Y, weight y := Finset.sum_filter_add_sum_filter_not Y _ _
  rw [hcard, ← hsplit]
  calc
    _ ≤ _ := add_le_add heasy' hthin
    _ = _ := by ring

theorem anisotropic_count_of_planeData
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    (S : Finset Triple) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ (35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2) *
      (R₁ * R₂ * R₃) ^ 2 * Real.log (2 * R₁) ^ 2 := by
  classical
  have hex : ∀ x : Triple, ∃ y : IntVector, x ∈ S →
      IsPrimitive y ∧ (∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y) ∧
      (x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0) ∧ length y ≤ R₂ * R₃ := by
    intro x
    by_cases hx : x ∈ S
    · have hnz : x.2.1 ⨯₃ x.2.2 ≠ 0 := by
        intro hc
        apply ht
        have hd := hdet x hx
        simpa [hc] using hd.symm
      obtain ⟨a, ha, y, hyp, hfactor, horth₁, horth₂, hyl, _⟩ :=
        CrossNormal.exists_bounded_primitive_cross_factor x.2.1 x.2.2 hnz
      refine ⟨y, fun _ => ⟨hyp, ⟨a, ne_of_gt ha, hfactor⟩, ⟨horth₁, horth₂⟩, ?_⟩⟩
      exact hyl.trans (mul_le_mul (hnorm x hx).2.1 (hnorm x hx).2.2
        (norm_nonneg _) ((norm_nonneg _).trans (hnorm x hx).2.1))
    · exact ⟨0, fun h => (hx h).elim⟩
  choose normal hnormal using hex
  have h := triple_card_le_of_normal_assignment hplanes S normal t ht
    R₁ R₂ R₃ h₃ h₃₂ h₂₁ hdet (fun x hx => (hnormal x hx).1)
    (fun x hx => (hnormal x hx).2.1) (fun x hx => (hnormal x hx).2.2.1)
    (fun x hx => (hnormal x hx).2.2.2) hnorm
  convert h using 1; simp only [div_pow]; ring

theorem anisotropic_count
    (S : Finset Triple) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ (35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2) *
      (R₁ * R₂ * R₃) ^ 2 * Real.log (2 * R₁) ^ 2 :=
  anisotropic_count_of_planeData exists_planeData S t ht R₁ R₂ R₃
    h₃ h₃₂ h₂₁ hdet hnorm

theorem anisotropic_constant_pos :
    0 < 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end Problem355.Anisotropic

end

end OAI
