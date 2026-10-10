import OAI.Probability.ThorpShuffle.ConvolutionBounds

namespace OAI

universe uX uY uΩ uI uG uH uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Trim
open scoped Classical

variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

def push (μ : X → ℝ) (f : X → Y) (y : Y) : ℝ := ∑ x, if f x = y then μ x else 0

omit [Fintype Y] in
lemma push_nonneg (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : X → Y) (y : Y) :
    0 ≤ push μ f y := Finset.sum_nonneg (fun x _ => by split_ifs <;> first | exact hμ _ | exact le_rfl)

lemma push_sum (μ : X → ℝ) (f : X → Y) : ∑ y, push μ f y = ∑ x, μ x := by
  unfold push
  rw [Finset.sum_comm]
  simp

lemma push_test (μ : X → ℝ) (f : X → Y) (s : Y → ℝ) :
    ∑ y, push μ f y * s y = ∑ x, μ x * s (f x) := by
  unfold push
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
lemma push_fairMass {Ω : Type uΩ} [Fintype Ω] (a : Ω → X) (f : X → Y) :
    push (fairMass a) f = fairMass (f ∘ a) := by
  funext y
  have he (x : X) : (if f x = y then fairMass a x else 0) =
      (∑ ω, if a ω = x then (if f x = y then (1:ℝ) else 0) else 0) / Fintype.card Ω := by
    by_cases h : f x = y <;> simp [h, fairMass]
  unfold push
  simp_rw [he]
  rw [← Finset.sum_div]
  unfold fairMass
  congr 1
  rw [Finset.sum_comm]
  simp

lemma push_bad_mass (μ υ : X → ℝ) (f : X → Y)
    (hm : ∑ x, μ x = ∑ x, υ x) :
    (∑ x, if 2 * push υ f (f x) < push μ f (f x) then μ x else 0) ≤
      2 * tv (push μ f) (push υ f) := by
  let s := Finset.univ.filter (fun y => 2 * push υ f y < push μ f y)
  have he : (∑ x, if 2 * push υ f (f x) < push μ f (f x) then μ x else 0) =
      ∑ y ∈ s, push μ f y := by
    rw [Finset.sum_filter]
    have ht := push_test μ f (fun y => if 2 * push υ f y < push μ f y then 1 else 0)
    simpa only [mul_ite, mul_one, mul_zero] using ht.symm
  have ht := sum_sub_le_tv (push μ f) (push υ f) (by simp only [push_sum, hm]) s
  have hs : ∑ y ∈ s, push μ f y ≤ 2 * ∑ y ∈ s, (push μ f y - push υ f y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y hy => by have hh := (Finset.mem_filter.mp hy).2; linarith)
  rw [he]
  linarith

lemma uniform_eq_fairMass_id : (fun _ : X => (Fintype.card X : ℝ)⁻¹) = fairMass id := by
  funext x
  simp [fairMass]

variable {I : Type uI} [Fintype I]
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

def cosetMass (ψ : (I → H) →* G) (μ : G → ℝ) (i : I) (g : G) : ℝ :=
  ∑ h, μ (g * ψ (Pi.mulSingle i h))

omit [Fintype I] [Fintype G] in
lemma cosetMass_right (ψ : (I → H) →* G) (μ : G → ℝ) (i : I) (g : G) (a : H) :
    cosetMass ψ μ i (g * ψ (Pi.mulSingle i a)) = cosetMass ψ μ i g := by
  unfold cosetMass
  have he (h : H) : g * ψ (Pi.mulSingle i a) * ψ (Pi.mulSingle i h) =
      g * ψ (Pi.mulSingle i (a * h)) := by rw [Pi.mulSingle_mul, map_mul, mul_assoc]
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.mulLeft a) (fun h => μ (g * ψ (Pi.mulSingle i h)))

def good (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : Prop :=
  ∀ i, cosetMass ψ μ i g ≤ 2 * ((Fintype.card H : ℝ) / Fintype.card G)

def discarded (ψ : (I → H) →* G) (μ : G → ℝ) : ℝ :=
  ∑ g, if good ψ μ g then 0 else μ g

def kept (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : ℝ :=
  if good ψ μ g then μ g else 0

def normalized (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : ℝ :=
  kept ψ μ g / (1 - discarded ψ μ)

omit [Fintype I] in
lemma discarded_nonneg (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) :
    0 ≤ discarded ψ μ := Finset.sum_nonneg (fun g _ => by split_ifs <;> first | exact hμ _ | exact le_rfl)

omit [Fintype I] in
lemma kept_add_discarded (ψ : (I → H) →* G) (μ : G → ℝ) :
    (∑ g, kept ψ μ g) + discarded ψ μ = ∑ g, μ g := by
  rw [discarded, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  unfold kept
  split_ifs <;> ring

lemma discarded_bound (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (A : I → Type uA) [∀ i, Fintype (A i)] (f : ∀ i, G → A i)
    (hM : ∀ i g, push μ (f i) (f i g) = cosetMass ψ μ i g)
    (hU : ∀ i g, push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) =
      (Fintype.card H : ℝ) / Fintype.card G) :
    discarded ψ μ ≤ 2 * ∑ i, tv (push μ (f i)) (push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i)) := by
  have hu : (∑ _ : G, (Fintype.card G : ℝ)⁻¹) = 1 := by simp [Fintype.card_ne_zero]
  have hpoint (g : G) : (if good ψ μ g then 0 else μ g) ≤
      ∑ i, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
        then μ g else 0 := by
    simp only [hM, hU]
    by_cases hg : good ψ μ g
    · rw [ite_eq_left hg]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hμ _ | exact le_rfl)
    · rw [ite_eq_right hg]
      have ⟨i, hi⟩ : ∃ i, 2 * ((Fintype.card H : ℝ) / Fintype.card G) < cosetMass ψ μ i g := by
        simpa only [good, not_forall, not_le] using hg
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun i => if 2 * ((Fintype.card H : ℝ) / Fintype.card G) < cosetMass ψ μ i g then μ g else 0)
        (fun j _ => by split_ifs <;> first | exact hμ _ | exact le_rfl) (Finset.mem_univ i)
      simpa only [ite_eq_left hi] using hh
  calc
    _ ≤ ∑ g, ∑ i, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
          then μ g else 0 := Finset.sum_le_sum (fun g _ => hpoint g)
    _ = ∑ i, ∑ g, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
          then μ g else 0 := Finset.sum_comm
    _ ≤ ∑ i, 2 * tv (push μ (f i)) (push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i)) :=
      Finset.sum_le_sum (fun i _ => push_bad_mass _ _ (f i) (h1.trans hu.symm))
    _ = _ := by rw [Finset.mul_sum]

end Trim

namespace Trim
open scoped Classical
variable {I : Type uI} {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

lemma normalized_nonneg (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (hδ : discarded ψ μ < 1) (g : G) : 0 ≤ normalized ψ μ g := by
  unfold normalized kept
  exact div_nonneg (by split_ifs <;> first | exact hμ _ | exact le_rfl) (by linarith)

lemma normalized_sum (ψ : (I → H) →* G) (μ : G → ℝ) (h1 : ∑ g, μ g = 1)
    (hδ : discarded ψ μ < 1) : ∑ g, normalized ψ μ g = 1 := by
  have hk : ∑ g, kept ψ μ g = 1 - discarded ψ μ := by
    have hh := kept_add_discarded ψ μ
    rw [h1] at hh
    linarith
  simp only [normalized, ← Finset.sum_div, hk]
  exact div_self (by linarith)

lemma normalized_tv (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (hδ : discarded ψ μ < 1) :
    tv μ (normalized ψ μ) = discarded ψ μ := by
  have hden : 0 < 1 - discarded ψ μ := by linarith
  have hd0 := discarded_nonneg ψ μ hμ
  have hpt (g : G) : |μ g - normalized ψ μ g| =
      normalized ψ μ g - μ g + 2 * (if good ψ μ g then 0 else μ g) := by
    by_cases hg : good ψ μ g
    · have he : normalized ψ μ g = μ g / (1 - discarded ψ μ) := by simp only [normalized, kept, ite_eq_left hg]
      have hle : μ g ≤ normalized ψ μ g := by rw [he]; apply (le_div_iff₀ hden).mpr; nlinarith [hμ g]
      rw [abs_of_nonpos (sub_nonpos.mpr hle), ite_eq_left hg]
      ring
    · simp only [normalized, kept, ite_eq_right hg, zero_div, sub_zero, abs_of_nonneg (hμ g)]
      ring
  unfold tv
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    normalized_sum ψ μ h1 hδ, h1]
  change (1/2 : ℝ) * (1-1+2*discarded ψ μ) = discarded ψ μ
  ring

lemma normalized_coset (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (hδ : discarded ψ μ ≤ 1/2) (i : I) (g : G) :
    cosetMass ψ (normalized ψ μ) i g ≤ 4 * (Fintype.card H : ℝ) / Fintype.card G := by
  have hden : 0 < 1 - discarded ψ μ := by linarith
  have hu : 0 ≤ (Fintype.card H : ℝ) / Fintype.card G := by positivity
  by_cases hg : cosetMass ψ μ i g ≤ 2 * ((Fintype.card H : ℝ) / Fintype.card G)
  · have hle : cosetMass ψ (normalized ψ μ) i g ≤ cosetMass ψ μ i g / (1-discarded ψ μ) := by
      simp only [cosetMass, normalized, ← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ hden.le
      apply Finset.sum_le_sum
      intro h _
      unfold kept
      split_ifs <;> simp [hμ]
    apply hle.trans
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ 1-discarded ψ μ by linarith) (show 0 ≤ 4*((Fintype.card H : ℝ)/Fintype.card G) by positivity)
    rw [mul_div_assoc]
    nlinarith
  · have hz (h : H) : normalized ψ μ (g * ψ (Pi.mulSingle i h)) = 0 := by
      have hn : ¬ good ψ μ (g * ψ (Pi.mulSingle i h)) := by
        intro hh
        have hi := hh i
        rw [cosetMass_right] at hi
        exact hg hi
      simp only [normalized, kept, ite_eq_right hn, zero_div]
    simp only [cosetMass, hz, Finset.sum_const_zero]
    positivity

lemma normalized_bias (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (hδ : discarded ψ μ < 1) (χ : G → ℂ)
    (hχ : ∀ g, ‖χ g‖ ≤ 1) (hb : ∑ g, (μ g : ℂ) * χ g = 0) :
    ‖∑ g, (normalized ψ μ g : ℂ) * χ g‖ ≤ 2 * discarded ψ μ := by
  have he : (∑ g, (normalized ψ μ g : ℂ) * χ g) =
      ∑ g, ((normalized ψ μ g - μ g : ℝ) : ℂ) * χ g := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, hb, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ g, ‖((normalized ψ μ g - μ g : ℝ) : ℂ) * χ g‖ := norm_sum_le _ _
    _ ≤ ∑ g, |normalized ψ μ g - μ g| := by
      apply Finset.sum_le_sum
      intro g _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hχ g) (abs_nonneg (normalized ψ μ g - μ g))
    _ = 2 * tv μ (normalized ψ μ) := by simp only [tv, abs_sub_comm]; ring
    _ = _ := by rw [normalized_tv ψ μ hμ h1 hδ]

end Trim

end Thorp

end

end OAI
