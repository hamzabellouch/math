import OAI.Probability.RadialTransition.EnvelopeSupport

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def IsPacking (L : ℝ) (X : Finset Position) : Prop :=
  (∀ x ∈ X, x ∈ cube L) ∧ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)

theorem dist_lt_one_of_coordinate_half {x y : Position}
    (h : ∀ k : Fin 3, |x k - y k| < 1 / 2) : dist x y < 1 := by
  have hh : dist x y ^ 2 < 1 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hc (k : Fin 3) : dist (x k) (y k) ^ 2 < (1 / 4 : ℝ) := by
      rw [Real.dist_eq]
      have hp := h k
      nlinarith [abs_nonneg (x k - y k)]
    have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      Finset.univ_nonempty (fun k _ => hc k)
    norm_num at hs
    linarith
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem packing_card_bound {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  classical
  let f : X → (Fin 3 → Fin (⌊2 * L⌋₊ + 1)) := fun x k =>
    ⟨⌊2 * (x : Position) k⌋₊,
      Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [(hX.1 x x.property k).2]))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : Position) ≠ y := fun h => hne (Subtype.ext h)
    have hlo := hX.2 x x.property y y.property hne'
    have hhi : dist (x : Position) y < 1 := by
      apply dist_lt_one_of_coordinate_half
      intro k
      have he : ⌊2 * (x : Position) k⌋₊ = ⌊2 * (y : Position) k⌋₊ :=
        congrArg Fin.val (congrFun hxy k)
      have hx0 := (hX.1 x x.property k).1
      have hy0 := (hX.1 y y.property k).1
      have hxL := Nat.floor_le (show 0 ≤ 2 * (x : Position) k by positivity)
      have hyL := Nat.floor_le (show 0 ≤ 2 * (y : Position) k by positivity)
      have hxU := Nat.lt_floor_add_one (2 * (x : Position) k)
      have hyU := Nat.lt_floor_add_one (2 * (y : Position) k)
      rw [he] at hxL hxU
      apply abs_lt.mpr
      constructor <;> linarith
    linarith
  simpa using Fintype.card_le_of_injective f hf

theorem packing_card_set_bddAbove (L : ℝ) :
    BddAbove {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X} := by
  refine ⟨(⌊2 * L⌋₊ + 1) ^ 3, ?_⟩
  rintro n ⟨X, rfl, hX⟩
  exact packing_card_bound hX

theorem packingNumber_attained (L : ℝ) :
    ∃ X : Finset Position, X.card = packingNumber L ∧ IsPacking L X := by
  exact Nat.sSup_mem (s := {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X})
    ⟨0, ∅, by simp [IsPacking]⟩ (packing_card_set_bddAbove L)

theorem packing_card_le {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ packingNumber L :=
  le_csSup (packing_card_set_bddAbove L) ⟨X, rfl, hX⟩

theorem packingNumber_bound (L : ℝ) :
    packingNumber L ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained L
  simpa only [hcard] using packing_card_bound hX

theorem packingNumber_pos {L : ℝ} (hL : 0 ≤ L) : 0 < packingNumber L := by
  have hh : IsPacking L {0} := by
    constructor
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst x
      intro k
      simp [hL]
    · intro x hx y hy hne
      simp only [Finset.mem_singleton] at hx hy
      exact (hne (hx.trans hy.symm)).elim
  have := packing_card_le hh
  simp only [Finset.card_singleton] at this
  omega

def packingTranslate {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) (x : Position) : Position :=
  WithLp.toLp 2 (fun k => (j k : ℝ) * (s + 1) + x k)

@[simp] theorem packingTranslate_apply {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n)
    (x : Position) (k : Fin 3) : packingTranslate s j x k = (j k : ℝ) * (s + 1) + x k := rfl

theorem packingTranslate_mem_cube {n : ℕ} {s L : ℝ} (hs : 0 ≤ s)
    (hn : (n : ℝ) * (s + 1) ≤ L) (j : Fin 3 → Fin n)
    {x : Position} (hx : x ∈ cube s) : packingTranslate s j x ∈ cube L := by
  intro k
  have hj : (j k : ℝ) + 1 ≤ n := by exact_mod_cast (j k).isLt
  have hj0 : 0 ≤ (j k : ℝ) := by positivity
  have hx0 : 0 ≤ x k := (hx k).1
  have hh := mul_le_mul_of_nonneg_right hj (show 0 ≤ s + 1 by linarith)
  simp only [packingTranslate_apply]
  constructor
  · positivity
  · linarith [(hx k).2]

theorem packingTranslate_dist_same {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n)
    (x y : Position) : dist (packingTranslate s j x) (packingTranslate s j y) = dist x y := by
  simp only [dist_eq_norm]
  congr 1
  ext k
  simp only [PiLp.sub_apply, packingTranslate_apply]
  ring

theorem packingTranslate_separated {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {j k : Fin 3 → Fin n} (hjk : j ≠ k) {x y : Position}
    (hx : x ∈ cube s) (hy : y ∈ cube s) :
    1 ≤ dist (packingTranslate s j x) (packingTranslate s k y) := by
  have hcoord {j k : Fin 3 → Fin n} {x y : Position}
      (hx : x ∈ cube s) (hy : y ∈ cube s) (q : Fin 3) (h : j q < k q) :
      1 ≤ dist (packingTranslate s j x) (packingTranslate s k y) := by
    have hq : (j q : ℝ) + 1 ≤ (k q : ℝ) := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ s + 1 by linarith)
    have hlo : 1 ≤ packingTranslate s k y q - packingTranslate s j x q := by
      simp only [packingTranslate_apply]
      linarith [(hx q).2, (hy q).1]
    have hnorm := PiLp.norm_apply_le (packingTranslate s k y - packingTranslate s j x) q
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at hnorm
    calc
      1 ≤ packingTranslate s k y q - packingTranslate s j x q := hlo
      _ ≤ |packingTranslate s k y q - packingTranslate s j x q| := le_abs_self _
      _ ≤ ‖packingTranslate s k y - packingTranslate s j x‖ := hnorm
      _ = dist (packingTranslate s j x) (packingTranslate s k y) := by rw [← dist_eq_norm, dist_comm]
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hjk
  rcases lt_or_gt_of_ne hq with h | h
  · exact hcoord hx hy q h
  · simpa only [dist_comm] using hcoord hy hx q h

theorem packingNumber_replication {s L : ℝ} (hs : 0 ≤ s) (n : ℕ)
    (hn : (n : ℝ) * (s + 1) ≤ L) :
    n ^ 3 * packingNumber s ≤ packingNumber L := by
  classical
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained s
  let f : (Fin 3 → Fin n) × X → Position := fun a => packingTranslate s a.1 a.2
  have hsep (a b : (Fin 3 → Fin n) × X) (hab : a ≠ b) : 1 ≤ dist (f a) (f b) := by
    by_cases hj : a.1 = b.1
    · have hx : (a.2 : Position) ≠ b.2 := by
        intro hx
        apply hab
        exact Prod.ext hj (Subtype.ext hx)
      dsimp [f]
      rw [hj, packingTranslate_dist_same]
      exact hX.2 _ a.2.property _ b.2.property hx
    · exact packingTranslate_separated hs hj (hX.1 _ a.2.property) (hX.1 _ b.2.property)
  have hfinj : Function.Injective f := by
    intro a b h
    by_contra hab
    have := hsep a b hab
    norm_num [h] at this
  let Y := Finset.univ.image f
  have hYcard : Y.card = n ^ 3 * packingNumber s := by
    rw [Finset.card_image_of_injective _ hfinj]
    simp [hcard]
  have hY : IsPacking L Y := by
    constructor
    · intro y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      exact packingTranslate_mem_cube hs hn a.1 (hX.1 _ a.2.property)
    · intro y hy z hz hyz
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
      exact hsep a b (fun hab => hyz (congrArg f hab))
  rw [← hYcard]
  exact packing_card_le hY

def packingDensity : ℝ :=
  sSup {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3}

theorem packing_ratio_bound {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ 8 := by
  have hc : (packingNumber s : ℝ) ≤ ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 := by
    exact_mod_cast packingNumber_bound s
  have hf := Nat.floor_le (show 0 ≤ 2 * s by positivity)
  have hg : ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := by
    gcongr
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (s + 1) ^ 3)).mpr
  nlinarith [hc.trans hg]

theorem packing_ratios_bdd :
    BddAbove {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3} := by
  refine ⟨8, ?_⟩
  rintro r ⟨s, hs, rfl⟩
  exact packing_ratio_bound hs

theorem packing_ratios_nonempty :
    ({r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3}).Nonempty :=
  ⟨_, 0, le_rfl, rfl⟩

theorem packing_ratio_le_density {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ packingDensity :=
  le_csSup packing_ratios_bdd ⟨s, hs, rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have h := packing_ratio_le_density (s := 0) le_rfl
  have hp : (0 : ℝ) < packingNumber 0 := by exact_mod_cast packingNumber_pos (L := 0) le_rfl
  norm_num at h
  exact hp.trans_le h

theorem packing_lower_approximation {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun L : ℝ => ((⌊L / (s + 1)⌋₊ : ℝ) / L) ^ 3 * packingNumber s)
      atTop (nhds ((packingNumber s : ℝ) / (s + 1) ^ 3)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ (s + 1)⁻¹ by positivity)).pow 3
  have h' := h.mul_const (packingNumber s : ℝ)
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using h'

theorem packing_lower_approximation_le {s L : ℝ} (hs : 0 ≤ s) (hL : 0 < L) :
    ((⌊L / (s + 1)⌋₊ : ℝ) / L) ^ 3 * packingNumber s ≤
      (packingNumber L : ℝ) / L ^ 3 := by
  have hn : (⌊L / (s + 1)⌋₊ : ℝ) * (s + 1) ≤ L := by
    apply (le_div_iff₀ (by positivity : 0 < s + 1)).mp
    exact Nat.floor_le (by positivity)
  have h := packingNumber_replication hs ⌊L / (s + 1)⌋₊ hn
  have hr : (⌊L / (s + 1)⌋₊ : ℝ) ^ 3 * packingNumber s ≤ packingNumber L := by
    exact_mod_cast h
  calc
    _ = ((⌊L / (s + 1)⌋₊ : ℝ) ^ 3 * packingNumber s) / L ^ 3 := by ring
    _ ≤ (packingNumber L : ℝ) / L ^ 3 := div_le_div_of_nonneg_right hr (by positivity)

theorem packing_upper_approximation_le {L : ℝ} (hL : 0 < L) :
    (packingNumber L : ℝ) / L ^ 3 ≤ packingDensity * (1 + L⁻¹) ^ 3 := by
  have h := packing_ratio_le_density hL.le
  have h' : (packingNumber L : ℝ) ≤ packingDensity * (L + 1) ^ 3 :=
    (div_le_iff₀ (by positivity : 0 < (L + 1) ^ 3)).mp h
  apply (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr
  calc
    _ ≤ packingDensity * (L + 1) ^ 3 := h'
    _ = packingDensity * (1 + L⁻¹) ^ 3 * L ^ 3 := by field_simp

theorem packingDensity_limit : IsPackingDensity packingDensity := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, ⟨s, hs, rfl⟩, har⟩ :=
      (lt_csSup_iff packing_ratios_bdd packing_ratios_nonempty).mp ha
    have he := (packing_lower_approximation hs).eventually_const_lt har
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with L hlow hL
    exact hlow.trans_le (packing_lower_approximation_le hs hL)
  · intro a ha
    have hu : Tendsto (fun L : ℝ => packingDensity * (1 + L⁻¹) ^ 3)
        atTop (nhds packingDensity) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero).pow 3
      simpa using h.const_mul packingDensity
    filter_upwards [hu.eventually_lt_const ha, eventually_gt_atTop (0 : ℝ)] with L hhi hL
    exact (packing_upper_approximation_le hL).trans_lt hhi

end RadialTransition

end

end OAI
