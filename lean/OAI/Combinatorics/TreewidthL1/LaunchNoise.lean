import OAI.Combinatorics.TreewidthL1.Padding

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1
namespace LaunchNoise
open Metric
variable {V I : Type*} [MetricSpace V] [Fintype I]
noncomputable def bump (E : Set V) (r : ℝ) (x : V) : ℝ :=
  by
    classical
    exact if Eᶜ.Nonempty then min r (infDist x Eᶜ) else r
noncomputable def noise (E : I → Set V) (r U : I → ℝ) (x : V) : ℝ :=
  ∑ i, U i * bump (E i) (r i) x

lemma bump_lipschitz (E : Set V) (r : ℝ) : LipschitzWith 1 (bump E r) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases h : Eᶜ.Nonempty
  · simpa only [bump, h, ↓reduceIte] using
      ((lipschitz_infDist_pt (s := Eᶜ)).const_min r).dist_le_mul x y
  · simp [bump, h]

lemma bump_bounds (E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    0 ≤ bump E r x ∧ bump E r x ≤ r := by
  classical
  unfold bump
  split_ifs
  · exact ⟨le_min hr infDist_nonneg, min_le_left _ _⟩
  · exact ⟨hr, le_rfl⟩

lemma bump_zero (E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) (hx : x ∉ E) :
    bump E r x = 0 := by
  have h : Eᶜ.Nonempty := ⟨x, hx⟩
  simp [bump, h, infDist_zero_of_mem (show x ∈ Eᶜ from hx), hr]

lemma bump_le_dist (E : Set V) (r : ℝ) (x y : V) (hy : y ∉ E) :
    bump E r x ≤ dist x y := by
  have h : Eᶜ.Nonempty := ⟨y, hy⟩
  simp only [bump, h, ↓reduceIte]
  exact (min_le_right _ _).trans (infDist_le_dist_of_mem (show y ∈ Eᶜ from hy))

lemma bump_padding (E : Set V) (r : ℝ) (x : V) (a : ℝ)
    (har : a ≤ r) (hball : ball x a ⊆ E) : a ≤ bump E r x := by
  classical
  by_cases h : Eᶜ.Nonempty
  · simp only [bump, h, ↓reduceIte, le_min_iff]
    refine ⟨har, le_of_not_gt ?_⟩
    intro ht
    obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff h).mp ht
    exact hy (hball (by simpa [mem_ball, dist_comm] using hxy))
  · simp [bump, h, har]

theorem bump_properties (E : Set V) (r : ℝ) (hr : 0 ≤ r) :
    LipschitzWith 1 (bump E r) ∧
    (∀ x, 0 ≤ bump E r x ∧ bump E r x ≤ r) ∧
    (∀ x, x ∉ E → bump E r x = 0) ∧
    (∀ x y, y ∉ E → bump E r x ≤ dist x y) ∧
    (∀ x a, a ≤ r → ball x a ⊆ E → a ≤ bump E r x) :=
  ⟨bump_lipschitz E r, bump_bounds E r hr, bump_zero E r hr,
    bump_le_dist E r, bump_padding E r⟩

lemma noise_at (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (i : I) (x : V) (hx : x ∈ E i) :
    noise E r U x = U i * bump (E i) (r i) x := by
  classical
  unfold noise
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hxj : x ∉ E j := fun hxj => Set.disjoint_left.mp (hE hji) hxj hx
    simp [bump_zero _ _ (hr j) _ hxj]
  · simp

lemma noise_zero (E : I → Set V) (r U : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (x : V) (hx : ∀ i, x ∉ E i) : noise E r U x = 0 := by
  simp [noise, fun i => bump_zero (E i) (r i) (hr i) x (hx i)]

lemma noise_nonneg (E : I → Set V) (r U : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hU : ∀ i, 0 ≤ U i) (x : V) :
    0 ≤ noise E r U x := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hU i) (bump_bounds _ _ (hr i) x).1

lemma noise_upper (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) (i : I) (x : V) (hx : x ∈ E i) :
    noise E r U x ≤ r i := by
  rw [noise_at E r U hE hr i x hx]
  exact (mul_le_of_le_one_left (bump_bounds _ _ (hr i) x).1 (hU i).2).trans
    (bump_bounds _ _ (hr i) x).2

lemma noise_one_sided (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) (x y : V) :
    noise E r U x - noise E r U y ≤ dist x y := by
  classical
  by_cases hx : ∃ i, x ∈ E i
  · obtain ⟨i, hi⟩ := hx
    rw [noise_at E r U hE hr i x hi]
    by_cases hy : y ∈ E i
    · rw [noise_at E r U hE hr i y hy, ← mul_sub]
      have hb := (bump_lipschitz (E i) (r i)).dist_le_mul x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hb
      have hsub := (le_abs_self (bump (E i) (r i) x - bump (E i) (r i) y)).trans hb
      calc U i * (bump (E i) (r i) x - bump (E i) (r i) y)
          ≤ U i * dist x y := mul_le_mul_of_nonneg_left hsub (hU i).1
        _ ≤ dist x y := mul_le_of_le_one_left dist_nonneg (hU i).2
    · have h1 := bump_le_dist (E i) (r i) x y hy
      have h2 := noise_nonneg E r U hr (fun j => (hU j).1) y
      have h3 := mul_le_of_le_one_left (bump_bounds (E i) (r i) (hr i) x).1 (hU i).2
      linarith
  · have h0 := noise_zero E r U hr x (by simpa using hx)
    have h1 := noise_nonneg E r U hr (fun i => (hU i).1) y
    rw [h0]
    linarith [dist_nonneg (x := x) (y := y)]

theorem disjoint_noise (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (noise E r U) ∧
    (∀ x, 0 ≤ noise E r U x) ∧
    (∀ i x, x ∈ E i → noise E r U x ≤ r i) ∧
    (∀ x, (∀ i, x ∉ E i) → noise E r U x = 0) := by
  refine ⟨?_, noise_nonneg E r U hr (fun i => (hU i).1),
    noise_upper E r U hE hr hU, noise_zero E r U hr⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  constructor
  · have := noise_one_sided E r U hE hr hU y x
    rw [dist_comm] at this
    linarith
  · exact noise_one_sided E r U hE hr hU x y
end LaunchNoise
end BoundedTreewidthL1
/-! Two deterministic shifted dyadic grids. A fair choice has the same
one-half interior probability needed by ordinary launch noise. -/
namespace BoundedTreewidthL1.LaunchNoise
noncomputable def bandIndex (a t : ℝ) : ℤ := ⌊Real.logb 2 (t/a)⌋
noncomputable def bandLower (a t : ℝ) : ℝ := a * (2:ℝ) ^ bandIndex a t

noncomputable def gridFactor (b : Bool) : ℝ := if b then 3/2 else 1

lemma band_bounds (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    0 < bandLower a t ∧ bandLower a t ≤ t ∧ t < 2 * bandLower a t := by
  have hp : 0 < t/a := div_pos ht ha
  have hl := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hp).mp
    (Int.floor_le (Real.logb 2 (t/a)))
  have hu := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hp).mp
    (Int.lt_floor_add_one (Real.logb 2 (t/a)))
  simp only [Real.rpow_intCast] at hl
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_intCast, Real.rpow_one] at hu
  dsimp [bandLower, bandIndex]
  have hlow := (le_div_iff₀ ha).mp hl
  have hupp := (div_lt_iff₀ ha).mp hu
  exact ⟨mul_pos ha (zpow_pos (by norm_num) _), by nlinarith, by nlinarith⟩

lemma bandIndex_eq (a t : ℝ) (j : ℤ) (ha : 0 < a) (ht : 0 < t)
    (hl : a * (2:ℝ)^j ≤ t) (hu : t < 2 * (a * (2:ℝ)^j)) :
    bandIndex a t = j := by
  apply Int.floor_eq_iff.mpr
  have hp := div_pos ht ha
  constructor
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hp).mpr
    rw [Real.rpow_intCast]
    exact (le_div_iff₀ ha).mpr (by nlinarith)
  · apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hp).mpr
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_intCast, Real.rpow_one]
    exact (div_lt_iff₀ ha).mpr (by nlinarith)

lemma band_same (a t u : ℝ) (ha : 0 < a) (_ : 0 < t) (hu : 0 < u)
    (hlo : bandLower a t ≤ u) (hhi : u < 2 * bandLower a t) :
    bandIndex a u = bandIndex a t :=
  bandIndex_eq a u (bandIndex a t) ha hu hlo hhi

lemma gridFactor_pos (b : Bool) : 0 < gridFactor b := by cases b <;> norm_num [gridFactor]

/-- Every positive height lies well inside one of the two grids. -/
theorem two_grid_margin (t : ℝ) (ht : 0 < t) :
    ∃ b : Bool, t/8 ≤ t - bandLower (gridFactor b) t ∧
      t/8 ≤ 2 * bandLower (gridFactor b) t - t := by
  let j := bandIndex 1 t
  let L := bandLower 1 t
  have hb := band_bounds 1 t (by norm_num) ht
  change 0 < L ∧ L ≤ t ∧ t < 2*L at hb
  have hL : L = (2:ℝ)^j := by simp [L, bandLower, j]
  by_cases h₁ : t/8 ≤ t-L
  · by_cases h₂ : t/8 ≤ 2*L-t
    · exact ⟨false, by simpa [gridFactor, L] using h₁,
        by simpa [gridFactor, L] using h₂⟩
    · have heq : bandIndex (3/2) t = j := by
        apply bandIndex_eq _ _ _ (by norm_num) ht
        · rw [← hL]; linarith
        · rw [← hL]; linarith [hb.2.2]
      refine ⟨true, ?_, ?_⟩ <;> simp only [gridFactor, ↓reduceIte, bandLower, heq, ← hL]
      · linarith
      · linarith [hb.2.2]
  · have hp : (2:ℝ)^(j-1) = L/2 := by
      rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one, hL]
    have heq : bandIndex (3/2) t = j-1 := by
      apply bandIndex_eq _ _ _ (by norm_num) ht
      · rw [hp]; linarith [hb.2.1]
      · rw [hp]; linarith
    refine ⟨true, ?_, ?_⟩ <;> simp only [gridFactor, ↓reduceIte, bandLower, heq, hp]
    · linarith [hb.2.1]
    · linarith
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.FiniteProductLaw
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
noncomputable def mass (p : I → A → ℝ) (x : I → A) : ℝ := ∏ i, p i (x i)
lemma nonneg
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A] [DecidableEq I]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : I → A) :
    0 ≤ mass p x := Finset.prod_nonneg (fun i _ => hp i (x i))
lemma total (p : I → A → ℝ) (hp : ∀ i, (∑ a, p i a) = 1) :
    (∑ x, mass p x) = 1 := by
  classical
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]
lemma factor_pos
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A] [DecidableEq I]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (x : I → A) (hx : 0 < mass p x) (i : I) : 0 < p i (x i) := by
  by_contra h
  have hz : p i (x i) = 0 := le_antisymm (le_of_not_gt h) (hp _ _)
  have hh : mass p x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith
lemma event (p : I → A → ℝ) (hp : ∀ i, (∑ a, p i a) = 1)
    (j : I) (E : A → Prop) [DecidablePred E] :
    (∑ x, if E (x j) then mass p x else 0) = ∑ a, if E a then p j a else 0 := by
  classical
  let q : I → A → ℝ := fun i a => if i = j then (if E a then p i a else 0) else p i a
  have heq (x : I → A) : (if E (x j) then mass p x else 0) = ∏ i, q i (x i) := by
    by_cases hx : E (x j)
    · simp only [hx, ↓reduceIte, mass]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i; simp [q, hx]
      · simp [q, hij]
    · simp only [hx, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [q, hx]
  simp_rw [heq]
  rw [← Fintype.prod_sum]
  calc
    _ = ∑ a, q j a := by
      apply Finset.prod_eq_single j
      · intro i _ hij
        simpa [q, hij] using hp i
      · simp
    _ = _ := by simp [q]
end BoundedTreewidthL1.FiniteProductLaw

namespace BoundedTreewidthL1.LaunchNoise
open Metric Classical

def MetricPaddedSupply {V : Type*} [Fintype V] [DecidableEq V] [MetricSpace V]
    (α π : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ μ : (V → V) → ℝ,
    (∀ P, 0 ≤ μ P) ∧ (∑ P, μ P) = 1 ∧
    (∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r) ∧
    ∀ x, π ≤ ∑ P, if (∀ y, dist x y ≤ α*r → P y = P x) then μ P else 0

def GoodBump {V J : Type*} [MetricSpace V]
    (h : V → ℝ) (α η : ℝ) (φ : J → V → ℝ) (x : V) : Prop :=
  ∃ j, α/8 * η * h x ≤ φ j x ∧
    (∀ y, 0 ≤ φ j y) ∧ (∀ y, 4*η*h x < dist x y → φ j y = 0)

def HasOrdinaryBumps {V : Type*} [MetricSpace V]
    (h : V → ℝ) (α π η : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ μ : Fin n → ℝ, ∃ φ : Fin n → Fin m → V → ℝ,
    (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a) = 1 ∧
    (∀ a (U : Fin m → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2) ∧
    ∀ x, 0 < h x → π/2 ≤ ∑ a, if GoodBump h α η (φ a) x then μ a else 0
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.LaunchNoise
open Metric Classical
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

noncomputable def bandSet (h : V → ℝ) : Finset ℤ :=
  Finset.univ.image (fun bx : Bool × V => bandIndex (gridFactor bx.1) (h bx.2))

noncomputable def bandKey (h : V → ℝ) (b : Bool) (x : V) : ↥(bandSet h) :=
  ⟨bandIndex (gridFactor b) (h x), Finset.mem_image.mpr ⟨(b,x), Finset.mem_univ _, rfl⟩⟩

noncomputable def bandScale (b : Bool) (j : ℤ) (η : ℝ) : ℝ :=
  η * (gridFactor b * (2:ℝ)^j) / 2

noncomputable def locationSet (h : V → ℝ) (b : Bool)
    (P : ↥(bandSet h) → V → V) (i : ↥(bandSet h) × V) : Set V :=
  {x | 0 < h x ∧ bandIndex (gridFactor b) (h x) = (i.1 : ℤ) ∧ P i.1 x = i.2}

lemma locationSet_disjoint
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (P : ↥(bandSet h) → V → V) :
    Pairwise (fun i j => Disjoint (locationSet h b P i) (locationSet h b P j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have heq : i.1 = j.1 := Subtype.ext (hi.2.1.symm.trans hj.2.1)
  have hval : i.2 = j.2 := by rw [← hi.2.2, heq, hj.2.2]
  exact hij (Prod.ext heq hval)

lemma location_self
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (P : ↥(bandSet h) → V → V)
    (x : V) (hx : 0 < h x) :
    x ∈ locationSet h b P (bandKey h b x, P (bandKey h b x) x) := ⟨hx,rfl,rfl⟩

lemma bandScale_pos (b : Bool) (j : ℤ) (η : ℝ) (hη : 0 < η) :
    0 < bandScale b j η := by
  dsimp [bandScale]
  exact div_pos (mul_pos hη (mul_pos (gridFactor_pos b) (zpow_pos (by norm_num) j)))
    (by norm_num)

lemma bandScale_at
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (x : V) (η : ℝ) :
    bandScale b (bandKey h b x) η = η * bandLower (gridFactor b) (h x) / 2 := rfl

lemma bump_noise_bounds (h : V → ℝ) (h0 : ∀ x, 0 ≤ h x)
    (b : Bool) (P : ↥(bandSet h) → V → V) (η : ℝ) (hη : 0 < η)
    (U : ↥(bandSet h) × V → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U) ∧
    ∀ x, 0 ≤ noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U x ∧
      noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U x ≤ η*h x/2 := by
  have hr (i : ↥(bandSet h) × V) : 0 ≤ bandScale b i.1 η/2 :=
    (div_pos (bandScale_pos b i.1 η hη) (by norm_num)).le
  have hh := disjoint_noise (locationSet h b P) (fun i => bandScale b i.1 η/2) U
    (locationSet_disjoint h b P) hr hU
  refine ⟨hh.1, fun x => ⟨hh.2.1 x, ?_⟩⟩
  by_cases hx : 0 < h x
  · have hh' := hh.2.2.1 _ x (location_self h b P x hx)
    have hB := (band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx).2.1
    rw [bandScale_at] at hh'
    have hmul := mul_le_mul_of_nonneg_left hB hη.le
    nlinarith [h0 x, mul_nonneg hη.le (h0 x)]
  · have hn : ∀ i, x ∉ locationSet h b P i := fun i hi => hx hi.1
    rw [hh.2.2.2 x hn]
    exact div_nonneg (mul_nonneg hη.le (h0 x)) (by norm_num)

lemma location_ball (h : V → ℝ) (hh : LipschitzWith 1 h)
    (b : Bool) (P : ↥(bandSet h) → V → V) (α η : ℝ)
    (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (x : V) (hx : 0 < h x)
    (hmargin : h x/8 ≤ h x - bandLower (gridFactor b) (h x) ∧
      h x/8 ≤ 2*bandLower (gridFactor b) (h x) - h x)
    (hpad : ∀ y, dist x y ≤ α*bandScale b (bandKey h b x) η →
      P (bandKey h b x) y = P (bandKey h b x) x) :
    ball x (α*bandScale b (bandKey h b x) η) ⊆
      locationSet h b P (bandKey h b x, P (bandKey h b x) x) := by
  intro y hy
  have hdist : dist x y < α*bandScale b (bandKey h b x) η := by
    simpa [mem_ball, dist_comm] using hy
  have hb := band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx
  have hscale : α*bandScale b (bandKey h b x) η < h x/8 := by
    rw [bandScale_at]
    have h₁ := mul_le_mul_of_nonneg_left hb.2.1 hη.le
    have h₂ := mul_le_mul_of_nonneg_left h₁ hα.le
    have h₃ := mul_le_mul_of_nonneg_right hα8 (mul_nonneg hη.le hx.le)
    have h₄ := mul_lt_mul_of_pos_right hη4 hx
    nlinarith
  have hL := hh.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le] at hL
  have hxy : 0 < h y := by linarith [hL.2]
  refine ⟨hxy, ?_, hpad y hdist.le⟩
  exact band_same (gridFactor b) (h x) (h y) (gridFactor_pos b) hx hxy
    (by linarith [hL.2, hmargin.1]) (by linarith [hL.1, hmargin.2])

lemma good_location (h : V → ℝ) (hh : LipschitzWith 1 h)
    (b : Bool) (P : ↥(bandSet h) → V → V) (α η : ℝ)
    (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (hdiam : ∀ j x y, P j x = P j y → dist x y ≤ bandScale b j η)
    (x : V) (hx : 0 < h x)
    (hmargin : h x/8 ≤ h x - bandLower (gridFactor b) (h x) ∧
      h x/8 ≤ 2*bandLower (gridFactor b) (h x) - h x)
    (hpad : ∀ y, dist x y ≤ α*bandScale b (bandKey h b x) η →
      P (bandKey h b x) y = P (bandKey h b x) x) :
    GoodBump h α η (fun i => bump (locationSet h b P i) (bandScale b i.1 η/2)) x := by
  let j := bandKey h b x
  let i : ↥(bandSet h) × V := (j, P j x)
  have hp := bandScale_pos b j η hη
  have hb := band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx
  have hball := location_ball h hh b P α η hα hα8 hη hη4 x hx hmargin hpad
  have hcap : α*bandScale b j η ≤ bandScale b j η/2 := by nlinarith
  have hbump := bump_padding (locationSet h b P i) (bandScale b j η/2)
    x (α*bandScale b j η) hcap hball
  refine ⟨i, ?_, (fun y => (bump_bounds _ _ (by positivity) y).1), ?_⟩
  · dsimp [i]
    apply le_trans _ hbump
    change α/8*η*h x ≤ α*(η*bandLower (gridFactor b) (h x)/2)
    have hmul := mul_lt_mul_of_pos_left hb.2.2 (mul_pos hα hη)
    nlinarith [mul_pos (mul_pos hα hη) hx]
  · intro y hy
    apply bump_zero _ _ (by positivity)
    intro hmem
    have heq : P j x = P j y := hmem.2.2.symm
    have hd := hdiam j x y heq
    have hs : bandScale b j η ≤ η*h x/2 := by
      change η*bandLower (gridFactor b) (h x)/2 ≤ η*h x/2
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2.1 hη.le) (by norm_num)
    nlinarith [mul_pos hη hx]
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.LaunchNoise
open Classical Metric
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

lemma ordinary_bumps_reindex
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    {J Ω : Type} [Fintype J] [Fintype Ω]
    (h : V → ℝ) (α π η : ℝ) (μ : Ω → ℝ) (φ : Ω → J → V → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ1 : (∑ a, μ a) = 1)
    (hb : ∀ a (U : J → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2)
    (hg : ∀ x, 0 < h x → π/2 ≤ ∑ a, if GoodBump h α η (φ a) x then μ a else 0) :
    HasOrdinaryBumps h α π η := by
  let e := (Fintype.equivFin J).symm
  let d := (Fintype.equivFin Ω).symm
  refine ⟨Fintype.card Ω, Fintype.card J, μ ∘ d, (fun a j => φ (d a) (e j)),
    (fun a => hμ _), ?_, ?_, ?_⟩
  · simpa using (d.sum_comp μ).trans hμ1
  · intro a U hU
    have hh := hb (d a) (U ∘ e.symm) (fun j => hU _)
    have heq : (fun x => ∑ j, U j * φ (d a) (e j) x) =
        (fun x => ∑ j, (U ∘ e.symm) j * φ (d a) j x) := by
      funext x
      simpa using e.sum_comp (fun j => (U ∘ e.symm) j * φ (d a) j x)
    constructor
    · rw [heq]
      exact hh.1
    · intro x
      rw [show (∑ j, U j * φ (d a) (e j) x) =
        (∑ j, (U ∘ e.symm) j * φ (d a) j x) from congrFun heq x]
      exact hh.2 x
  · intro x hx
    have heq (a : Fin (Fintype.card Ω)) :
        GoodBump h α η (fun j => φ (d a) (e j)) x ↔ GoodBump h α η (φ (d a)) x := by
      constructor
      · rintro ⟨j,hj,hj0,hjS⟩; exact ⟨e j,hj,hj0,hjS⟩
      · rintro ⟨j,hj,hj0,hjS⟩
        refine ⟨e.symm j, ?_, ?_, ?_⟩ <;> simpa using ‹_›
    simp_rw [heq]
    have he := d.sum_comp (fun a => if GoodBump h α η (φ a) x then μ a else 0)
    exact (hg x hx).trans he.ge

noncomputable def locationMass (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (a : Bool × (↥(bandSet h) → V → V)) : ℝ :=
  (1/2) * FiniteProductLaw.mass (p a.1) a.2

lemma locationMass_nonneg
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ) (hp : ∀ b j P, 0 ≤ p b j P) :
    ∀ a, 0 ≤ locationMass h p a := by
  intro a
  exact mul_nonneg (by norm_num) (FiniteProductLaw.nonneg _ (hp a.1) _)

lemma locationMass_total
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (hp : ∀ b j, (∑ P, p b j P) = 1) :
    (∑ a, locationMass h p a) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [locationMass, ← Finset.mul_sum, FiniteProductLaw.total _ (hp _)]
  norm_num [Fintype.sum_bool]

lemma locationMass_event
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (hp : ∀ b j, (∑ P, p b j P) = 1) (b : Bool) (j : ↥(bandSet h))
    (E : (V → V) → Prop) :
    (∑ a : Bool × (↥(bandSet h) → V → V),
      if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) =
      (1/2) * ∑ P, if E P then p b j P else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  have heq (b' : Bool) :
      (∑ P, if b' = b ∧ E (P j) then locationMass h p (b',P) else 0) =
        if b' = b then (1/2) * ∑ P, if E P then p b j P else 0 else 0 := by
    by_cases he : b' = b
    · subst b'
      simp only [true_and, locationMass, ite_true]
      have he (q : ↥(bandSet h) → V → V) :
          (if E (q j) then (1/2:ℝ) * FiniteProductLaw.mass (p b) q else 0) =
            (1/2) * (if E (q j) then FiniteProductLaw.mass (p b) q else 0) := by
        split_ifs <;> ring
      simp_rw [he]
      rw [← Finset.mul_sum, FiniteProductLaw.event _ (hp b)]
    · simp [he]
  simp_rw [heq]
  simp

/-- Finite ordinary noise from a padded supply, which is available
unconditionally for the weighted graph metrics by `PaddedConstruction`. -/
theorem finite_ordinary_bumps
    (h : V → ℝ) (hh : LipschitzWith 1 h) (h0 : ∀ x, 0 ≤ h x)
    (α π η : ℝ) (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (hsupply : MetricPaddedSupply (V := V) α π) : HasOrdinaryBumps h α π η := by
  classical
  have hs (b : Bool) (j : ↥(bandSet h)) := hsupply (bandScale b j η) (bandScale_pos b j η hη)
  choose p hp hp1 hdiam hpad using hs
  let φ : (Bool × (↥(bandSet h) → V → V)) → (↥(bandSet h) × V) → V → ℝ :=
    fun a i => bump (locationSet h a.1 a.2 i) (bandScale a.1 i.1 η/2)
  apply ordinary_bumps_reindex h α π η (locationMass h p) φ
    (locationMass_nonneg h p hp) (locationMass_total h p hp1)
  · intro a U hU
    exact bump_noise_bounds h h0 a.1 a.2 η hη U hU
  · intro x hx
    obtain ⟨b,hmargin⟩ := two_grid_margin (h x) hx
    let j := bandKey h b x
    let E : (V → V) → Prop := fun P => ∀ y, dist x y ≤ α*bandScale b j η → P y = P x
    have hsum : (∑ a : Bool × (↥(bandSet h) → V → V),
        if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) =
        (1/2) * ∑ P, if E P then p b j P else 0 := by
      convert locationMass_event h p hp1 b j E using 1
      · apply Finset.sum_congr (by ext; simp)
        intro a _
        split_ifs <;> rfl
      · congr 1
        apply Finset.sum_congr (by ext; simp)
        intro P _
        split_ifs <;> rfl
    have hle : (∑ a : Bool × (↥(bandSet h) → V → V),
        if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) ≤
        ∑ a, if GoodBump h α η (φ a) x then locationMass h p a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      have hnonneg := locationMass_nonneg h p hp a
      by_cases ha : a.1 = b ∧ E (a.2 j)
      · rw [ite_eq_left ha]
        by_cases hpos : 0 < locationMass h p a
        · have hprod : 0 < FiniteProductLaw.mass (p a.1) a.2 := by
            dsimp [locationMass] at hpos
            linarith
          have hgood : GoodBump h α η (φ a) x := by
            have hda : ∀ j x y, a.2 j x = a.2 j y → dist x y ≤ bandScale a.1 j η := by
              intro j x y hxy
              exact hdiam a.1 j (a.2 j)
                (FiniteProductLaw.factor_pos _ (hp a.1) _ hprod j) x y hxy
            apply good_location h hh a.1 a.2 α η hα hα8 hη hη4 hda x hx
            · simpa [ha.1] using hmargin
            · simpa [ha.1, j, E] using ha.2
          rw [ite_eq_left hgood]
        · have hz : locationMass h p a = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
          simp [hz]
      · rw [ite_eq_right ha]
        split_ifs <;> positivity
    have hle2 : (1/2) * (∑ P, if E P then p b j P else 0) ≤
        ∑ a, if GoodBump h α η (φ a) x then locationMass h p a else 0 := by
      calc
        _ = ∑ a : Bool × (↥(bandSet h) → V → V),
          if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0 := hsum.symm
        _ ≤ _ := hle
    have hpπ := hpad b j x
    change π ≤ ∑ P, if E P then p b j P else 0 at hpπ
    have hh' := mul_le_mul_of_nonneg_left hpπ (by norm_num : (0:ℝ) ≤ 1/2)
    exact (by linarith : π/2 ≤ (1/2)*∑ P, if E P then p b j P else 0).trans hle2
end BoundedTreewidthL1.LaunchNoise

/-! The actual finite product probability space for the ordinary launch noise.
No random coefficient distribution or independence is supplied as an assumption.
-/
namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable
open scoped unitInterval ENNReal
noncomputable def locationLaw {n : ℕ} (μ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ a, ENNReal.ofReal (μ a) • Measure.dirac a
abbrev CoeffCube (m : ℕ) := Fin m → I
abbrev NoiseSpace (n m : ℕ) := I × (Fin n × CoeffCube m)
noncomputable def noiseLaw {n : ℕ} (m : ℕ) (μ : Fin n → ℝ) : Measure (NoiseSpace n m) :=
  (volume : Measure I).prod ((locationLaw μ).prod volume)
def noiseXi {n m : ℕ} (ω : NoiseSpace n m) : ℝ := 1 + (ω.1 : ℝ)
noncomputable def noiseV {V : Type*} {n m : ℕ} (φ : Fin n → Fin m → V → ℝ)
    (ω : NoiseSpace n m) (x : V) : ℝ := ∑ j, (ω.2.2 j : ℝ) * φ ω.2.1 j x
noncomputable def noiseG {V : Type*} {n m : ℕ} (h : V → ℝ)
    (φ : Fin n → Fin m → V → ℝ) (ω : NoiseSpace n m) (x : V) : ℝ :=
  noiseXi ω * h x + noiseV φ ω x

lemma locationLaw_apply {n : ℕ} (μ : Fin n → ℝ) (S : Set (Fin n)) :
    locationLaw μ S = ∑ a, if a ∈ S then ENNReal.ofReal (μ a) else 0 := by
  classical
  simp [locationLaw, Set.indicator, apply_ite]

lemma locationLaw_probability {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) : IsProbabilityMeasure (locationLaw μ) := by
  constructor
  rw [locationLaw_apply]
  simp only [Set.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a), hμ₁, ENNReal.ofReal_one]

lemma noiseLaw_probability {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) : IsProbabilityMeasure (noiseLaw m μ) := by
  let := locationLaw_probability μ hμ hμ₁
  unfold noiseLaw
  infer_instance

lemma noise_locationLaw {n m : ℕ} (μ : Fin n → ℝ) :
    Measure.map (fun ω : NoiseSpace n m => ω.2.1) (noiseLaw m μ) = locationLaw μ := by
  unfold noiseLaw
  change Measure.map (Prod.fst ∘ Prod.snd) _ = _
  rw [← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul, Measure.map_fst_prod]

lemma noise_goodProbability {n m : ℕ} (μ : Fin n → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (E : Fin n → Prop) :
    noiseLaw m μ {ω | E ω.2.1} = ENNReal.ofReal (∑ a, if E a then μ a else 0) := by
  classical
  have hm : MeasurableSet {a : Fin n | E a} := MeasurableSet.of_discrete
  change noiseLaw m μ ((Prod.fst ∘ Prod.snd) ⁻¹' {a : Fin n | E a}) = _
  rw [← Measure.map_apply (measurable_fst.comp measurable_snd) hm]
  change (Measure.map (fun ω : NoiseSpace n m => ω.2.1) (noiseLaw m μ)) {a | E a} = _
  rw [noise_locationLaw, locationLaw_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by split_ifs <;> simp [hμ])]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

lemma noiseXi_measurable {n m : ℕ} : Measurable (noiseXi (n := n) (m := m)) := by
  unfold noiseXi
  fun_prop

lemma noiseV_measurable {V : Type*} {n m : ℕ} (φ : Fin n → Fin m → V → ℝ) :
    Measurable (noiseV φ) := by
  apply Measurable.of_eval
  intro x
  unfold noiseV
  apply Finset.measurable_sum
  intro j _
  have hu : Measurable (fun ω : NoiseSpace n m => (ω.2.2 j : ℝ)) := by fun_prop
  have ha : Measurable (fun ω : NoiseSpace n m => φ ω.2.1 j x) :=
    (show Measurable (fun a : Fin n => φ a j x) from Measurable.of_discrete).comp
      (measurable_fst.comp measurable_snd)
  exact hu.mul ha

lemma noiseG_measurable {V : Type*} {n m : ℕ} (h : V → ℝ)
    (φ : Fin n → Fin m → V → ℝ) : Measurable (noiseG h φ) := by
  apply Measurable.of_eval
  intro x
  exact (noiseXi_measurable.mul_const (h x)).add ((measurable_pi_apply x).comp (noiseV_measurable φ))

lemma noiseXi_uniform {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    MeasurePreserving (fun ω : NoiseSpace n m => noiseXi ω - 1)
      (noiseLaw m μ) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let := locationLaw_probability μ hμ hμ₁
  simpa [noiseLaw, noiseXi, Function.comp_def, unitInterval] using
    (unitInterval.measurePreserving_coe.comp
      (measurePreserving_fst (μ := (volume : Measure I))
        (ν := (locationLaw μ).prod (volume : Measure (CoeffCube m)))))

lemma noiseXi_indep {V : Type*} {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (φ : Fin n → Fin m → V → ℝ) :
    IndepFun noiseXi (noiseV φ) (noiseLaw m μ) := by
  let := locationLaw_probability μ hμ hμ₁
  exact indepFun_prod (X := fun t : I => 1 + (t : ℝ)) (by fun_prop)
    (Y := fun ac : Fin n × CoeffCube m => fun x => ∑ j, (ac.2 j : ℝ) * φ ac.1 j x)
    (by
      apply Measurable.of_eval
      intro x
      apply Finset.measurable_sum
      intro j _
      have hu : Measurable (fun ac : Fin n × CoeffCube m => (ac.2 j : ℝ)) := by fun_prop
      have ha : Measurable (fun ac : Fin n × CoeffCube m => φ ac.1 j x) :=
        (show Measurable (fun a : Fin n => φ a j x) from Measurable.of_discrete).comp measurable_fst
      exact hu.mul ha)

lemma cube_uniform {m : ℕ} (j : Fin m) :
    MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  unitInterval.measurePreserving_coe.comp (measurePreserving_eval (fun _ : Fin m => (volume : Measure I)) j)

lemma cube_independent (m : ℕ) :
    iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume :=
  iIndepFun_pi (fun _ => measurable_subtype_coe.aemeasurable)

/-- Fresh independent randomness works with any previously constructed probability space. -/
lemma fresh_noise {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {V : Type*} {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (h : V → ℝ) (φ : Fin n → Fin m → V → ℝ) :
    IndepFun (fun ω : Ω × NoiseSpace n m => ω.1)
      (fun ω => noiseG h φ ω.2) (ν.prod (noiseLaw m μ)) := by
  let := noiseLaw_probability (m := m) μ hμ hμ₁
  exact indepFun_prod measurable_id (noiseG_measurable h φ)

lemma noiseXi_uniform_interval {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m μ)
      (volume.restrict (Set.Icc (1:ℝ) 2)) := by
  have he : (fun x : ℝ => 1 + x) ⁻¹' Set.Icc 1 2 = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  have ht := (measurePreserving_add_left (volume : Measure ℝ) 1).restrict_preimage
    (s := Set.Icc 1 2) measurableSet_Icc
  rw [he] at ht
  simpa [Function.comp_def] using ht.comp (noiseXi_uniform (m := m) μ hμ hμ₁)

lemma noise_deterministic {V : Type*} [MetricSpace V] {n m : ℕ}
    (h : V → ℝ) (hh : LipschitzWith 1 h) (hhn : ∀ x, 0 ≤ h x)
    (η : ℝ) (hη : η < 1/4) (φ : Fin n → Fin m → V → ℝ)
    (hv : ∀ a (U : Fin m → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2)
    (ω : NoiseSpace n m) :
    LipschitzWith 1 (noiseV φ ω) ∧
      (∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h φ ω) ∧
      ∀ x, h x ≤ noiseG h φ ω x ∧ noiseG h φ ω x ≤ (5/2) * h x := by
  obtain ⟨hlip, hbound⟩ := hv ω.2.1 (fun j => (ω.2.2 j : ℝ)) (fun j => (ω.2.2 j).property)
  change LipschitzWith 1 (noiseV φ ω) at hlip
  change ∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2 at hbound
  have hξ : 1 ≤ noiseXi ω ∧ noiseXi ω ≤ 2 := by
    have hp := ω.1.property
    dsimp [noiseXi]
    constructor <;> linarith [hp.1, hp.2]
  refine ⟨hlip, hbound, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hhl : |h x - h y| ≤ dist x y := by simpa [Real.dist_eq] using hh.dist_le_mul x y
    have hvl : |noiseV φ ω x - noiseV φ ω y| ≤ dist x y := by
      simpa [Real.dist_eq] using hlip.dist_le_mul x y
    rw [Real.dist_eq]
    calc
      |noiseG h φ ω x - noiseG h φ ω y| =
          |noiseXi ω * (h x - h y) + (noiseV φ ω x - noiseV φ ω y)| := by
            congr 1
            dsimp [noiseG]
            ring
      _ ≤ |noiseXi ω * (h x - h y)| + |noiseV φ ω x - noiseV φ ω y| := abs_add_le _ _
      _ = noiseXi ω * |h x - h y| + |noiseV φ ω x - noiseV φ ω y| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ noiseXi ω)]
      _ ≤ 2 * dist x y + dist x y := add_le_add
        ((mul_le_mul_of_nonneg_left hhl (by linarith)).trans
          (mul_le_mul_of_nonneg_right hξ.2 dist_nonneg)) hvl
      _ = (3 : NNReal) * dist x y := by norm_num; ring
  · intro x
    have hz := hhn x
    have hb := hbound x
    dsimp [noiseG]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hξ.1 hz]
    · nlinarith [mul_le_mul_of_nonneg_right hξ.2 hz, mul_nonneg (le_of_lt (sub_pos.mpr hη)) hz]
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
/-- Complete finite ordinary-noise sampler; its law is the displayed product
of a fresh uniform xi, a finite location law, and independent uniform amplitudes. -/
def HasOrdinaryNoise {V : Type*} [MetricSpace V]
    (h : V → ℝ) (α π η : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ μ : Fin n → ℝ, ∃ φ : Fin n → Fin m → V → ℝ,
    (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a) = 1 ∧
    IsProbabilityMeasure (noiseLaw m μ) ∧
    Measurable (noiseG h φ) ∧
    MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m μ)
      (volume.restrict (Set.Icc (1:ℝ) 2)) ∧
    IndepFun noiseXi (noiseV φ) (noiseLaw m μ) ∧
    (∀ ω : NoiseSpace n m,
      LipschitzWith 1 (noiseV φ ω) ∧
      (∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h φ ω) ∧
      ∀ x, h x ≤ noiseG h φ ω x ∧ noiseG h φ ω x ≤ (5/2) * h x) ∧
    (∀ x, 0 < h x → ENNReal.ofReal (π/2) ≤
      noiseLaw m μ {ω | GoodBump h α η (φ ω.2.1) x}) ∧
    (∀ j : Fin m, MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1))) ∧
    iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

theorem metric_ordinary_noise
    (h : V → ℝ) (hh : LipschitzWith 1 h) (h0 : ∀ x, 0 ≤ h x)
    (α π η : ℝ) (hα : 0 < α) (hα8 : α ≤ 1/8) (_ : 0 < π)
    (hη : 0 < η) (hη4 : η < 1/4)
    (hsupply : MetricPaddedSupply (V := V) α π) : HasOrdinaryNoise h α π η := by
  classical
  obtain ⟨n,m,μ,φ,hμ,hμ₁,hv,hgood⟩ :=
    finite_ordinary_bumps h hh h0 α π η hα hα8 hη hη4 hsupply
  refine ⟨n,m,μ,φ,hμ,hμ₁,noiseLaw_probability μ hμ hμ₁,
    noiseG_measurable h φ,noiseXi_uniform_interval μ hμ hμ₁,
    noiseXi_indep μ hμ hμ₁ φ,?_,?_,cube_uniform,cube_independent m⟩
  · exact noise_deterministic h hh h0 η hη4 φ hv
  · intro x hx
    rw [noise_goodProbability (m := m) μ hμ (fun a => GoodBump h α η (φ a) x)]
    exact ENNReal.ofReal_le_ofReal (hgood x hx)
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
/-- Uniform graph-metric input; the distance is definitionally the original
positive-weight shortest-path distance, with no edge-ratio restriction. -/
theorem graph_ordinary_noise (k : ℕ) (hk : 2 ≤ k) :
    ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
        (G : SimpleGraph V) (hG : G.Connected) (_ : HasTreeDecomposition G k)
        (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e),
        let := weightedMetricSpace G ℓ hG hℓ
        ∀ (A : Set V), A.Nonempty → ∀ η : ℝ, 0 < η → η < 1/4 →
          HasOrdinaryNoise (fun x => Metric.infDist x A) α π η := by
  classical
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hpad⟩ := PaddedPartitions.uniform_padded_partitions k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG hT ℓ hℓ metric
  let _ : MetricSpace V := metric
  intro A hA η hη hη4
  have hsupply : MetricPaddedSupply (V := V) α π := by
    intro r hr
    obtain ⟨μ,hμ,hμ1,hdiam,hprob⟩ := hpad V G hG hT ℓ hℓ r hr
    refine ⟨μ,hμ,hμ1,hdiam,?_⟩
    intro x
    apply le_trans (hprob x)
    apply le_of_eq
    unfold PaddedPartitions.paddingProbability
    apply Finset.sum_congr (by ext; simp)
    intro P _
    have hd (u v : V) : dist u v = shortestPathDistance G ℓ u v := rfl
    simp only [PaddedPartitions.PaddedAt, hd]
    exact congrArg (fun d : Decidable
      (∀ y : V, shortestPathDistance G ℓ x y ≤ α * r → P y = P x) =>
        @ite ℝ _ d (μ P) 0) (Subsingleton.elim _ _)
  exact metric_ordinary_noise (fun x => Metric.infDist x A)
    (Metric.lipschitz_infDist_pt A) (fun x => Metric.infDist_nonneg) α π η hα hα8 hπ hη hη4 hsupply
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.TreeCache
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

lemma fresh_eq_singleton (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :
    AnchorTreeParticles.fresh (RootedTree.forest T hT root)
      (active T hT root B D k d J) i = {i} := by
  classical
  unfold AnchorTreeParticles.fresh AnchorTreeParticles.retained
  cases hp : (RootedTree.forest T hT root).parent i with
  | none =>
    have hi : i = root := by
      by_contra hi
      simp [RootedTree.forest,hi] at hp
    subst i
    simp only [Option.elim_none,Finset.sdiff_empty]
    exact active_root T hT root B D k d J
  | some p =>
    simp only [Option.elim_some]
    convert active_sdiff_parent T hT root B D k d J hp using 1
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto

lemma origin_self (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    (i a : I) (ha : a ∈ active T hT root B D k d J i) :
    AnchorTreeParticles.origin (RootedTree.forest T hT root)
      (active T hT root B D k d J) root i a = a := by
  have hf := AnchorTreeParticles.origin_fresh (RootedTree.forest T hT root)
    (active T hT root B D k d J) root i a ha
  rw [fresh_eq_singleton,Finset.mem_singleton] at hf
  exact hf.symm
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1
open MeasureTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type*} [Fintype V]

lemma bagDistance_eq_infDist [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x : V) :
    let := weightedMetricSpace G ℓ hG hℓ
    bagDistance G ℓ A hA x = Metric.infDist x (A : Set V) := by
  let := weightedMetricSpace G ℓ hG hℓ
  apply le_antisymm
  · apply (Metric.le_infDist (show (A : Set V).Nonempty from hA)).mpr
    intro a ha
    exact bagDistance_le G ℓ A hA x ha
  · obtain ⟨a,ha,heq⟩ := bagDistance_attained G ℓ A hA x
    rw [heq]
    exact Metric.infDist_le_dist_of_mem ha
end BoundedTreewidthL1

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
/-- The complete finite launch data, retaining both independent uniform variables
and the random good-bump event required in the non-collapse argument. -/
structure OrdinarySeed {V : Type*} [MetricSpace V] (h : V → ℝ) (α π η : ℝ) where
  n : ℕ
  m : ℕ
  mass : Fin n → ℝ
  bump : Fin n → Fin m → V → ℝ
  mass_nonneg : ∀ a, 0 ≤ mass a
  mass_total : (∑ a, mass a) = 1
  probability : IsProbabilityMeasure (noiseLaw m mass)
  measurable : Measurable (noiseG h bump)
  xi_uniform : MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m mass)
    (volume.restrict (Set.Icc (1:ℝ) 2))
  xi_independent : IndepFun noiseXi (noiseV bump) (noiseLaw m mass)
  bounds : ∀ ω : NoiseSpace n m,
      LipschitzWith 1 (noiseV bump ω) ∧
      (∀ x, 0 ≤ noiseV bump ω x ∧ noiseV bump ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h bump ω) ∧
      ∀ x, h x ≤ noiseG h bump ω x ∧ noiseG h bump ω x ≤ (5/2) * h x
  good : ∀ x, 0 < h x → ENNReal.ofReal (π/2) ≤
    noiseLaw m mass {ω | GoodBump h α η (bump ω.2.1) x}
  coefficients_uniform : ∀ j : Fin m,
    MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1))
  coefficients_independent : iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume

lemma OrdinarySeed.exists_of_has {V : Type*} [MetricSpace V] {h : V → ℝ} {α π η : ℝ}
    (hN : HasOrdinaryNoise h α π η) : Nonempty (OrdinarySeed h α π η) := by
  obtain ⟨n,m,μ,φ,hμ,hμ₁,hprob,hmeas,hxi,hind,hbound,hgood,huni,hindep⟩ := hN
  exact ⟨⟨n,m,μ,φ,hμ,hμ₁,hprob,hmeas,hxi,hind,hbound,hgood,huni,hindep⟩⟩
end BoundedTreewidthL1.LaunchNoise

end OAI
