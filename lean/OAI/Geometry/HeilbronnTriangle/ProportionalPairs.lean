import OAI.Geometry.HeilbronnTriangle.GcdPairCount

namespace OAI


open Finset

noncomputable section

namespace Problem355.ProportionalPairs

theorem proportional_parameter (a b x y : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (hx : x < a) (hxy : a * y = b * x) :
    ∃ k < Nat.gcd a b,
      x = (a / Nat.gcd a b) * k ∧ y = (b / Nat.gcd a b) * k := by
  let g := Nat.gcd a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hag : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbg : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hap : 0 < a / g := by nlinarith
  have hxy' : (a / g) * y = (b / g) * x := by
    apply Nat.mul_left_cancel hg
    simpa only [← mul_assoc, hag, hbg] using hxy
  have hd : a / g ∣ x :=
    (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
      ⟨y, hxy'.symm⟩
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_, hk, ?_⟩
  · nlinarith
  · apply Nat.mul_left_cancel hap
    rw [hxy', hk]
    ring

theorem card_coordinate_pairs_le_gcd (N a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hNa : N ≤ a) :
    ((range N ×ˢ range N).filter fun p : ℕ × ℕ => a * p.2 = b * p.1).card ≤
      Nat.gcd a b := by
  let S := (range N ×ˢ range N).filter fun p : ℕ × ℕ => a * p.2 = b * p.1
  let g := Nat.gcd a b
  let f : ℕ × ℕ → ℕ := fun p => p.1 / (a / g)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hag : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hap : 0 < a / g := by nlinarith
  have hparam (p : ℕ × ℕ) (hp : p ∈ S) :
      ∃ k < g, p.1 = (a / g) * k ∧ p.2 = (b / g) * k := by
    have hp' := mem_filter.mp hp
    have hxp := mem_range.mp (mem_product.mp hp'.1).1
    exact proportional_parameter a b p.1 p.2 ha hb (lt_of_lt_of_le hxp hNa) hp'.2
  have hf (p : ℕ × ℕ) (hp : p ∈ S) : f p < g := by
    obtain ⟨k, hk, hx, hy⟩ := hparam p hp
    simpa only [f, hx, Nat.mul_div_right _ hap] using hk
  have hinj : Set.InjOn f ↑S := by
    intro p hp q hq hpq
    obtain ⟨k, hk, hx, hy⟩ := hparam p hp
    obtain ⟨l, hl, qx, qy⟩ := hparam q hq
    have hkl : k = l := by
      simpa only [f, hx, qx, Nat.mul_div_right _ hap] using hpq
    apply Prod.ext <;> simp_all
  simpa only [card_range] using
    (Finset.card_le_card_of_injOn f (fun p hp => mem_range.mpr (hf p hp)) hinj)

theorem sum_gcd_sq_le_cube_of_subset (M : ℕ) (H : Finset ℕ)
    (hH : H ⊆ Ico 1 (M + 1)) :
    (∑ a ∈ H, ∑ b ∈ H, Nat.gcd a b ^ 2) ≤ M ^ 3 := by
  calc
    _ ≤ ∑ a ∈ H, ∑ b ∈ Ico 1 (M + 1), Nat.gcd a b ^ 2 := by
      exact sum_le_sum fun a _ => sum_le_sum_of_subset hH
    _ ≤ ∑ a ∈ Ico 1 (M + 1), ∑ b ∈ Ico 1 (M + 1), Nat.gcd a b ^ 2 :=
      sum_le_sum_of_subset hH
    _ ≤ M ^ 3 := by
      have heq : Ico 1 (M + 1) = Ioc 0 M := by
        ext a
        simp only [mem_Ico, mem_Ioc]
        omega
      rw [heq]
      exact GcdPairCount.sum_gcd_sq_le_cube M

def coordinatePairs (N a b : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter fun p => a * p.2 = b * p.1

def proportionalPairParameters (N : ℕ) : Finset (Σ _a : ℕ, Σ _b : ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :=
  (Ico N (2 * N)).sigma fun a =>
    (Ico N (2 * N)).sigma fun b => coordinatePairs N a b ×ˢ coordinatePairs N a b

theorem card_proportionalPairParameters_le (N : ℕ) (hN : 0 < N) :
    (proportionalPairParameters N).card ≤ 8 * N ^ 3 := by
  have hH : Ico N (2 * N) ⊆ Ico 1 (2 * N + 1) := by
    intro a ha
    simp only [mem_Ico] at ha ⊢
    omega
  calc
    _ = ∑ a ∈ Ico N (2 * N), ∑ b ∈ Ico N (2 * N),
        (coordinatePairs N a b).card ^ 2 := by
      simp only [proportionalPairParameters, card_sigma, card_product, pow_two]
    _ ≤ ∑ a ∈ Ico N (2 * N), ∑ b ∈ Ico N (2 * N), Nat.gcd a b ^ 2 := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      apply Nat.pow_le_pow_left
      exact card_coordinate_pairs_le_gcd N a b
        (lt_of_lt_of_le hN (mem_Ico.mp ha).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hb).1) (mem_Ico.mp ha).1
    _ ≤ (2 * N) ^ 3 := sum_gcd_sq_le_cube_of_subset (2 * N) _ hH
    _ = 8 * N ^ 3 := by ring

abbrev NatColumn := (ℕ × ℕ) × ℕ

def columnBox (N : ℕ) : Finset NatColumn :=
  (range N ×ˢ range N) ×ˢ Ico N (2 * N)

def Proportional (u v : NatColumn) : Prop :=
  u.2 * v.1.1 = v.2 * u.1.1 ∧ u.2 * v.1.2 = v.2 * u.1.2

instance (u v : NatColumn) : Decidable (Proportional u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

def proportionalPairs (N : ℕ) : Finset (NatColumn × NatColumn) :=
  (columnBox N ×ˢ columnBox N).filter fun p => Proportional p.1 p.2

theorem card_proportionalPairs_le (N : ℕ) (hN : 0 < N) :
    (proportionalPairs N).card ≤ 8 * N ^ 3 := by
  let f : NatColumn × NatColumn → Σ _a : ℕ, Σ _b : ℕ, (ℕ × ℕ) × (ℕ × ℕ) :=
    fun p => ⟨p.1.2, p.2.2, (p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)⟩
  have hf : Set.MapsTo f ↑(proportionalPairs N) ↑(proportionalPairParameters N) := by
    intro p hp
    change p ∈ proportionalPairs N at hp
    change f p ∈ proportionalPairParameters N
    have hfilter := Finset.mem_filter.mp hp
    have hpairs := Finset.mem_product.mp hfilter.1
    have hleft := Finset.mem_product.mp hpairs.1
    have hright := Finset.mem_product.mp hpairs.2
    have hleftCoords := Finset.mem_product.mp hleft.1
    have hrightCoords := Finset.mem_product.mp hright.1
    simp only [f, proportionalPairParameters, mem_sigma, mem_product,
      coordinatePairs, mem_filter]
    exact ⟨hleft.2, hright.2,
      ⟨⟨hleftCoords.1, hrightCoords.1⟩, hfilter.2.1⟩,
      ⟨⟨hleftCoords.2, hrightCoords.2⟩, hfilter.2.2⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨⟨px, py⟩, pz⟩, ⟨⟨qx, qy⟩, qz⟩⟩
      ⟨⟨⟨rx, ry⟩, rz⟩, ⟨⟨sx, sy⟩, sz⟩⟩ h
    simp only [f, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h ⊢
    tauto
  exact (card_le_card_of_injOn f hf hinj.injOn).trans
    (card_proportionalPairParameters_le N hN)

def project (u : NatColumn) : ℝ × ℝ :=
  ((u.1.1 : ℝ) / u.2, (u.1.2 : ℝ) / u.2)

theorem project_eq_iff_proportional (u v : NatColumn) (hu : 0 < u.2) (hv : 0 < v.2) :
    project u = project v ↔ Proportional u v := by
  have hu' : (u.2 : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v.2 : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [project, Prod.mk.injEq, div_eq_div_iff hu' hv', Proportional]
  constructor
  · rintro ⟨hx, hy⟩
    norm_cast at hx hy
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    constructor
    · exact_mod_cast (show u.1.1 * v.2 = v.1.1 * u.2 by nlinarith)
    · exact_mod_cast (show u.1.2 * v.2 = v.1.2 * u.2 by nlinarith)

theorem card_equal_projection_pairs_le (N : ℕ) (hN : 0 < N) :
    ((columnBox N ×ˢ columnBox N).filter fun p => project p.1 = project p.2).card ≤
      8 * N ^ 3 := by
  classical
  have heq : ((columnBox N ×ˢ columnBox N).filter fun p => project p.1 = project p.2) =
      proportionalPairs N := by
    ext p
    simp only [mem_filter, proportionalPairs]
    constructor
    · rintro ⟨hp, he⟩
      have hp' := mem_product.mp hp
      have hu := (mem_product.mp hp'.1).2
      have hv := (mem_product.mp hp'.2).2
      exact ⟨hp, (project_eq_iff_proportional _ _
        (lt_of_lt_of_le hN (mem_Ico.mp hu).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hv).1)).mp he⟩
    · rintro ⟨hp, he⟩
      have hp' := mem_product.mp hp
      have hu := (mem_product.mp hp'.1).2
      have hv := (mem_product.mp hp'.2).2
      exact ⟨hp, (project_eq_iff_proportional _ _
        (lt_of_lt_of_le hN (mem_Ico.mp hu).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hv).1)).mpr he⟩
  rw [heq]
  exact card_proportionalPairs_le N hN

theorem card_equal_projection_pairs_le_of_subset (N : ℕ) (hN : 0 < N)
    (U V : Finset NatColumn) (hU : U ⊆ columnBox N) (hV : V ⊆ columnBox N) :
    ((U ×ˢ V).filter fun p => project p.1 = project p.2).card ≤ 8 * N ^ 3 := by
  classical
  exact (card_le_card (filter_subset_filter _ (product_subset_product hU hV))).trans
    (card_equal_projection_pairs_le N hN)

theorem uniform_collision_fraction_le (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L)
    (hN : N = Q * L) (U V : Finset NatColumn)
    (hU : U ⊆ columnBox N) (hV : V ⊆ columnBox N)
    (hUc : U.card = L ^ 3) (hVc : V.card = L ^ 3) :
    (((U ×ˢ V).filter fun p => project p.1 = project p.2).card : ℝ) /
        ((U.card : ℝ) * (V.card : ℝ)) ≤ 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  classical
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcount : (((U ×ˢ V).filter fun p => project p.1 = project p.2).card : ℝ) ≤
      8 * (N : ℝ) ^ 3 := by
    exact_mod_cast card_equal_projection_pairs_le_of_subset N hNpos U V hU hV
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hUc, hVc]
  push_cast
  calc
    _ ≤ (8 * (N : ℝ) ^ 3) / ((L : ℝ) ^ 3 * (L : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ = 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
      rw [hN]
      push_cast
      field_simp

end Problem355.ProportionalPairs

end

end OAI
