import OAI.Combinatorics.TreewidthL1.CobagNoise

namespace OAI

namespace BoundedTreewidthL1.CobagScales
open LaunchNoise
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def pairDistance (d : V → V → ℝ) (p : Finset V) : ℝ :=
  if h : p.card = 2 then
    d (Finset.card_eq_two.mp h).choose (Finset.card_eq_two.mp h).choose_spec.choose
  else 0

lemma pairDistance_witness (d : V → V → ℝ) (p : Finset V) (hp : p.card = 2) :
    ∃ u v, u ≠ v ∧ p = {u,v} ∧ pairDistance d p = d u v := by
  unfold pairDistance
  rw [dite_eq_left hp]
  exact ⟨_,_,(Finset.card_eq_two.mp hp).choose_spec.choose_spec.1,
    (Finset.card_eq_two.mp hp).choose_spec.choose_spec.2,rfl⟩

lemma pairDistance_pair (d : V → V → ℝ) (hs : ∀ u v, d u v = d v u)
    {u v : V} (huv : u ≠ v) : pairDistance d {u,v} = d u v := by
  obtain ⟨a,b,hab,he,hd⟩ := pairDistance_witness d {u,v} (by simp [huv])
  have ha : a = u ∨ a = v := by
    have hm : a ∈ ({u,v} : Finset V) := he.symm ▸ Finset.mem_insert_self a {b}
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hb : b = u ∨ b = v := by
    have hm : b ∈ ({u,v} : Finset V) := he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact hd
  · exact hd.trans (hs _ _)
  · exact False.elim (hab rfl)

noncomputable def distanceScales (t : ℝ) : Finset ℤ :=
  (Finset.Icc (bandIndex 1 t - 2) (bandIndex 1 t + 1)).filter
    (fun j => (2:ℝ)^j/2 ≤ t ∧ t ≤ 4*(2:ℝ)^j)

lemma score_interval (t : ℝ) (ht : 0 < t) (j : ℤ)
    (hl : (2:ℝ)^j/2 ≤ t) (hu : t ≤ 4*(2:ℝ)^j) :
    bandIndex 1 t - 2 ≤ j ∧ j ≤ bandIndex 1 t + 1 := by
  have hbase := band_bounds 1 t (by norm_num) ht
  simp only [bandLower, one_mul] at hbase
  have hpow (a : ℤ) : (2:ℝ)^(a+2) = 4*(2:ℝ)^a := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hpow' (a : ℤ) : (2:ℝ)^(a+1) = 2*(2:ℝ)^a := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hlo : bandIndex 1 t ≤ j+2 := by
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
    rw [hpow]
    exact hbase.2.1.trans hu
  have hhi : j < bandIndex 1 t+2 := by
    apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
    rw [hpow]
    nlinarith [hbase.2.2]
  omega

lemma mem_distanceScales (t : ℝ) (ht : 0 < t) (j : ℤ) :
    j ∈ distanceScales t ↔ (2:ℝ)^j/2 ≤ t ∧ t ≤ 4*(2:ℝ)^j := by
  simp only [distanceScales, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨score_interval t ht j h.1 h.2,h⟩⟩

lemma distanceScales_card (t : ℝ) : (distanceScales t).card ≤ 4 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Int.card_Icc]
  omega

noncomputable def active (d : V → V → ℝ) (B : Finset V) : Finset ℤ :=
  (B.powersetCard 2).biUnion (fun p => distanceScales (pairDistance d p))

lemma mem_active (d : V → V → ℝ) (hs : ∀ u v, d u v = d v u)
    (hp : ∀ u v, u ≠ v → 0 < d u v) (B : Finset V) (j : ℤ) :
    j ∈ active d B ↔ ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧
      (2:ℝ)^j/2 ≤ d u v ∧ d u v ≤ 4*(2:ℝ)^j := by
  constructor
  · intro hj
    obtain ⟨p,hpB,hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hpB,hp₂⟩ := Finset.mem_powersetCard.mp hpB
    obtain ⟨u,v,huv,he,hd⟩ := pairDistance_witness d p hp₂
    have hu : u ∈ B := hpB (he ▸ Finset.mem_insert_self u {v})
    have hv : v ∈ B := hpB (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    rw [hd] at hj
    exact ⟨u,hu,v,hv,huv,(mem_distanceScales _ (hp u v huv) j).mp hj⟩
  · rintro ⟨u,hu,v,hv,huv,hl,hh⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨{u,v},Finset.mem_powersetCard.mpr ⟨?_,by simp [huv]⟩,?_⟩
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu hv
    · rw [pairDistance_pair d hs huv]
      exact (mem_distanceScales _ (hp u v huv) j).mpr ⟨hl,hh⟩

theorem active_card (d : V → V → ℝ) (B : Finset V) :
    (active d B).card ≤ 4 * B.card.choose 2 := by
  calc
    (active d B).card ≤ ∑ p ∈ B.powersetCard 2, (distanceScales (pairDistance d p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ B.powersetCard 2, 4 := Finset.sum_le_sum (fun p _ => distanceScales_card _)
    _ = 4 * B.card.choose 2 := by simp [Finset.card_powersetCard, Nat.mul_comm]

end BoundedTreewidthL1.CobagScales

namespace BoundedTreewidthL1.CobagScales
open Metric
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem inactive_far (A : Finset V) (j : ℤ) (x y : V)
    (hj : j ∉ active dist A) (hl : (2:ℝ)^j ≤ dist x y)
    (hu : dist x y < 2*(2:ℝ)^j) (hA : (A : Set V).Nonempty) :
    (2:ℝ)^j/8 ≤ infDist x (A : Set V) ∨
      (2:ℝ)^j/8 ≤ infDist y (A : Set V) := by
  by_contra h
  have hx : infDist x (A : Set V) < (2:ℝ)^j/8 := by
    exact lt_of_not_ge (fun hx => h (Or.inl hx))
  have hy : infDist y (A : Set V) < (2:ℝ)^j/8 := by
    exact lt_of_not_ge (fun hy => h (Or.inr hy))
  obtain ⟨a,ha,hxa⟩ := (infDist_lt_iff hA).mp hx
  obtain ⟨b,hb,hyb⟩ := (infDist_lt_iff hA).mp hy
  have hs : 0 < (2:ℝ)^j := zpow_pos (by norm_num) _
  have hxy := dist_triangle4 x a b y
  have hab := dist_triangle4 a x y b
  rw [dist_comm b y] at hxy
  rw [dist_comm a x] at hab
  have habpos : 0 < dist a b := by linarith
  apply hj
  apply (mem_active dist dist_comm (fun u v huv => dist_pos.mpr huv) A j).mpr
  exact ⟨a,ha,b,hb,dist_pos.mp habpos,by linarith,by linarith⟩

lemma small_scale_active (A : Finset V) (x y : V) (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y) :
    LaunchNoise.bandIndex 1 (dist x y) ∈ active dist A := by
  have hb := LaunchNoise.band_bounds 1 (dist x y) (by norm_num) (dist_pos.mpr hxy)
  simp only [LaunchNoise.bandLower,one_mul] at hb
  apply (mem_active dist dist_comm (fun u v huv => dist_pos.mpr huv) A _).mpr
  exact ⟨x,hx,y,hy,hxy,by linarith,by linarith⟩
end BoundedTreewidthL1.CobagScales

end OAI
