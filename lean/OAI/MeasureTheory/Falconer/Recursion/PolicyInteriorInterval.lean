import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy

namespace OAI

namespace PlanarFalconer

theorem policy_blocks_order_convex {N q a t j k l : ℕ}
    (hj : j ∈ policyBlocks N q a t) (hl : l ∈ policyBlocks N q a t)
    (hjk : j ≤ k) (hkl : k ≤ l) : k ∈ policyBlocks N q a t := by
  have hj' := policyBlocks_mem hj
  have hl' := policyBlocks_mem hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · exact hj'.2.1.trans (Nat.mul_le_mul_right q hjk)
  · exact (Nat.mul_le_mul_right q (Nat.add_le_add_right hkl 1)).trans hl'.2.2

theorem policy_interior_interval (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ l u : ℕ, l ≤ a+2*q ∧ t ≤ u+2*q ∧
      l ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ u ∧
      ∀ n, l ≤ n → n ≤ u → A (policyDepth A N q a t) ≤ A n := by
  let S := policyBlocks N q a t
  have hS : S.Nonempty := policyBlocks_nonempty hq ht hwide
  let j := S.min' hS
  let k := S.max' hS
  have hj : j ∈ S := S.min'_mem hS
  have hk : k ∈ S := S.max'_mem hS
  have hj' := policyBlocks_mem hj
  have hk' := policyBlocks_mem hk
  have hkpos : 0 < (k+1)*q := Nat.mul_pos (by omega) hq
  have huN : (k+1)*q-1 ≤ N := by omega
  obtain ⟨j₀,hj₀,hleft⟩ := policy_left_block hq ht hwide
  obtain ⟨k₀,hk₀,hright⟩ := policy_right_block hq ht hwide
  have hjj₀ : j ≤ j₀ := S.min'_le j₀ hj₀
  have hk₀k : k₀ ≤ k := S.le_max' k₀ hk₀
  have hlower : j*q ≤ a+2*q := (Nat.mul_le_mul_right q hjj₀).trans hleft
  have hupper : t ≤ ((k+1)*q-1)+2*q := by
    have hh := Nat.mul_le_mul_right q (Nat.add_le_add_right hk₀k 1)
    omega
  let key := policyKey A N q a t
  have hkey : key ∈ S := (finiteArgmin_spec hS (fun j => A (policyRepresentative A N q j))).1
  have hkeylo : j ≤ key := S.min'_le key hkey
  have hkeyhi : key ≤ k := S.le_max' key hkey
  have hrep := policyRepresentative_spec A hq
    ((Nat.le_div_iff_mul_le hq).mp (policyBlocks_mem hkey).1)
  have hplo : j*q ≤ policyDepth A N q a t := (Nat.mul_le_mul_right q hkeylo).trans hrep.1
  have hphi : policyDepth A N q a t ≤ (k+1)*q-1 := by
    have hh := hrep.2.1.trans_le (Nat.mul_le_mul_right q (Nat.add_le_add_right hkeyhi 1))
    exact Nat.le_sub_one_of_lt hh
  refine ⟨j*q,(k+1)*q-1,hlower,hupper,hplo,hphi,?_⟩
  intro n hnlo hnhi
  have hnN : n ≤ N := hnhi.trans huN
  have hjn : j ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hnlo
  have hnk : n/q ≤ k := by
    have hh : n < (k+1)*q := by omega
    have hd := (Nat.div_lt_iff_lt_mul hq).mpr hh
    omega
  exact policyDepth_minimizes A hq hS hnN (policy_blocks_order_convex hj hk hjn hnk)

noncomputable def policyRepresentatives (A : ℕ → ℝ) (N q : ℕ) : Finset ℕ :=
  (Finset.range (N/q+1)).image (policyRepresentative A N q)

theorem policy_representatives_card (A : ℕ → ℝ) (N q : ℕ) :
    (policyRepresentatives A N q).card ≤ N/q+1 :=
  Finset.card_image_le.trans (by simp)

theorem policyDepth_mem_representatives (A : ℕ → ℝ) {N q a t : ℕ}
    (hne : (policyBlocks N q a t).Nonempty) :
    policyDepth A N q a t ∈ policyRepresentatives A N q := by
  have hk := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  exact Finset.mem_image.mpr ⟨policyKey A N q a t,(Finset.mem_filter.mp hk).1,rfl⟩

end PlanarFalconer

end OAI
