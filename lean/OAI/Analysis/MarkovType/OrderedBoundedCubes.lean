import OAI.Analysis.MarkovType.AlternatingNorm
import OAI.Analysis.MarkovType.NormCompression
import OAI.Analysis.MarkovType.NormedC00
import OAI.Analysis.MarkovType.FiniteCubeBound
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def pairLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] C00 where
  toFun a := ∑ i : Fin n, a i • (basis (2 * i.val) - basis (2 * i.val + 1))
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def collapseAtPair (i k : ℕ) : ℕ := if k ≤ 2 * i then 0 else 1

theorem collapseAtPair_monotone (i : ℕ) : Monotone (collapseAtPair i) := by
  intro a b hab
  simp only [collapseAtPair]
  split_ifs <;> omega

theorem mapDomain_pair_collapse (i j : ℕ) :
    Finsupp.mapDomain (collapseAtPair i) (basis (2 * j) - basis (2 * j + 1)) =
      if j = i then basis 0 - basis 1 else 0 := by
  have hsub := map_sub (Finsupp.mapDomain.addMonoidHom (collapseAtPair i))
    (basis (2 * j)) (basis (2 * j + 1))
  change Finsupp.mapDomain (collapseAtPair i) _ = _ at hsub
  rw [hsub]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, basis, Finsupp.mapDomain_single]
  by_cases hji : j = i
  · subst j
    have hnext : ¬ 2 * i + 1 ≤ 2 * i := by omega
    simp [collapseAtPair, hnext]
  · by_cases hlt : j < i
    · have h1 : 2 * j ≤ 2 * i := by omega
      have h2 : 2 * j + 1 ≤ 2 * i := by omega
      simp only [collapseAtPair, ite_eq_left h1, ite_eq_left h2, ite_eq_right hji, sub_self]
    · have h1 : ¬ 2 * j ≤ 2 * i := by omega
      have h2 : ¬ 2 * j + 1 ≤ 2 * i := by omega
      simp only [collapseAtPair, ite_eq_right h1, ite_eq_right h2, ite_eq_right hji, sub_self]

theorem mapDomain_pairLinear {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    Finsupp.mapDomain (collapseAtPair i.val) (pairLinear n a) =
      a i • (basis 0 - basis 1) := by
  classical
  change Finsupp.mapDomain (collapseAtPair i.val)
      (∑ j : Fin n, a j • (basis (2 * j.val) - basis (2 * j.val + 1))) = _
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_smul, mapDomain_pair_collapse]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [ite_eq_right hval, smul_zero]
  · simp

end C00

namespace OrderedNorm

theorem subset_pairs_norm (N : OrderedNorm) {n : ℕ} (s : Finset (Fin n)) :
    N (∑ i ∈ s, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))) =
      N.alternatingNorm s.card := by
  classical
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have himage : Finset.univ.image e = s := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact s.range_orderEmbOfFin rfl
  have hsum : (∑ i : Fin s.card,
      (C00.basis (2 * (e i).val) - C00.basis (2 * (e i).val + 1))) =
      ∑ i ∈ s, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1)) := by
    have hreindex := Finset.sum_image
      (f := fun i : Fin n =>
        C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))
      (s := (Finset.univ : Finset (Fin s.card))) (g := e)
      (fun i _ j _ hij => e.injective hij)
    exact hreindex.symm.trans (congrArg
      (fun u : Finset (Fin n) =>
        ∑ i ∈ u, (C00.basis (2 * i.val) - C00.basis (2 * i.val + 1))) himage)
  rw [← hsum]
  apply N.alternatingPairs_norm
  · intro i
    omega
  · intro i j hij
    have he : (e i).val < (e j).val := e.strictMono hij
    omega

theorem pairLinear_sign_bound (N : OrderedNorm) {R : ℝ}
    (hR : ∀ m : ℕ, N.alternatingNorm m ≤ R)
    {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i = -1 ∨ ε i = 1) :
    N (C00.pairLinear n ε) ≤ 2 * R := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => ε i = 1)
  let t : Finset (Fin n) := Finset.univ.filter (fun i => ε i ≠ 1)
  let d : Fin n → C00 := fun i => C00.basis (2 * i.val) - C00.basis (2 * i.val + 1)
  have hsplit : C00.pairLinear n ε = (∑ i ∈ s, d i) - ∑ i ∈ t, d i := by
    change (∑ i : Fin n, ε i • d i) = _
    simp only [s, t, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hε i with hi | hi
    · norm_num [hi]
    · simp [hi]
  rw [hsplit]
  calc
    N ((∑ i ∈ s, d i) - ∑ i ∈ t, d i) ≤
        N (∑ i ∈ s, d i) + N (-(∑ i ∈ t, d i)) := by
      simpa only [sub_eq_add_neg] using N.add_le (∑ i ∈ s, d i) (-(∑ i ∈ t, d i))
    _ = N.alternatingNorm s.card + N.alternatingNorm t.card := by
      dsimp only [d]
      rw [N.neg, N.subset_pairs_norm s, N.subset_pairs_norm t]
    _ ≤ 2 * R := by linarith [hR s.card, hR t.card]

theorem pairLinear_upper (N : OrderedNorm) {R : ℝ}
    (hR : ∀ m : ℕ, N.alternatingNorm m ≤ R)
    {n : ℕ} (a : Fin n → ℝ) : N (C00.pairLinear n a) ≤ (2 * R) * ‖a‖ := by
  have hR0 : 0 ≤ R := by simpa only [N.alternatingNorm_zero] using hR 0
  exact seminorm_linearMap_le_mul_norm_of_sign_vertices N.toSeminorm
    (C00.pairLinear n) (mul_nonneg (by norm_num) hR0)
    (fun ε hε => N.pairLinear_sign_bound hR ε hε) a

theorem pairLinear_coordinate_lower (N : OrderedNorm) {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) :
    |a i| * N.alternatingNorm 1 ≤ N (C00.pairLinear n a) := by
  have h := N.mapDomain_le (C00.collapseAtPair i.val)
    (C00.collapseAtPair_monotone i.val) (C00.pairLinear n a)
  rw [C00.mapDomain_pairLinear, N.smul] at h
  simpa only [alternatingNorm, C00.alternating_one] using h

theorem pairLinear_lower (N : OrderedNorm) {n : ℕ} (a : Fin n → ℝ) :
    N.alternatingNorm 1 * ‖a‖ ≤ N (C00.pairLinear n a) := by
  have hc : 0 < N.alternatingNorm 1 := N.alternatingNorm_pos (by decide)
  have hnorm : ‖a‖ ≤ N (C00.pairLinear n a) / N.alternatingNorm 1 := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (N.nonneg _) hc.le)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact (le_div_iff₀ hc).mpr (N.pairLinear_coordinate_lower a i)
  have h := (le_div_iff₀ hc).mp hnorm
  simpa only [mul_comm] using h

theorem exists_uniform_cubes_of_bounded_alternating (N : OrderedNorm)
    (hbounded : BddAbove (Set.range N.alternatingNorm)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ n : ℕ,
      ∃ T : (Fin n → ℝ) →ₗ[ℝ] OrderedSpace N, ∀ a,
        ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ L * ‖a‖ := by
  obtain ⟨R, hR⟩ := hbounded
  have hRall (m : ℕ) : N.alternatingNorm m ≤ R := hR ⟨m, rfl⟩
  let c := N.alternatingNorm 1
  have hc : 0 < c := N.alternatingNorm_pos (by decide)
  refine ⟨max 1 (2 * R / c), le_max_left _ _, ?_⟩
  intro n
  let T : (Fin n → ℝ) →ₗ[ℝ] OrderedSpace N :=
    c⁻¹ • ((NormedC00.coefficients N.toSeminorm N.definite).symm.toLinearMap.comp
      (C00.pairLinear n))
  have hnorm (a : Fin n → ℝ) : ‖T a‖ = c⁻¹ * N (C00.pairLinear n a) := by
    change N (c⁻¹ • C00.pairLinear n a) = _
    rw [N.smul, abs_of_pos (inv_pos.mpr hc)]
  refine ⟨T, ?_⟩
  intro a
  rw [hnorm]
  constructor
  · calc
      ‖a‖ = c⁻¹ * (c * ‖a‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * N (C00.pairLinear n a) :=
        mul_le_mul_of_nonneg_left (N.pairLinear_lower a) (inv_nonneg.mpr hc.le)
  · calc
      c⁻¹ * N (C00.pairLinear n a) ≤ c⁻¹ * ((2 * R) * ‖a‖) :=
        mul_le_mul_of_nonneg_left (N.pairLinear_upper hRall a) (inv_nonneg.mpr hc.le)
      _ = (2 * R / c) * ‖a‖ := by simp only [div_eq_mul_inv]; ring
      _ ≤ max 1 (2 * R / c) * ‖a‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg a)

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
