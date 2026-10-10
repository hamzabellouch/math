import OAI.Combinatorics.SharpThreshold.LowDegreeConstants
import OAI.Combinatorics.SharpThreshold.LowDegreeInfluence

namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

/-- Every nonempty low-degree Fourier support is counted by at least one of
its incident coordinate sums.  This is purely finite, nonnegative double counting. -/
theorem lowDegree_mass_le_incident_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k : ℝ) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro S hS
  by_cases h : S.Nonempty ∧ (S.card : ℝ) ≤ k
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h.1
    calc
      a S = (if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) := by simp [hi, h.2]
      _ ≤ ∑ j : ι, if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
        apply Finset.single_le_sum (f := fun j : ι =>
          if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) (s := Finset.univ)
        · intro j hj
          split_ifs
          · exact ha S
          · exact le_refl 0
        · exact Finset.mem_univ i
  · rw [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact ha S
    · exact le_refl 0

/-- Assemble coordinatewise low-degree estimates without any choice of a
single coordinate common to all supports. -/
theorem lowDegree_mass_le_of_coordinate_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k C : ℝ)
    (J : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι,
      if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤ C * J i) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ i : ι, J i := by
  calc
    _ ≤ ∑ i : ι, ∑ S : Finset ι,
        if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 :=
      lowDegree_mass_le_incident_mass a ha k
    _ ≤ ∑ i : ι, C * J i := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = C * ∑ i : ι, J i := (Finset.mul_sum _ _ _).symm

/-- A cutoff below one contains no nonconstant Boolean Fourier supports. -/
theorem lowDegree_mass_eq_zero_of_lt_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) {k : ℝ} (hk : k < 1) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  apply ite_eq_right
  rintro ⟨hne, hcard⟩
  have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
  linarith

/-- Erasing a fixed coordinate injects supports containing it into supports
of no larger degree.  This transports a derivative coefficient identity to
a low-degree mass bound, without changing the ambient coordinate type. -/
theorem incident_mass_le_erase_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι → ℝ) (hb : ∀ T, 0 ≤ b T) (i : ι) (k C : ℝ)
    (hC : 0 ≤ C)
    (hderiv : ∀ S, i ∈ S → a S = C * b (S.erase i)) :
    (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ T : Finset ι, if (T.card : ℝ) ≤ k then b T else 0 := by
  let s : Finset (Finset ι) := univ.filter (fun S => i ∈ S ∧ (S.card : ℝ) ≤ k)
  let t : Finset (Finset ι) := univ.filter (fun T => (T.card : ℝ) ≤ k)
  have hinj : Set.InjOn (fun S : Finset ι => S.erase i) (s : Set (Finset ι)) := by
    intro S hS T hT hST
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2.1
    have hiT : i ∈ T := (Finset.mem_filter.mp hT).2.1
    simpa only [Finset.insert_erase hiS, Finset.insert_erase hiT] using
      congrArg (fun U : Finset ι => insert i U) hST
  have hsub : s.image (fun S => S.erase i) ⊆ t := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard : ((S.erase i).card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_erase_le (s := S) (a := i)
    exact hcard.trans (Finset.mem_filter.mp hS).2.2
  calc
    _ = ∑ S ∈ s, a S := (Finset.sum_filter _ _).symm
    _ = ∑ S ∈ s, C * b (S.erase i) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hderiv S (Finset.mem_filter.mp hS).2.1
    _ = C * ∑ S ∈ s, b (S.erase i) := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ T ∈ s.image (fun S => S.erase i), b T := by
      rw [Finset.sum_image hinj]
    _ ≤ C * ∑ T ∈ t, b T := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hb T)
    _ = _ := by rw [Finset.sum_filter]

/-- The complete low-degree estimate once the analytic Fourier ingredients
are supplied: the derivative coefficient identity and the low-degree
projection bound.  All incidence counting, bias constants, and the
small/large total-influence split are discharged here. -/
theorem lowDegree_bound_of_projection
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (b : ι → Finset ι → ℝ) (J : ι → ℝ)
    (σ m : ℝ) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m)
    (ha : ∀ S, 0 ≤ a S) (hb : ∀ i S, 0 ≤ b i S)
    (hJ : ∀ i, 0 ≤ J i) (horbit : ∀ i, J i ≤ (∑ j, J j) / m)
    (henergy : (∑ S : Finset ι, a S) ≤ 1)
    (hderiv : ∀ i S, i ∈ S → a S = σ ^ 2 * b i (S.erase i))
    (hprojection : ∀ i,
      (∑ S : Finset ι, if (S.card : ℝ) ≤ σ * Real.log m / 64 then b i S else 0) ≤
        (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) * (J i) ^ (3 / 2 : ℝ)) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ σ * Real.log m / 64 then a S else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, J i := by
  let k : ℝ := σ * Real.log m / 64
  let R : ℝ := (σ / 4) ^ (-(2 : ℝ) * k)
  let L : ℝ := ∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0
  have hL1 : L ≤ 1 := by
    apply le_trans _ henergy
    apply Finset.sum_le_sum
    intro S hS
    split_ifs
    · exact le_refl _
    · exact ha S
  have hcoord : ∀ i,
      (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
        (σ ^ 2 * R) * (J i) ^ (3 / 2 : ℝ) := by
    intro i
    calc
      _ ≤ σ ^ 2 * ∑ S : Finset ι, if (S.card : ℝ) ≤ k then b i S else 0 :=
        incident_mass_le_erase_mass a (b i) (hb i) i k (σ ^ 2)
          (sq_nonneg σ) (hderiv i)
      _ ≤ σ ^ 2 * (R * (J i) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hprojection i) (sq_nonneg σ)
      _ = _ := by ring
  have hproj : L ≤ σ ^ 2 * R * ∑ i, (J i) ^ (3 / 2 : ℝ) :=
    lowDegree_mass_le_of_coordinate_bound a ha k (σ ^ 2 * R)
      (fun i => (J i) ^ (3 / 2 : ℝ)) hcoord
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  exact low_degree_influence_bound_of_factor J m (∑ i, J i) (σ ^ 2) R L
    hm hJ rfl horbit (sq_nonneg σ) hσsq (noise_loss_le_rpow hσ hσhalf hm) hL1 hproj

end Problem313

end

end OAI
