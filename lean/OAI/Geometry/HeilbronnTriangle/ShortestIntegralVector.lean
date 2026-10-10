import Mathlib
import OAI.Geometry.HeilbronnTriangle.PrimitiveVector

namespace OAI


namespace Problem355.IntegralMinima

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def toEuclidean (x : ι → ℤ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

def normSq (x : ι → ℤ) : ℕ := ∑ i, (x i).natAbs ^ 2

lemma norm_sq_eq (x : ι → ℤ) :
    ‖toEuclidean x‖ ^ 2 = (normSq x : ℝ) := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [toEuclidean, PiLp.toLp_apply, normSq, Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  have habs : ((x i).natAbs : ℝ) = |(x i : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (x i))
  rw [habs, sq_abs]

lemma norm_le_norm_iff (x y : ι → ℤ) :
    ‖toEuclidean x‖ ≤ ‖toEuclidean y‖ ↔ normSq x ≤ normSq y := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq, norm_sq_eq]
  exact Nat.cast_le

theorem exists_shortest (S : Set (ι → ℤ)) (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, ‖toEuclidean x‖ ≤ ‖toEuclidean y‖ := by
  classical
  have hex : ∃ n : ℕ, ∃ x ∈ S, normSq x = n := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨normSq x, x, hx, rfl⟩
  obtain ⟨x, hx, hn⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun y hy => (norm_le_norm_iff x y).mpr ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨y, hy, rfl⟩

theorem one_le_norm {x : ι → ℤ} (hx : x ≠ 0) :
    1 ≤ ‖toEuclidean x‖ := by
  classical
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hxi
  have hi_pos : 0 < (x i).natAbs := Int.natAbs_pos.mpr hi
  have hsq : 1 ≤ (x i).natAbs ^ 2 := Nat.pow_pos hi_pos
  have hsum : (x i).natAbs ^ 2 ≤ normSq x := by
    exact Finset.single_le_sum (f := fun j => (x j).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hnormSq : (1 : ℝ) ≤ normSq x := by exact_mod_cast hsq.trans hsum
  have hnorm := norm_sq_eq x
  nlinarith [norm_nonneg (toEuclidean x)]

theorem exists_shortest_outside (S : Set (ι → ℤ))
    (W : Submodule ℝ (EuclideanSpace ℝ ι))
    (h : ∃ x ∈ S, toEuclidean x ∉ W) :
    ∃ x ∈ S, toEuclidean x ∉ W ∧ 1 ≤ ‖toEuclidean x‖ ∧
      ∀ y ∈ S, toEuclidean y ∉ W → ‖toEuclidean x‖ ≤ ‖toEuclidean y‖ := by
  obtain ⟨x, hx, hmin⟩ := exists_shortest
    {x ∈ S | toEuclidean x ∉ W} h
  have hne : x ≠ 0 := by
    intro hzero
    apply hx.2
    have hz : toEuclidean x = 0 := by
      ext i
      simp [toEuclidean, hzero]
    rw [hz]
    exact W.zero_mem
  exact ⟨x, hx.1, hx.2, one_le_norm hne, fun y hy hW => hmin y ⟨hy, hW⟩⟩

theorem exists_shortest_outside_of_independent
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Set (ι → ℤ)) (f : α → ι → ℤ)
    (hfmem : ∀ i, f i ∈ S)
    (hfind : LinearIndependent ℝ (fun i => toEuclidean (f i)))
    (w : β → EuclideanSpace ℝ ι)
    (hcard : Fintype.card β < Fintype.card α)
    (R : ℝ) (hR : ∀ i, ‖toEuclidean (f i)‖ ≤ R) :
    ∃ x ∈ S, toEuclidean x ∉ Submodule.span ℝ (Set.range w) ∧
      1 ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ R ∧
      ∀ y ∈ S, toEuclidean y ∉ Submodule.span ℝ (Set.range w) →
        ‖toEuclidean x‖ ≤ ‖toEuclidean y‖ := by
  classical
  have hex : ∃ i, toEuclidean (f i) ∉ Submodule.span ℝ (Set.range w) := by
    by_contra! hall
    have hs : Submodule.span ℝ (Set.range (fun i => toEuclidean (f i))) ≤
        Submodule.span ℝ (Set.range w) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hall i
    have hd : Fintype.card α ≤ Fintype.card β := calc
      _ = Module.finrank ℝ (Submodule.span ℝ
          (Set.range (fun i => toEuclidean (f i)))) :=
        (finrank_span_eq_card hfind).symm
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range w)) :=
        Submodule.finrank_mono hs
      _ ≤ Fintype.card β := finrank_range_le_card w
    exact (not_le_of_gt hcard) hd
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x, hx, hxout, hxone, hxmin⟩ := exists_shortest_outside S
    (Submodule.span ℝ (Set.range w)) ⟨f i, hfmem i, hi⟩
  exact ⟨x, hx, hxout, hxone, (hxmin (f i) (hfmem i) hi).trans (hR i), hxmin⟩

theorem shortest_kernel_has_bezout {κ : Type*}
    (A : Matrix κ ι ℤ) (x : ι → ℤ) (hx : x ≠ 0)
    (hAx : A.mulVec x = 0)
    (hmin : ∀ y : ι → ℤ, y ≠ 0 → A.mulVec y = 0 →
      ‖toEuclidean x‖ ≤ ‖toEuclidean y‖) :
    ∃ z : ι → ℤ, ∑ i, x i * z i = 1 := by
  obtain ⟨g, y, z, hg, hxy, hyz, _, hzero, hAy⟩ :=
    PrimitiveVector.exists_factorization_mem_ker A x hx hAx
  have hyne : y ≠ 0 := by
    intro hy
    apply hx
    funext i
    rw [hxy i]
    simp [hy]
  have heq : toEuclidean x = (g : ℝ) • toEuclidean y := by
    ext i
    simp only [toEuclidean, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hxy i, Int.cast_mul]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hnorm := hmin y hyne hAy
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hgR] at hnorm
  have hypos : 0 < ‖toEuclidean y‖ := lt_of_lt_of_le zero_lt_one (one_le_norm hyne)
  have hgleR : (g : ℝ) ≤ 1 := by nlinarith
  have hgle : g ≤ 1 := by exact_mod_cast hgleR
  have hgone : g = 1 := by omega
  refine ⟨z, ?_⟩
  simpa only [hxy, hgone, one_mul] using hyz

end Problem355.IntegralMinima

end OAI
