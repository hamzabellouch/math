import Mathlib
import OAI.LinearAlgebra.MatrixFields.Tensors.ComplexDotPairing

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation.Separation

theorem grid_modular_collision (Q c t u v : ℤ)
    (hc : 0 ≤ c ∧ c < Q) (ht : 0 ≤ t ∧ t < Q)
    (hu : 0 ≤ u ∧ u < Q) (hv : 0 ≤ v ∧ v < Q)
    (hmod : Int.ModEq (4 * Q) c (t + u - v)) : c = t + u - v := by
  have hdvd : 4 * Q ∣ t + u - v - c := hmod.dvd
  have hz : t + u - v - c = 0 := by
    rcases le_total 0 (t + u - v - c) with h | h
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h (by omega) hdvd
    · have hn : -(t + u - v - c) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (Int.dvd_neg.mpr hdvd)
      omega
  omega

variable {ι : Type*} [Fintype ι]

def squaredNorm (t : ι → ℝ) : ℝ := ∑ i, (t i) ^ 2

def dot (t u : ι → ℝ) : ℝ := ∑ i, t i * u i

theorem squaredNorm_displacement (t u v : ι → ℝ) :
    squaredNorm (fun i => t i + u i - v i) =
      squaredNorm t + 2 * (dot t u - dot t v) +
        squaredNorm (fun i => u i - v i) := by
  calc
    squaredNorm (fun i => t i + u i - v i) =
        ∑ i, ((t i) ^ 2 + 2 * (t i * u i - t i * v i) +
          (u i - v i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [squaredNorm, dot, Finset.sum_add_distrib,
        mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

theorem sphere_slice_collision (t c u v : ι → ℝ)
    (hsphere : squaredNorm c = squaredNorm t)
    (hslice : dot t u = dot t v)
    (hcollision : ∀ i, c i = t i + u i - v i) : u = v ∧ c = t := by
  have hc : c = fun i => t i + u i - v i := funext hcollision
  have hzero : squaredNorm (fun i => u i - v i) = 0 := by
    have hid := squaredNorm_displacement t u v
    rw [← hc, hsphere, hslice] at hid
    linarith
  have huv : u = v := by
    funext i
    have hle : (u i - v i) ^ 2 ≤ squaredNorm (fun j => u j - v j) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j - v j)) (Finset.mem_univ i)
    rw [hzero] at hle
    nlinarith [sq_nonneg (u i - v i)]
  refine ⟨huv, ?_⟩
  funext i
  rw [hcollision, huv]
  ring

end MatrixMultiplication.Foundation.Separation





namespace MatrixMultiplication.Foundation.Separation

abbrev Grid (d Q : ℕ) := Fin d → Fin Q

def gridSquaredNorm {d Q : ℕ} (x : Grid d Q) : ℕ := ∑ i, (x i : ℕ) ^ 2

def gridDot {d Q : ℕ} (t u : Grid d Q) : ℕ := ∑ i, (t i : ℕ) * (u i : ℕ)

theorem gridSquaredNorm_le {d Q : ℕ} (x : Grid d Q) : gridSquaredNorm x ≤ d * Q ^ 2 := by
  calc
    gridSquaredNorm x ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (Nat.le_of_lt (x i).isLt) 2
    _ = d * Q ^ 2 := by simp

theorem gridDot_le {d Q : ℕ} (t u : Grid d Q) : gridDot t u ≤ d * Q ^ 2 := by
  calc
    gridDot t u ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pow_two] using
        Nat.mul_le_mul (Nat.le_of_lt (t i).isLt) (Nat.le_of_lt (u i).isLt)
    _ = d * Q ^ 2 := by simp

def normColor {d Q : ℕ} (x : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridSquaredNorm x, Nat.lt_succ_of_le (gridSquaredNorm_le x)⟩

def dotColor {d Q : ℕ} (t u : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridDot t u, Nat.lt_succ_of_le (gridDot_le t u)⟩

theorem two_stage_pigeonhole {A : Type*} [Fintype A] [DecidableEq A]
    {M K m : ℕ} (hM : 0 < M) (f : A → Fin M) (g : A → A → Fin M)
    (hK : M * K ≤ Fintype.card A) (hm : M * m ≤ Fintype.card A) :
    ∃ tags : Finset A, tags.card = K ∧
      (∃ radius : Fin M, ∀ t ∈ tags, f t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset A, slice.card = m ∧
        ∃ level : Fin M, ∀ u ∈ slice, g t u = level := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨radius, hr⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f
    (by simpa only [Fintype.card_fin] using hK)
  obtain ⟨tags, htags, hcard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨tags, hcard, ⟨radius, ?_⟩, ?_⟩
  · intro t ht
    exact (Finset.mem_filter.mp (htags ht)).2
  · intro t ht
    obtain ⟨level, hl⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (g t)
      (by simpa only [Fintype.card_fin] using hm)
    obtain ⟨slice, hslice, hsize⟩ := Finset.exists_subset_card_eq hl
    refine ⟨slice, hsize, level, ?_⟩
    intro u hu
    exact (Finset.mem_filter.mp (hslice hu)).2

theorem grid_tags_slices {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ tags : Finset (Grid d Q), tags.card = K ∧
      (∃ radius : Fin (d * Q ^ 2 + 1), ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid d Q), slice.card = m ∧
        ∃ level : Fin (d * Q ^ 2 + 1), ∀ u ∈ slice, dotColor t u = level := by
  exact two_stage_pigeonhole (Nat.succ_pos _) normColor dotColor
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hK)
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hm)







abbrev AuxiliaryGroup (d Q : ℕ) := Fin d → ZMod (4 * Q)

def gridToGroup {d Q : ℕ} (x : Grid d Q) : AuxiliaryGroup d Q :=
  fun i => (x i : ℕ)

def gridToReal {d Q : ℕ} (x : Grid d Q) : Fin d → ℝ :=
  fun i => (x i : ℕ)

theorem gridToReal_injective {d Q : ℕ} :
    Function.Injective (gridToReal : Grid d Q → Fin d → ℝ) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((x i : ℕ) : ℝ) = ((y i : ℕ) : ℝ) at hi
  exact_mod_cast hi

theorem squaredNorm_gridToReal {d Q : ℕ} (x : Grid d Q) :
    squaredNorm (gridToReal x) = (gridSquaredNorm x : ℝ) := by
  simp [squaredNorm, gridToReal, gridSquaredNorm, Nat.cast_sum]

theorem dot_gridToReal {d Q : ℕ} (x y : Grid d Q) :
    dot (gridToReal x) (gridToReal y) = (gridDot x y : ℝ) := by
  simp [dot, gridToReal, gridDot, Nat.cast_sum]

theorem grid_group_collision_lift {d Q : ℕ} (t c u v : Grid d Q)
    (h : gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c) :
    ∀ i, ((c i : ℕ) : ℤ) =
      ((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ) := by
  intro i
  have hcast : (((c i : ℕ) : ℤ) : ZMod (4 * Q)) =
      ((((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) :
        ZMod (4 * Q)) := by
    simpa [gridToGroup, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (congrFun h i).symm
  have hmod : Int.ModEq (4 * (Q : ℤ)) ((c i : ℕ) : ℤ)
      (((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff _ _ (4 * Q)).mp
        (by simpa only [Int.cast_add, Int.cast_sub] using hcast)
  have hbound (x : Fin Q) : 0 ≤ ((x : ℕ) : ℤ) ∧ ((x : ℕ) : ℤ) < (Q : ℤ) := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast x.isLt
  exact grid_modular_collision (Q : ℤ) _ _ _ _
    (hbound (c i)) (hbound (t i)) (hbound (u i)) (hbound (v i)) hmod

theorem grid_sphere_slice_collision {d Q : ℕ} (t c u v : Grid d Q)
    (hsphere : gridSquaredNorm c = gridSquaredNorm t)
    (hslice : gridDot t u = gridDot t v) :
    gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c ↔
      u = v ∧ c = t := by
  constructor
  · intro h
    have hnorm : squaredNorm (gridToReal c) = squaredNorm (gridToReal t) := by
      simp only [squaredNorm_gridToReal, hsphere]
    have hdot : dot (gridToReal t) (gridToReal u) =
        dot (gridToReal t) (gridToReal v) := by
      simp only [dot_gridToReal, hslice]
    have hlift := grid_group_collision_lift t c u v h
    have hreal : ∀ i, gridToReal c i =
        gridToReal t i + gridToReal u i - gridToReal v i := by
      intro i
      dsimp [gridToReal]
      exact_mod_cast hlift i
    obtain ⟨huv, hct⟩ := sphere_slice_collision
      (gridToReal t) (gridToReal c) (gridToReal u) (gridToReal v) hnorm hdot hreal
    exact ⟨gridToReal_injective huv, gridToReal_injective hct⟩
  · rintro ⟨rfl, rfl⟩
    simp [sub_eq_add_neg, add_left_comm]

theorem indexed_grid_collision {S U : Type*} {d Q : ℕ}
    (tag : S → Grid d Q) (point : S → U → Grid d Q)
    (htag : Function.Injective tag)
    (hpoint : ∀ s, Function.Injective (point s))
    (hsphere : ∀ s s', gridSquaredNorm (tag s') = gridSquaredNorm (tag s))
    (hslice : ∀ s i j, gridDot (tag s) (point s i) = gridDot (tag s) (point s j)) :
    ∀ s s' i j,
      gridToGroup (point s i) + (gridToGroup (tag s) - gridToGroup (point s j)) =
        gridToGroup (tag s') ↔ s = s' ∧ i = j := by
  intro s s' i j
  rw [grid_sphere_slice_collision (tag s) (tag s') (point s i) (point s j)
    (hsphere s s') (hslice s i j)]
  constructor
  · rintro ⟨hij, hss⟩
    exact ⟨(htag hss).symm, hpoint s hij⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem exists_modular_separation {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ (tag : Fin K → AuxiliaryGroup d Q)
      (point : Fin K → Fin m → AuxiliaryGroup d Q),
      ∀ s s' i j,
        point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j := by
  classical
  obtain ⟨tags, htags, ⟨radius, hradius⟩, hslices⟩ := grid_tags_slices hK hm
  choose slice hsliceCard level hlevel using
    (fun t : ↥tags => hslices t.val t.property)
  let tagEnum : Fin K ≃ ↥tags := (Finset.equivFinOfCardEq htags).symm
  let sliceEnum (t : ↥tags) : Fin m ≃ ↥(slice t) :=
    (Finset.equivFinOfCardEq (hsliceCard t)).symm
  let tagGrid (s : Fin K) : Grid d Q := (tagEnum s).val
  let pointGrid (s : Fin K) (i : Fin m) : Grid d Q :=
    (sliceEnum (tagEnum s) i).val
  have htag : Function.Injective tagGrid := by
    intro s s' h
    apply tagEnum.injective
    exact Subtype.ext h
  have hpoint : ∀ s, Function.Injective (pointGrid s) := by
    intro s i j h
    apply (sliceEnum (tagEnum s)).injective
    exact Subtype.ext h
  have hsphere : ∀ s s', gridSquaredNorm (tagGrid s') = gridSquaredNorm (tagGrid s) := by
    intro s s'
    have hc := (hradius (tagEnum s').val (tagEnum s').property).trans
      (hradius (tagEnum s).val (tagEnum s).property).symm
    exact congrArg Fin.val hc
  have hslice : ∀ s i j,
      gridDot (tagGrid s) (pointGrid s i) = gridDot (tagGrid s) (pointGrid s j) := by
    intro s i j
    have hc := (hlevel (tagEnum s) (sliceEnum (tagEnum s) i).val
      (sliceEnum (tagEnum s) i).property).trans
      (hlevel (tagEnum s) (sliceEnum (tagEnum s) j).val
        (sliceEnum (tagEnum s) j).property).symm
    exact congrArg Fin.val hc
  exact ⟨fun s => gridToGroup (tagGrid s), fun s i => gridToGroup (pointGrid s i),
    indexed_grid_collision tagGrid pointGrid htag hpoint hsphere hslice⟩

theorem card_auxiliaryGroup (d Q : ℕ) [NeZero (4 * Q)] :
    Fintype.card (AuxiliaryGroup d Q) = (4 * Q) ^ d := by
  simp [AuxiliaryGroup, ZMod.card]

end MatrixMultiplication.Foundation.Separation





namespace MatrixMultiplication.Foundation

section Separation

variable {X Y Z S U G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq S] [DecidableEq U]

def separatedTensor (lx : X → S) (T : Tensor ℂ X Y Z) :
    Tensor ℂ (X × U) (Y × U) (Z × S) :=
  fun x y z => if lx x.1 = z.2 ∧ x.2 = y.2 then T x.1 y.1 z.1 else 0

omit [Fintype G] in
theorem finite_separation_identity
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.pullback
      (fun x : X × U => (x.1, point (lx x.1) x.2))
      (fun y : Y × U => (y.1, tag (ly y.1) - point (ly y.1) y.2))
      (fun z : Z × S => (z.1, tag z.2))
      (Tensor.product T (groupTensor G)) = separatedTensor lx T := by
  funext x y z
  by_cases hzero : T x.1 y.1 z.1 = 0
  · simp [Tensor.pullback, Tensor.product, separatedTensor, hzero]
  · have hxy := hlabels x.1 y.1 z.1 hzero
    simp only [Tensor.pullback, Tensor.product, groupTensor, separatedTensor]
    simp only [← hxy, hcollision, mul_ite, mul_one, mul_zero]

theorem finite_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    separatedTensor (U := U) lx T ∈
      Tensor.restrictionOrbit (Tensor.product T (groupTensor G)) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  refine ⟨(fun (x : X × U) (original : X × G) =>
      if original = (x.1, point (lx x.1) x.2) then 1 else 0),
    (fun (y : Y × U) (original : Y × G) =>
      if original = (y.1, tag (ly y.1) - point (ly y.1) y.2) then 1 else 0),
    (fun (z : Z × S) (original : Z × G) =>
      if original = (z.1, tag z.2) then 1 else 0), ?_⟩
  exact Tensor.pullback_eq_restrict _ _ _ _

theorem finite_separation_degeneratesTo
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.DegeneratesTo (Tensor.product T (groupTensor G))
      (separatedTensor (U := U) lx T) := by
  exact subset_closure
    (finite_separation_mem_restrictionOrbit T lx ly tag point hlabels hcollision)

theorem finite_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.RankAtMost (separatedTensor (U := U) lx T) (r * Fintype.card G) := by
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  exact (hT.product (groupTensor_rankAtMost G)).pullback _ _ _

theorem finite_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.BorderRankAtMost (separatedTensor (U := U) lx T)
      (r * Fintype.card G) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  rw [Tensor.pullback_eq_restrict]
  exact (hT.product (groupTensor_rankAtMost G).borderRankAtMost).restrict _ _ _

end Separation

section FiniteGrid

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

theorem finite_grid_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m : ℕ} [NeZero (4 * Q)]
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin m) lx T ∈ Tensor.restrictionOrbit
      (Tensor.product T (groupTensor (Separation.AuxiliaryGroup d Q))) := by
  classical
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  exact finite_separation_mem_restrictionOrbit T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hlabels hc

theorem finite_grid_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := Fin m) lx T) (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_rankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

theorem finite_grid_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (separatedTensor (U := Fin m) lx T)
      (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_borderRankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

end FiniteGrid
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
