import OAI.Combinatorics.FiniteCircle.TaggedRows

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

noncomputable def circleCost {M : ℕ} (x : ZMod M) : ℝ := x.valMinAbs.natAbs / (M : ℝ)

@[simp] theorem circleCost_zero (M : ℕ) : circleCost (0 : ZMod M) = 0 := by
  simp [circleCost]

theorem circleCost_nonneg {M : ℕ} (x : ZMod M) : 0 ≤ circleCost x := by
  unfold circleCost
  positivity

@[simp] theorem circleCost_neg {M : ℕ} (x : ZMod M) : circleCost (-x) = circleCost x := by
  simp [circleCost, ZMod.natAbs_valMinAbs_neg]

theorem circleCost_add_le {M : ℕ} (x y : ZMod M) :
    circleCost (x+y) ≤ circleCost x + circleCost y := by
  have h := (ZMod.natAbs_valMinAbs_add_le x y).trans (Int.natAbs_add_le _ _)
  unfold circleCost
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

theorem circleCost_le_half {M : ℕ} [NeZero M] (x : ZMod M) : circleCost x ≤ 1/2 := by
  have hM : 0 < M := NeZero.pos M
  have h := ZMod.natAbs_valMinAbs_le x
  have h' : 2*x.valMinAbs.natAbs ≤ M := by omega
  unfold circleCost
  rw [div_le_iff₀ (by exact_mod_cast hM)]
  have hh : 2*(x.valMinAbs.natAbs : ℝ) ≤ M := by exact_mod_cast h'
  linarith

theorem circleCost_pos {M : ℕ} [NeZero M] {x : ZMod M} (hx : x ≠ 0) : 0 < circleCost x := by
  have hn : x.valMinAbs.natAbs ≠ 0 := by
    intro he
    exact hx ((ZMod.valMinAbs_eq_zero x).mp (Int.natAbs_eq_zero.mp he))
  unfold circleCost
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast NeZero.pos M)

theorem circleCost_order_lower {M q : ℕ} [NeZero M] {x : ZMod M}
    (hq : 0 < q) (hx : x ≠ 0) (hqx : q • x = 0) : 1 ≤ (q : ℝ)*circleCost x := by
  have he : (((q : ℤ)*x.valMinAbs : ℤ) : ZMod M) = 0 := by
    simpa [nsmul_eq_mul] using hqx
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  have hd' : M ∣ q*x.valMinAbs.natAbs := by
    have hh := Int.natAbs_dvd_natAbs.mpr hd
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
  have ha : 0 < x.valMinAbs.natAbs := by
    apply Nat.pos_of_ne_zero
    intro he
    exact hx ((ZMod.valMinAbs_eq_zero x).mp (Int.natAbs_eq_zero.mp he))
  have hm := Nat.le_of_dvd (Nat.mul_pos hq ha) hd'
  unfold circleCost
  rw [← mul_div_assoc, le_div_iff₀ (by exact_mod_cast NeZero.pos M)]
  simp only [one_mul]
  exact_mod_cast hm

structure PhaseCost (G : Type*) [AddCommGroup G] where
  toFun : G → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  zero : toFun 0 = 0
  neg : ∀ x, toFun (-x) = toFun x
  add_le : ∀ x y, toFun (x+y) ≤ toFun x + toFun y

instance {G : Type*} [AddCommGroup G] : CoeFun (PhaseCost G) (fun _ => G → ℝ) := ⟨PhaseCost.toFun⟩

noncomputable def circlePhaseCost (M : ℕ) : PhaseCost (ZMod M) :=
  ⟨circleCost, circleCost_nonneg, circleCost_zero M, circleCost_neg, circleCost_add_le⟩

namespace PhaseCost
variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H] [Fintype J]

noncomputable def average (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) : ℝ :=
  (∑ j, f (x + σ s j)) / Fintype.card J

noncomputable def infAverage (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (f.average σ x)

theorem infAverage_le (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) :
    f.infAverage σ x ≤ f.average σ x s :=
  Finset.inf'_le _ (Finset.mem_univ s)

theorem exists_average_eq (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    ∃ s : H, f.infAverage σ x = f.average σ x s := by
  obtain ⟨s,_,hs⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (f.average σ x)
  exact ⟨s,hs⟩

theorem infAverage_nonneg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    0 ≤ f.infAverage σ x := by
  apply Finset.le_inf'
  intro s _
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => f.nonneg _)) (by positivity)

omit [Fintype H] in
@[simp] theorem average_zero_mask [Nonempty J] (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.average σ x 0 = f x := by
  simp only [average, map_zero, Pi.zero_apply, add_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J).ne')

theorem infAverage_le_self [Nonempty J] (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.infAverage σ x ≤ f x := by
  simpa using f.infAverage_le σ x 0

@[simp] theorem infAverage_zero (f : PhaseCost G) (σ : H →+ (J → G)) :
    f.infAverage σ 0 = 0 := by
  apply le_antisymm
  · refine (f.infAverage_le σ 0 0).trans_eq ?_
    simp only [average, map_zero, Pi.zero_apply, add_zero, f.zero,
      Finset.sum_const_zero, zero_div]
  · exact f.infAverage_nonneg σ 0

omit [Fintype H] in
@[simp] theorem average_neg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) (s : H) :
    f.average σ (-x) (-s) = f.average σ x s := by
  unfold average
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : -x+σ (-s) j = -(x+σ s j) := by simp [add_comm]
  rw [he, f.neg]

@[simp] theorem infAverage_neg (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.infAverage σ (-x) = f.infAverage σ x := by
  have aux (x : G) : f.infAverage σ (-x) ≤ f.infAverage σ x := by
    obtain ⟨s,hs⟩ := f.exists_average_eq σ x
    rw [hs]
    simpa using f.infAverage_le σ (-x) (-s)
  exact le_antisymm (aux x) (by simpa using aux (-x))

omit [Fintype H] in
theorem average_add_le (f : PhaseCost G) (σ : H →+ (J → G)) (x y : G) (s t : H) :
    f.average σ (x+y) (s+t) ≤ f.average σ x s + f.average σ y t := by
  unfold average
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have he : x+y+σ (s+t) j = (x+σ s j)+(y+σ t j) := by
    simp only [map_add, Pi.add_apply]
    abel
  rw [he]
  exact f.add_le _ _

theorem infAverage_add_le (f : PhaseCost G) (σ : H →+ (J → G)) (x y : G) :
    f.infAverage σ (x+y) ≤ f.infAverage σ x + f.infAverage σ y := by
  obtain ⟨s,hs⟩ := f.exists_average_eq σ x
  obtain ⟨t,ht⟩ := f.exists_average_eq σ y
  rw [hs,ht]
  exact (f.infAverage_le σ (x+y) (s+t)).trans (f.average_add_le σ x y s t)

noncomputable def step (f : PhaseCost G) (σ : H →+ (J → G)) : PhaseCost G :=
  ⟨f.infAverage σ, f.infAverage_nonneg σ, f.infAverage_zero σ,
    f.infAverage_neg σ, f.infAverage_add_le σ⟩

end PhaseCost

end FiniteCircle

end OAI
