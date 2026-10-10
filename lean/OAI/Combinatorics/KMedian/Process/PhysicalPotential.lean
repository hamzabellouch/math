import Mathlib
import OAI.Combinatorics.KMedian.Analysis.Coefficients

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

noncomputable def mass {I : Type*} (g : ℝ) (S : Finset I) : ℝ := g * S.card
noncomputable def cost {I : Type*} (g : ℝ) (d : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, g * d i
noncomputable def potential {I : Type*} (x g : ℝ) (d : I → ℝ) (S : Finset I) (b : ℝ) : ℝ :=
  (1 + m x + B x * mass g S) * cost g d S + (1 - mass g S) * b

variable {I : Type*}

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

theorem cost_mono {g : ℝ} {d : I → ℝ} {S T : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ T, 0 ≤ d i) (hST : S ⊆ T) : cost g d S ≤ cost g d T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => mul_nonneg hg (hd i hi))

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

theorem cost_sdiff [DecidableEq I] (g : ℝ) (d : I → ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    cost g d (S \ T) = cost g d S - cost g d T := by
  exact Finset.sum_sdiff_eq_sub hTS

theorem cost_ge_mass_mul {g b : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hb : ∀ i ∈ S, b ≤ d i) : mass g S * b ≤ cost g d S := by
  have h := Finset.sum_le_sum (fun i (hi : i ∈ S) => mul_le_mul_of_nonneg_left (hb i hi) hg)
  simpa only [cost, mass, Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem point_cost_le {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) {i : I} (hi : i ∈ S) : g * d i ≤ cost g d S := by
  exact Finset.single_le_sum (fun j hj => mul_nonneg hg (hd j hj)) hi

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg x)

theorem removal_identity [DecidableEq I] (x g : ℝ) (d : I → ℝ) {S E : Finset I}
    (hES : E ⊆ S) (b b' : ℝ) :
    potential x g d (S \ E) b' - potential x g d S b =
      mass g E * b' - (1 + m x + B x * mass g S) * cost g d E -
      B x * mass g E * (cost g d S - cost g d E) +
      (1 - mass g S) * (b' - b) := by
  simp only [potential, mass_sdiff g hES, cost_sdiff g d hES]
  ring

theorem external_update_le [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hES : E ⊆ S) (hy : mass g S ≤ 1) (hb : b' ≤ b) :
    potential x g d (S \ E) b' - potential x g d S b ≤
      mass g E * b' - (1 + m x + B x * mass g S) * cost g d E -
      B x * mass g E * (cost g d S - cost g d E) := by
  rw [removal_identity x g d hES b b']
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) (sub_nonpos.mpr hb))

noncomputable def retained (a dh : ℝ) (d : I → ℝ) (physicalSurvivors : Finset I) : Finset I :=
  physicalSurvivors.filter (fun i => a * d i < dh)

theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

theorem retained_hinge_identity (a dh g : ℝ) (d : I → ℝ) (T : Finset I) :
    a * cost g d (retained a dh d T) + (1 - mass g (retained a dh d T)) * dh =
      dh - ∑ i ∈ T, g * max (dh - a * d i) 0 := by
  have hsum : (∑ i ∈ T, g * max (dh - a * d i) 0) =
      mass g (retained a dh d T) * dh - a * cost g d (retained a dh d T) := by
    rw [show (∑ i ∈ T, g * max (dh - a * d i) 0) =
        ∑ i ∈ retained a dh d T, g * (dh - a * d i) by
      rw [retained, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [max_eq_left (sub_nonneg.mpr h.le)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), mul_zero]]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      cost, mass, ← Finset.mul_sum]
    ring
  rw [hsum]
  ring

theorem internal_update_le {x g b' dh : ℝ} {d : I → ℝ} {S T : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) (hTS : T ⊆ S)
    (hy : mass g S ≤ 1) (hb : b' ≤ dh) :
    let a := 1 + m x + B x * mass g S
    potential x g d (retained a dh d T) b' ≤
      dh - ∑ i ∈ T, g * max (dh - a * d i) 0 := by
  dsimp only
  let a := 1 + m x + B x * mass g S
  let U := retained a dh d T
  have hUS : U ⊆ S := (retained_subset a dh d T).trans hTS
  have hmass : mass g U ≤ mass g S := mass_mono hg hUS
  have hcost : 0 ≤ cost g d U := cost_nonneg hg (fun i hi => hd i (hUS hi))
  have hcoeff : 1 + m x + B x * mass g U ≤ a := by
    dsimp [a]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hmass (B_nonneg x)) _
  have hcap := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (hmass.trans hy))
  have hc := mul_le_mul_of_nonneg_right hcoeff hcost
  have hbound : potential x g d U b' ≤ a * cost g d U + (1 - mass g U) * dh :=
    add_le_add hc hcap
  exact hbound.trans_eq (retained_hinge_identity a dh g d T)

theorem force_savings [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hES : E ⊆ S) (hδ : g ≤ mass g E) (hbE : ∀ i ∈ E, b' ≤ d i) :
    B x * g * cost g d S + (1 - mass g S) * (b - b') ≤
      potential x g d S b - potential x g d (S \ E) b' := by
  have hY := cost_nonneg hg (fun i hi => hd i (hES hi))
  have hV := cost_nonneg hg hd
  have hδy := mass_mono hg hES
  have hcap := cost_ge_mass_mul hg hbE
  have h1 := mul_nonneg (m_nonneg x) hY
  have h2 := mul_nonneg (B_nonneg x) (mul_nonneg (sub_nonneg.mpr hδy) hY)
  have h3 := mul_nonneg (B_nonneg x) (mul_nonneg (sub_nonneg.mpr hδ) hV)
  have hid := removal_identity x g d hES b b'
  nlinarith only [hcap, h1, h2, h3, hid]

theorem force_cap_bound {g b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i) (hES : E ⊆ S)
    (hE : E.Nonempty) (hbE : ∀ i ∈ E, b' ≤ d i) : b' ≤ cost g d S / g := by
  obtain ⟨i, hi⟩ := hE
  apply (le_div_iff₀ hg).mpr
  have hc := point_cost_le hg.le hd (hES hi)
  have hb := mul_le_mul_of_nonneg_left (hbE i hi) hg.le
  nlinarith only [hc, hb]

noncomputable def savingsFraction (g : ℝ) : ℝ :=
  min 1 (2 * P 1 * g / (1 + 1 / g))

theorem savingsFraction_pos {g : ℝ} (hg : 0 < g) : 0 < savingsFraction g := by
  apply lt_min (by norm_num)
  exact div_pos (mul_pos (mul_pos (by norm_num) (P_pos (by norm_num))) hg)
    (by positivity)

theorem force_fraction [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hx : x ≤ 1) (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hES : E ⊆ S) (hδ : g ≤ mass g E) (hy : mass g S ≤ 1)
    (hb' : 0 ≤ b') (hb : b' ≤ b) (hbE : ∀ i ∈ E, b' ≤ d i) :
    savingsFraction g * (cost g d S + (1 - mass g S) * b) ≤
      potential x g d S b - potential x g d (S \ E) b' := by
  have hE : E.Nonempty := by
    by_contra he
    have hzero : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hzero, mass, Finset.card_empty, Nat.cast_zero, mul_zero] at hδ
    linarith
  have hcap := force_cap_bound hg hd hES hE hbE
  have hm0 := mass_nonneg hg.le S
  have hV := cost_nonneg hg.le hd
  have hD : 0 ≤ (1 - mass g S) * (b - b') :=
    mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hb)
  have hs0 := (savingsFraction_pos hg).le
  have hs1 : savingsFraction g ≤ 1 := min_le_left _ _
  have hs2 : savingsFraction g * (1 + 1 / g) ≤ 2 * P 1 * g :=
    (le_div_iff₀ (by positivity : 0 < (1:ℝ) + 1 / g)).mp (min_le_right _ _)
  have hB : 2 * P 1 ≤ B x := by
    exact mul_le_mul_of_nonneg_left (P_antitone hx) (by norm_num)
  have hVB := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hg.le) hV
  have hsmall : (1 - mass g S) * b' ≤ b' :=
    mul_le_of_le_one_left hb' (by linarith)
  have hQ : cost g d S + (1 - mass g S) * b ≤
      (1 + 1 / g) * cost g d S + (1 - mass g S) * (b - b') := by
    have hvdiv : cost g d S / g = (1 / g) * cost g d S := by ring
    rw [hvdiv] at hcap
    nlinarith only [hsmall, hcap]
  have hsQ := mul_le_mul_of_nonneg_left hQ hs0
  have hsV := mul_le_mul_of_nonneg_right hs2 hV
  have hsD := mul_le_mul_of_nonneg_right hs1 hD
  have hsavings := force_savings (x := x) (b := b) hg.le hd hES hδ hbE
  nlinarith only [hsQ, hsV, hsD, hVB, hsavings]

theorem chunks_le_full {C : Type*} (chunks : Finset C) (δ Y : C → ℝ)
    (a B V b : ℝ) (hδ : ∀ c ∈ chunks, 0 ≤ δ c)
    (hY : ∀ c ∈ chunks, 0 ≤ Y c) (hB : 0 ≤ B) :
    (∑ c ∈ chunks, (δ c * b - a * Y c - B * δ c * (V - Y c))) ≤
      (∑ c ∈ chunks, δ c) * b - a * (∑ c ∈ chunks, Y c) -
        B * (∑ c ∈ chunks, δ c) * (V - ∑ c ∈ chunks, Y c) := by
  have hpoint : ∀ c ∈ chunks, B * δ c * Y c ≤ B * δ c * (∑ t ∈ chunks, Y t) := by
    intro c hc
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hY hc) (mul_nonneg hB (hδ c hc))
  have hs := Finset.sum_le_sum hpoint
  have hrewrite : ∀ c, δ c * b - a * Y c - B * δ c * (V - Y c) =
      δ c * b - a * Y c - B * δ c * V + B * δ c * Y c := by intro c; ring
  simp_rw [hrewrite]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at hs ⊢
  nlinarith only [hs]

end MetricKMedian.PhysicalPotential
end
end

end OAI
