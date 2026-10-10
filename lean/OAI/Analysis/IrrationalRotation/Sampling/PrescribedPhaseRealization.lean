import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic

namespace OAI

namespace Invariant233
namespace PrescribedPhaseRealization

open Set

local notation "Circle" => AddCircle (1 : ℝ)

theorem dense_positive_orbit_tail {θ : ℝ} (hθ : Irrational θ) (N : ℕ) :
    DenseRange (fun n : ℕ => (n + N) • (θ : Circle)) := by
  have hz : DenseRange (fun n : ℤ => n • (θ : Circle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hθ)
  have hn : DenseRange (fun n : ℕ => n • (θ : Circle)) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have ht := (Homeomorph.addRight (N • (θ : Circle))).surjective.denseRange.comp
    hn (Homeomorph.addRight (N • (θ : Circle))).continuous
  change DenseRange (fun n : ℕ => n • (θ : Circle) + N • (θ : Circle)) at ht
  simpa only [add_nsmul] using ht

theorem exists_large_phase_in_interval {θ a b : ℝ} (hθ : Irrational θ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a < Int.fract ((n : ℝ) * θ) ∧
      Int.fract ((n : ℝ) * θ) < b := by
  let s : Set Circle := (fun x : ℝ => (x : Circle)) '' Ioo a b
  have hsopen : IsOpen s := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hsnonempty : s.Nonempty := (nonempty_Ioo.mpr hab).image _
  obtain ⟨n, hn⟩ := (dense_positive_orbit_tail hθ N).exists_mem_open hsopen hsnonempty
  obtain ⟨z, hz, he⟩ := hn
  have hz01 : 0 ≤ z ∧ z < 1 := ⟨ha.trans hz.1.le, hz.2.trans_le hb⟩
  have he' : Int.fract z = Int.fract (((n + N : ℕ) : ℝ) * θ) := by
    have heq := congrArg (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) he
    simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul,
      AddCircle.coe_equivIco_mk_apply, div_one, mul_one] using heq
  rw [Int.fract_eq_self.mpr hz01] at he'
  refine ⟨n + N, Nat.le_add_left N n, ?_⟩
  rw [← he']
  exact hz

theorem exists_large_divisible_phase {θ a b : ℝ} (hθ : Irrational θ)
    {q : ℕ} (hq : 0 < q) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a < Int.fract (((q * n : ℕ) : ℝ) * θ) ∧
      Int.fract (((q * n : ℕ) : ℝ) * θ) < b := by
  obtain ⟨n, hn, hlo, hhi⟩ :=
    exists_large_phase_in_interval (hθ.natCast_mul hq.ne') ha hab hb N
  refine ⟨n, hn, ?_, ?_⟩
  · have he : ((q * n : ℕ) : ℝ) * θ = (n : ℝ) * ((q : ℝ) * θ) := by
      push_cast
      ring
    rw [he]
    exact hlo
  · have he : ((q * n : ℕ) : ℝ) * θ = (n : ℝ) * ((q : ℝ) * θ) := by
      push_cast
      ring
    rw [he]
    exact hhi

theorem exists_divisible_frequencies {θ : ℝ} (hθ : Irrational θ)
    (a b : ℕ → ℝ) (B : ℕ → ℕ)
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n < b n) (hb : ∀ n, b n ≤ 1)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ n, 0 < q n) ∧
      ∀ n, q n ∣ q (n + 1) ∧ q n < q (n + 1) ∧
        B n * q n ≤ q (n + 1) ∧
        a n < Int.fract ((q (n + 1) : ℝ) * θ) ∧
        Int.fract ((q (n + 1) : ℝ) * θ) < b n := by
  classical
  let P := {q : ℕ // 0 < q}
  have hstep : ∀ n (q : P), ∃ q' : P,
      q.val ∣ q'.val ∧ q.val < q'.val ∧ B n * q.val ≤ q'.val ∧
        a n < Int.fract ((q'.val : ℝ) * θ) ∧
        Int.fract ((q'.val : ℝ) * θ) < b n := by
    intro n q
    obtain ⟨m, hm, hlo, hhi⟩ := exists_large_divisible_phase hθ q.property
      (ha n) (hab n) (hb n) (max (B n) 2)
    have hm₂ : 2 ≤ m := (le_max_right (B n) 2).trans hm
    have hmB : B n ≤ m := (le_max_left (B n) 2).trans hm
    refine ⟨⟨q.val * m, Nat.mul_pos q.property (by omega)⟩, ⟨m, rfl⟩, ?_, ?_, hlo, hhi⟩
    · change q.val < q.val * m
      nlinarith [q.property]
    · change B n * q.val ≤ q.val * m
      nlinarith
  let Q : ℕ → P := Nat.rec ⟨q₀, hq₀⟩ (fun n q => Classical.choose (hstep n q))
  refine ⟨fun n => (Q n).val, rfl, fun n => (Q n).property, ?_⟩
  intro n
  exact Classical.choose_spec (hstep n (Q n))

theorem exists_divisible_phase_approximation {θ : ℝ} (hθ : Irrational θ)
    (target ε : ℕ → ℝ) (B : ℕ → ℕ)
    (htarget₀ : ∀ n, 0 < target n) (htarget₁ : ∀ n, target n < 1) (hε : ∀ n, 0 < ε n)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ n, 0 < q n) ∧
      ∀ n, q n ∣ q (n + 1) ∧ q n < q (n + 1) ∧
        B n * q n ≤ q (n + 1) ∧
        |Int.fract ((q (n + 1) : ℝ) * θ) - target n| < ε n := by
  have ha : ∀ n, 0 ≤ max 0 (target n - ε n) := fun n => le_max_left _ _
  have hab : ∀ n, max 0 (target n - ε n) < min 1 (target n + ε n) := by
    intro n
    apply max_lt
    · apply lt_min
      · norm_num
      · linarith [htarget₀ n, hε n]
    · apply lt_min
      · linarith [htarget₁ n, hε n]
      · linarith [hε n]
  obtain ⟨q, hqzero, hqpos, hq⟩ := exists_divisible_frequencies hθ
    (fun n => max 0 (target n - ε n)) (fun n => min 1 (target n + ε n)) B
    ha hab (fun n => min_le_left _ _) hq₀
  refine ⟨q, hqzero, hqpos, ?_⟩
  intro n
  obtain ⟨hdiv, hlt, hbound, hlo, hhi⟩ := hq n
  refine ⟨hdiv, hlt, hbound, abs_lt.mpr ?_⟩
  constructor
  · have := lt_of_le_of_lt (le_max_right 0 (target n - ε n)) hlo
    linarith
  · have := lt_of_lt_of_le hhi (min_le_right 1 (target n + ε n))
    linarith

end PrescribedPhaseRealization
end Invariant233

end OAI
