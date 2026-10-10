import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGlobal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The contact realization preserves polynomial coordinate extent. -/

noncomputable section
namespace ContinuumCoulomb

def contactGridAxis (a : ℤ × ℤ) (i : Fin 2) : ℤ := ![a.1, a.2] i

@[simp] theorem contactGridPoint_apply (a : ℤ × ℤ) (i : Fin 2) :
    contactGridPoint a i = 17 * (contactGridAxis a i : ℝ) := by
  fin_cases i <;> rfl

/-- Every internal strip remains within sixteen coordinate units of its
canonical lower/left lattice endpoint. -/
theorem ContactGridEdge.strip_coordinate_bound (e : ContactGridEdge) (p : ContactStripSite)
    (i : Fin 2) :
    |e.place (contactPoint p.axial p.transverse) i - contactGridPoint e.anchor i| ≤ 16 := by
  obtain ⟨q, hq⟩ := e.place_strip p
  rw [hq]
  cases h : e.vertical <;> fin_cases i <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, horizontalContact, verticalContact,
      contactGridPoint]
  all_goals
    dsimp [contactPoint]
    apply abs_le.mpr
    constructor <;> linarith [q.axial_lower, q.axial_upper, q.transverse_lower, q.transverse_upper]

/-- A source edge's canonical anchor is one of its two actual endpoints. -/
theorem SquareLatticeHeisenberg.contactEdge_anchor (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) :
    (d.contactEdge e).anchor = d.coordinate (d.left e) ∨
      (d.contactEdge e).anchor = d.coordinate (d.right e) := by
  cases h : (d.contactEdge e).reversed
  · left
    simpa only [ContactGridEdge.left, h, Bool.false_eq_true, ite_false] using d.contactEdge_left e
  · right
    simpa only [ContactGridEdge.right, h, ite_true] using d.contactEdge_right e

namespace ContactMediator

theorem globalSite_card (d : SquareLatticeHeisenberg) :
    Fintype.card (GlobalSite d) = d.vertices + 18 * d.edges := by
  simp only [GlobalSite, Fintype.card_fin]
  ring

theorem globalEdge_card (d : SquareLatticeHeisenberg) :
    Fintype.card (GlobalEdge d) = 19 * d.edges := by
  simp only [GlobalEdge, Fintype.card_fin]
  ring

private theorem abs_le_add_abs_sub (x y : ℝ) : |x| ≤ |x - y| + |y| := by
  have h := abs_add_le (x - y) y
  simpa only [sub_add_cancel] using h

/-- Uniform coordinate bounds of the source control the full final graph,
including all eighteen fresh sites per edge. -/
theorem globalPosition_coordinate_bound (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) {M : ℝ}
    (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (x : GlobalSite d) (i : Fin 2) :
    |globalPosition d P x i| ≤ 17 * M + 17 := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  cases x with
  | inl j =>
    rw [globalPosition_old, contactGridPoint_apply, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)]
    linarith [hcoord j i]
  | inr eu =>
    rcases eu with ⟨e, u⟩
    obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
    let z := (d.contactEdge e).place (contactPoint p.axial p.transverse)
    have hanchor : |(contactGridAxis (d.contactEdge e).anchor i : ℝ)| ≤ M := by
      rcases d.contactEdge_anchor e with h | h
      · rw [h]
        exact hcoord (d.left e) i
      · rw [h]
        exact hcoord (d.right e) i
    have hb : |contactGridPoint (d.contactEdge e).anchor i| ≤ 17 * M := by
      rw [contactGridPoint_apply, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)]
      exact mul_le_mul_of_nonneg_left hanchor (by norm_num)
    have hz : |z i| ≤ 17 * M + 16 := by
      have ht := abs_le_add_abs_sub (z i) (contactGridPoint (d.contactEdge e).anchor i)
      have hs := (d.contactEdge e).strip_coordinate_bound p i
      dsimp only [z] at ht ⊢
      linarith
    have hd := contactPoint_coordinate_le_dist z
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u)))) i
    have ht := abs_le_add_abs_sub
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))) i) (z i)
    rw [abs_sub_comm] at ht
    linarith

/-- A fixed logarithmic spacing and polynomial source extent give an
explicit polynomial bound for every realized coordinate. -/
theorem logarithmic_extent_polynomial (k s : ℕ) {N : ℝ} (hN : 2 ≤ N) :
    (k : ℝ) * Real.log N * (17 * N ^ s + 17) ≤ N ^ (k + s + 7) := by
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hk₂ : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hkN : (k : ℝ) ≤ N ^ k := hk₂.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hNp).trans (by linarith)
  have hlog₀ := Real.log_nonneg hN₁
  have hs : 1 ≤ N ^ s := one_le_pow₀ hN₁
  have hsize : 17 * N ^ s + 17 ≤ 34 * N ^ s := by linarith
  have h34 : (34 : ℝ) ≤ N ^ 6 :=
    (by norm_num : (34 : ℝ) ≤ 2 ^ 6).trans (pow_le_pow_left₀ (by norm_num) hN 6)
  calc
    (k : ℝ) * Real.log N * (17 * N ^ s + 17) ≤
        (N ^ k * N) * (34 * N ^ s) :=
      mul_le_mul (mul_le_mul hkN hlog hlog₀ (pow_nonneg hNp.le k)) hsize
        (by positivity) (by positivity)
    _ = 34 * (N ^ k * N ^ s * N) := by ring
    _ ≤ N ^ 6 * (N ^ k * N ^ s * N) :=
      mul_le_mul_of_nonneg_right h34 (by positivity)
    _ = N ^ (k + s + 7) := by
      rw [show k + s + 7 = 6 + k + s + 1 by omega, pow_add, pow_add, pow_add, pow_one]
      ring

end ContactMediator
end ContinuumCoulomb

end

end OAI
