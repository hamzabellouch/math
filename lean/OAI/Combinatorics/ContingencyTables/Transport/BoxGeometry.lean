import OAI.Combinatorics.ContingencyTables.PublishedInputs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Convex.Basic

namespace OAI

/-!
# Finite-box geometry for the conditional conductance argument

Finite unions of grid boxes remain finite unions of boxes under weighted
Minkowski interpolation, giving the domain hypothesis of Prékopa–Leindler.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

private theorem scalar_box_interpolation (t a b c d z : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (hab : a < b) (hcd : c < d)
    (hz : (1 - t) * a + t * c < z ∧ z < (1 - t) * b + t * d) :
    ∃ w : ℝ × ℝ, a < w.1 ∧ w.1 < b ∧ c < w.2 ∧ w.2 < d ∧
      z = (1 - t) * w.1 + t * w.2 := by
  let D := (1 - t) * (b - a) + t * (d - c)
  have hD : 0 < D := add_pos (mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab))
    (mul_pos ht (sub_pos.mpr hcd))
  let wgt := (z - ((1 - t) * a + t * c)) / D
  have hwgt : 0 < wgt := div_pos (sub_pos.mpr hz.1) hD
  have hwgt1 : wgt < 1 := by
    apply (div_lt_one hD).mpr
    dsimp [D]
    linarith [hz.2]
  refine ⟨(a + wgt * (b - a), c + wgt * (d - c)), ?_, ?_, ?_, ?_, ?_⟩
  · linarith [mul_pos hwgt (sub_pos.mpr hab)]
  · nlinarith [mul_pos (sub_pos.mpr hwgt1) (sub_pos.mpr hab)]
  · linarith [mul_pos hwgt (sub_pos.mpr hcd)]
  · nlinarith [mul_pos (sub_pos.mpr hwgt1) (sub_pos.mpr hcd)]
  · dsimp [wgt]
    field_simp
    dsimp [D]
    ring

private theorem finite_box_union_of_fintype {q : ℕ} {K : Type*} [Fintype K]
    (lower upper : K → Point q) :
    IsFiniteBoxUnion {x | ∃ k : K, ∀ i, lower k i < x i ∧ x i < upper k i} := by
  classical
  let e := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, (fun k => lower (e k)), (fun k => upper (e k)), ?_⟩
  ext x
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e.symm k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩

/-- Interpolation preserves exactly the finite-box class appearing in
Prékopa's published integral inequality. -/
theorem IsFiniteBoxUnion.interpolate {q : ℕ} {S T : Set (Point q)}
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    IsFiniteBoxUnion (interpolate t S T) := by
  classical
  obtain ⟨n, l, u, rfl⟩ := hS
  obtain ⟨m, l', u', rfl⟩ := hT
  let K := {p : Fin n × Fin m //
    (∀ i, l p.1 i < u p.1 i) ∧ (∀ i, l' p.2 i < u' p.2 i)}
  let lower : K → Point q := fun p i => (1 - t) * l p.val.1 i + t * l' p.val.2 i
  let upper : K → Point q := fun p i => (1 - t) * u p.val.1 i + t * u' p.val.2 i
  have heq : PublishedInputs.interpolate t {x | ∃ k : Fin n, ∀ i, l k i < x i ∧ x i < u k i}
      {x | ∃ k : Fin m, ∀ i, l' k i < x i ∧ x i < u' k i} =
      {z | ∃ k : K, ∀ i, lower k i < z i ∧ z i < upper k i} := by
    ext z
    constructor
    · rintro ⟨x, ⟨k, hk⟩, y, ⟨k', hk'⟩, rfl⟩
      let p : K := ⟨(k, k'),
        (fun i => (hk i).1.trans (hk i).2),
        (fun i => (hk' i).1.trans (hk' i).2)⟩
      refine ⟨p, ?_⟩
      intro i
      change (1 - t) * l k i + t * l' k' i < (1 - t) * x i + t * y i ∧
        (1 - t) * x i + t * y i < (1 - t) * u k i + t * u' k' i
      constructor
      · exact add_lt_add
          (mul_lt_mul_of_pos_left (hk i).1 (sub_pos.mpr ht1))
          (mul_lt_mul_of_pos_left (hk' i).1 ht)
      · exact add_lt_add
          (mul_lt_mul_of_pos_left (hk i).2 (sub_pos.mpr ht1))
          (mul_lt_mul_of_pos_left (hk' i).2 ht)
    · rintro ⟨p, hp⟩
      have hw (i : Fin q) := scalar_box_interpolation t
        (l p.val.1 i) (u p.val.1 i) (l' p.val.2 i) (u' p.val.2 i) (z i)
        ht ht1 (p.property.1 i) (p.property.2 i) (hp i)
      choose w hw using hw
      refine ⟨(fun i => (w i).1), ⟨p.val.1, ?_⟩,
        (fun i => (w i).2), ⟨p.val.2, ?_⟩, ?_⟩
      · exact fun i => ⟨(hw i).1, (hw i).2.1⟩
      · exact fun i => ⟨(hw i).2.2.1, (hw i).2.2.2.1⟩
      · funext i
        exact (hw i).2.2.2.2
  rw [heq]
  exact finite_box_union_of_fintype lower upper

theorem IsFiniteBoxUnion.isOpen {q : ℕ} {S : Set (Point q)}
    (hS : IsFiniteBoxUnion S) : IsOpen S := by
  obtain ⟨n, l, u, rfl⟩ := hS
  have heq : {x : Point q | ∃ k : Fin n, ∀ i, l k i < x i ∧ x i < u k i} =
      ⋃ k : Fin n, ⋂ i : Fin q, {x : Point q | l k i < x i ∧ x i < u k i} := by
    ext x
    simp
  rw [heq]
  apply isOpen_iUnion
  intro k
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

theorem interpolation_closure_in_box {q : ℕ} {S T : Set (Point q)}
    {lower upper : Point q} (hS : closure S ⊆ Set.Icc lower upper)
    (hT : closure T ⊆ Set.Icc lower upper) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    closure (interpolate t S T) ⊆ Set.Icc lower upper := by
  apply isClosed_Icc.closure_subset_iff.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact convex_Icc lower upper (hS (subset_closure hx)) (hT (subset_closure hy))
    (sub_nonneg.mpr ht1) ht (by ring)

private theorem weighted_geometric_doubling (a b t : ℝ) (ha : 0 < a)
    (hb : 2 * a ≤ b) (ht : 0 ≤ t) :
    (2 : ℝ) ^ t * a ≤ a ^ (1 - t) * b ^ t := by
  have hab : 0 ≤ 2 * a := by positivity
  have hr := Real.rpow_le_rpow hab hb ht
  calc
    (2 : ℝ) ^ t * a = a ^ (1 - t) * (2 * a) ^ t := by
      rw [Real.mul_rpow (by norm_num) ha.le]
      have heq := Real.rpow_add ha (1 - t) t
      have hexp : (1 - t) + t = 1 := by ring
      rw [hexp, Real.rpow_one] at heq
      calc
        (2 : ℝ) ^ t * a = (2 : ℝ) ^ t * (a ^ (1 - t) * a ^ t) :=
          congrArg (fun z => (2 : ℝ) ^ t * z) heq
        _ = a ^ (1 - t) * ((2 : ℝ) ^ t * a ^ t) := by ring
    _ ≤ a ^ (1 - t) * b ^ t :=
      mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg ha.le _)

/-- The interpolation shell gains the mass used in the grid-cut proof.
This conditional result depends only on the precisely identified published
integral inequality; finite-box closure and integrability are proved here. -/
theorem interpolation_shell_gain {q : ℕ} (hPL : FiniteBoxPrekopaLeindler q)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (lower upper : Point q) (S T : Set (Point q)) (ρ : Point q → ℝ)
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (hSc : closure S ⊆ Set.Icc lower upper)
    (hTc : closure T ⊆ Set.Icc lower upper)
    (hρ : ContinuousOn ρ (Set.Icc lower upper))
    (hpos : ∀ x ∈ Set.Icc lower upper, 0 < ρ x)
    (hlc : LogConcaveOn ρ (Set.Icc lower upper))
    (hsub : S ⊆ interpolate t S T)
    (hSmass : 0 < ∫ x in S, ρ x)
    (hTmass : 2 * (∫ x in S, ρ x) ≤ ∫ x in T, ρ x) :
    ((2 : ℝ) ^ t - 1) * (∫ x in S, ρ x) ≤
      ∫ x in (interpolate t S T) \ S, ρ x := by
  have hMc := interpolation_closure_in_box hSc hTc t ht.le ht1.le
  have hM := hS.interpolate hT t ht ht1
  have hint : IntegrableOn ρ (interpolate t S T) :=
    hρ.integrableOn_Icc.mono_set (fun _ hx => hMc (subset_closure hx))
  rw [MeasureTheory.setIntegral_sdiff hS.isOpen.measurableSet hint hsub]
  have hPL' := density_interpolation hPL t ht ht1 lower upper S T ρ
    hS hT hM hSc hTc hMc hρ hpos hlc
  have hgain := weighted_geometric_doubling (∫ x in S, ρ x) (∫ x in T, ρ x)
    t hSmass hTmass ht.le
  nlinarith

end ContingencyTables.PublishedInputs

end OAI
