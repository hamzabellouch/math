import OAI.Analysis.SegmentLenses.HeadTests

namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def headLinear (H : Finset V) : FullDual V →ₗ[ℝ] FullDual V where
  toFun := head H
  map_add' := by intros; simp [head, add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [head, mul_smul, Finset.smul_sum]

def tailLinear (H : Finset V) : FullDual V →ₗ[ℝ] FullDual V :=
  LinearMap.id - headLinear H

@[simp] theorem headLinear_apply (H : Finset V) (x : FullDual V) :
    headLinear H x = head H x := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem tailLinear_apply (H : Finset V) (x : FullDual V) :
    tailLinear H x = tail H x := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem tail_unitVector (H : Finset V) (x : FullDual V) (v : V) :
    tail H x (unitVector v) = if v ∈ H then 0 else x (unitVector v) := by
  simp only [tail, _root_.sub_apply, head_unitVector]
  split_ifs <;> simp

@[simp] theorem tail_segmentFunctional (H S : Finset V) :
    tail H (segmentFunctional S) = segmentFunctional (S \ H) := by
  apply dual_ext_test
  intro u
  rw [tail_pairing, segmentFunctional_apply, segmentFunctional_apply]
  change (∑ v ∈ S, (u.coeff.filter (· ∉ H)) v) = _
  simp only [Finsupp.filter_apply]
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

namespace SegmentFamily

def replacement (F : SegmentFamily V) (p : V →₀ ℝ) : Representation V :=
  ⟨F, fun S => ∑ v ∈ S.val, p v⟩

@[simp] theorem replacement_energy (F : SegmentFamily V) (p : V →₀ ℝ) :
    (F.replacement p).energy = F.seminorm p ^ 2 := by
  have _ := decidableEqV
  exact (F.seminorm_sq p).symm

@[simp] theorem replacement_gate [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
    [IntervalSegments V] (F : SegmentFamily V) (p : V →₀ ℝ) (g : V) :
    (F.replacement p).value (unitVector g) = F.boundary p g := by
  rw [Representation.apply_unitVector]
  exact Finset.sum_coe_sort F.sets (fun S => if g ∈ S then ∑ v ∈ S, p v else 0)

end SegmentFamily

namespace Representation

def error (A : Representation V) (p : V →₀ ℝ) : Representation V :=
  ⟨A.family, fun S => A.coeff S - ∑ v ∈ S.val, p v⟩

@[simp] theorem error_value (A : Representation V) (p : V →₀ ℝ) :
    (A.error p).value = A.value - (A.family.replacement p).value := by
  apply dual_ext_test
  intro u
  rw [_root_.sub_apply, Representation.apply_test, Representation.apply_test,
    Representation.apply_test]
  change (∑ S : A.family.sets, (A.coeff S - ∑ v ∈ S.val, p v) *
    (∑ v ∈ S.val, u.coeff v)) =
    (∑ S : A.family.sets, A.coeff S * ∑ v ∈ S.val, u.coeff v) -
    (∑ S : A.family.sets, (∑ v ∈ S.val, p v) * ∑ v ∈ S.val, u.coeff v)
  simp only [sub_mul, Finset.sum_sub_distrib]

@[simp] theorem error_energy (A : Representation V) (p : V →₀ ℝ) :
    (A.error p).energy = ∑ S : A.family.sets, (A.coeff S - ∑ v ∈ S.val, p v) ^ 2 := by
  have _ := decidableEqV
  exact rfl

theorem error_slack_identity (A : Representation V) (p : V →₀ ℝ) (r : ℝ) :
    (A.error p).energy + (r ^ 2 - A.family.seminorm p ^ 2) =
      A.energy - 2 * (∑ S : A.family.sets, A.coeff S * ∑ v ∈ S.val, p v) + r ^ 2 := by
  rw [error_energy, SegmentFamily.seminorm_sq]
  unfold energy
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem energy_nonneg (A : Representation V) : 0 ≤ A.energy := by
  have _ := decidableEqV
  exact
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

theorem member_unique (F : SegmentFamily V) {S T : F.sets} {v : V}
    (hS : v ∈ S.val) (hT : v ∈ T.val) : S = T := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  by_contra hn
  exact Finset.disjoint_left.mp
    (F.disjoint S.property T.property (fun he => hn (Subtype.ext he))) hS hT


def gateTail (F : SegmentFamily V) (H : Finset V) (g : V) : Finset V :=
  if h : ∃ S : F.sets, g ∈ S.val then (Classical.choose h).val \ H else ∅

theorem gateTail_of_mem (F : SegmentFamily V) (H : Finset V) (S : F.sets)
    {g : V} (hg : g ∈ S.val) : F.gateTail H g = S.val \ H := by
  classical
  have hex : ∃ T : F.sets, g ∈ T.val := ⟨S, hg⟩
  rw [gateTail, dite_eq_left hex]
  rw [F.member_unique (Classical.choose_spec hex) hg]

theorem gateTail_segment (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (g : V) :
    F.gateTail H g = ∅ ∨ SegmentSystem.isSegment (F.gateTail H g) := by
  classical
  unfold gateTail
  split_ifs with h
  · let S := Classical.choose h
    apply subinterval_isSegment (F.segment S.val S.property) Finset.sdiff_subset
    intro a ha b hb v hav hvb
    have hS : v ∈ S.val := by
      rw [F.repr S] at ha hb ⊢
      have ha' := (Finset.mem_sdiff.mp ha).1
      have hb' := (Finset.mem_sdiff.mp hb).1
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha').1.trans hav,
        hvb.trans (Finset.mem_Icc.mp hb').2⟩
    exact Finset.mem_sdiff.mpr ⟨hS, fun hv => (Finset.mem_sdiff.mp ha).2 (hH hv hav)⟩
  · exact Or.inl rfl

theorem gateTail_cone (F : SegmentFamily V) {H : Finset V} {g v : V}
    (hg : Gate H g) (hv : v ∈ F.gateTail H g) : g ≤ v := by
  classical
  unfold gateTail at hv
  split_ifs at hv with h
  · let S := Classical.choose h
    have hgm : g ∈ S.val := Classical.choose_spec h
    have hvS := (Finset.mem_sdiff.mp hv).1
    rw [F.repr S] at hgm hvS
    rcases TreeOrder.lower_chain (Finset.mem_Icc.mp hgm).2
      (Finset.mem_Icc.mp hvS).2 with hle | hle
    · exact hle
    · by_contra hn
      exact (Finset.mem_sdiff.mp hv).2 (hg.2 v (lt_of_le_not_ge hle hn))
  · exact False.elim (Finset.notMem_empty _ hv)

theorem exists_gate_of_crossing (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (S : F.sets) (hpS : (∑ v ∈ S.val, p v) ≠ 0)
    (hne : (S.val \ H).Nonempty) : ∃ g ∈ S.val, Gate H g := by
  classical
  have ha : F.first S ∈ H := by
    by_contra hn
    apply hpS
    apply Finset.sum_eq_zero
    intro v hv
    rw [F.repr S] at hv
    exact head_zero_above hH hp hn (Finset.mem_Icc.mp hv).1
  obtain ⟨g, hg, hmin⟩ := Finset.exists_minimal hne
  refine ⟨g, (Finset.mem_sdiff.mp hg).1, (Finset.mem_sdiff.mp hg).2, ?_⟩
  intro v hvg
  have hm : g ∈ Finset.Icc (F.first S) (F.last S) := by
    rw [← F.repr S]; exact (Finset.mem_sdiff.mp hg).1
  rcases TreeOrder.lower_chain hvg.le (Finset.mem_Icc.mp hm).1 with hle | hle
  · exact hH ha hle
  · by_contra hv
    have hvS : v ∈ S.val \ H := Finset.mem_sdiff.mpr ⟨by
      rw [F.repr S]
      exact Finset.mem_Icc.mpr ⟨hle, hvg.le.trans (Finset.mem_Icc.mp hm).2⟩, hv⟩
    exact not_le_of_gt hvg (hmin hvS hvg.le)

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

theorem boundary_tail_expansion (F : SegmentFamily V) (H : Finset V)
    (p : V →₀ ℝ) (g : V) :
    F.boundary p g • segmentFunctional (F.gateTail H g) =
      ∑ S : F.sets, if g ∈ S.val then (∑ v ∈ S.val, p v) •
        segmentFunctional (S.val \ H) else 0 := by
  classical
  rw [boundary, Finset.sum_smul, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hg : g ∈ S.val
  · simp only [hg, ite_true, F.gateTail_of_mem H S hg]
  · simp only [hg, ite_false, zero_smul]



theorem tail_replacement (F : SegmentFamily V) {H K : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (hK : ∀ S ∈ F.sets, S ⊆ K) :
    tail H (F.replacement p).value =
      ∑ g : K.filter (Gate H), F.boundary p g.val • segmentFunctional (F.gateTail H g.val) := by
  classical
  change tailLinear H (∑ S : F.sets, (∑ v ∈ S.val, p v) • segmentFunctional S.val) = _
  rw [map_sum]
  simp only [map_smul, tailLinear_apply, tail_segmentFunctional, F.boundary_tail_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hz : (∑ v ∈ S.val, p v) = 0
  · simp [hz]
  by_cases he : S.val \ H = ∅
  · simp [he, segmentFunctional]
  obtain ⟨g, hgS, hg⟩ := F.exists_gate_of_crossing hH p hp S hz (Finset.nonempty_iff_ne_empty.mpr he)
  have hgK : g ∈ K.filter (Gate H) := Finset.mem_filter.mpr ⟨hK S.val S.property hgS, hg⟩
  rw [Finset.sum_eq_single (⟨g, hgK⟩ : K.filter (Gate H))]
  · simp [hgS]
  · intro g' hg' hne
    have hn : g'.val ∉ S.val := by
      intro hm
      apply hne
      apply Subtype.ext
      exact F.gate_unique S (Finset.mem_filter.mp g'.property).2 hg hm hgS
    simp [hn]
  · simp

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

def scale (A : Representation V) (t : ℝ) : Representation V :=
  ⟨A.family, fun S => t * A.coeff S⟩

@[simp] theorem scale_value (t : ℝ) (A : Representation V) :
    (A.scale t).value = t • A.value := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  change (∑ S : A.family.sets, (t * A.coeff S) • segmentFunctional S.val) =
    t • (∑ S : A.family.sets, A.coeff S • segmentFunctional S.val)
  simp only [Finset.smul_sum, mul_smul]

@[simp] theorem scale_energy (t : ℝ) (A : Representation V) :
    (A.scale t).energy = t ^ 2 * A.energy := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  change (∑ S : A.family.sets, (t * A.coeff S) ^ 2) = t ^ 2 * ∑ S, A.coeff S ^ 2
  simp only [mul_pow, Finset.mul_sum]

end Representation

theorem exists_atomic_law {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) {R : ℝ} (hR : 0 < R) (hn : ‖z‖ ≤ R) :
    ∃ μ : FiniteLaw (Option (LocalFamily K)),
      ∃ A : Option (LocalFamily K) → Representation V,
        (∀ ω, (A ω).energy ≤ R ^ 2) ∧
        (∀ ω S, S ∈ (A ω).family.sets → S ⊆ K) ∧
        μ.expect (fun ω => (A ω).value) = z := by
  classical
  have hzh : head K (R⁻¹ • z) = R⁻¹ • z := by
    change headLinear K (R⁻¹ • z) = _
    rw [map_smul, headLinear_apply, hz]
  have hzn : ‖R⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hn)
  obtain ⟨c, hc, hcz⟩ := mem_atomicBody_of_norm_le_one hK (R⁻¹ • z) hzh hzn
  let μ := coefficientLaw K c hc
  let A := fun ω => (coefficientAtoms K c ω).scale R
  refine ⟨μ, A, ?_, ?_, ?_⟩
  · intro ω
    change ((coefficientAtoms K c ω).scale R).energy ≤ R ^ 2
    rw [Representation.scale_energy]
    exact mul_le_of_le_one_right (sq_nonneg R) (coefficientAtoms_energy K c ω)
  · intro ω S hS
    cases ω with
    | none => exact False.elim (Finset.notMem_empty _ hS)
    | some F => exact F.property S hS
  · change μ.expect (fun ω => ((coefficientAtoms K c ω).scale R).value) = z
    simp only [Representation.scale_value]
    rw [μ.expect_smul, coefficientLaw_mean, hcz, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

@[simp] theorem expect_apply {V : Type*} [SegmentSystem V] (μ : FiniteLaw Ω)
    (f : Ω → FullDual V) (u : Primal V) :
    (μ.expect f) u = μ.mean (fun ω => f ω u) := by
  simp only [expect, mean, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]

@[simp] theorem expect_sum {E ι : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι]
    (μ : FiniteLaw Ω) (f : Ω → ι → E) :
    μ.expect (fun ω => ∑ i, f ω i) = ∑ i, μ.expect (fun ω => f ω i) := by
  simp only [expect, Finset.smul_sum]
  exact Finset.sum_comm

end FiniteLaw


end SegmentLenses

end

end OAI
