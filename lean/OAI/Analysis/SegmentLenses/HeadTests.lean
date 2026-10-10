import OAI.Analysis.SegmentLenses.LawRecovery

namespace OAI

/-!
# Common finite norming tests and head localization
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses





theorem exists_norming_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ p : E, ‖p‖ ≤ 1 ∧ f p = ‖f‖ := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : E) (1 : ℝ)).exists_isMaxOn
    (by exact ⟨0, by simp⟩) f.continuous.continuousOn
  have hpn : ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  have hpos : 0 ≤ f p := by
    have h := hmax (by simp : (0 : E) ∈ Metric.closedBall 0 1)
    simpa only [Set.mem_ofPred_eq, map_zero] using h
  have hupper : ‖f‖ ≤ f p := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hpos
    intro v hv
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := hmax (show -v ∈ Metric.closedBall (0 : E) 1 by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_neg, hv, le_refl])
      change f (-v) ≤ f p at h
      rw [map_neg] at h
      linarith
    · exact hmax (by simpa only [Metric.mem_closedBall, dist_zero_right, hv] using le_rfl)
  have hlower : f p ≤ ‖f‖ := calc
    f p ≤ |f p| := le_abs_self _
    _ ≤ ‖f‖ * ‖p‖ := f.le_opNorm p
    _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg _) hpn
  exact ⟨p, hpn, le_antisymm hlower hupper⟩

section HeadTests
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]


def headTestSpace (H : Finset V) : Submodule ℝ (Test V) where
  carrier := {u | ∀ v ∉ H, u.coeff v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro u v hu hv w hw; exact (show u.coeff w + v.coeff w = 0 by rw [hu w hw, hv w hw, add_zero])
  smul_mem' := by intro a u hu w hw; exact (show a * u.coeff w = 0 by rw [hu w hw, mul_zero])

instance headTestFinite (H : Finset V) : FiniteDimensional ℝ (headTestSpace H) := by
  let e : headTestSpace H →ₗ[ℝ] (H → ℝ) :=
    { toFun := fun u v => u.val.coeff v.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective e
  intro u v huv
  apply Subtype.ext
  change u.val.coeff = v.val.coeff
  ext w
  by_cases hw : w ∈ H
  · exact congrFun huv ⟨w, hw⟩
  · rw [u.property w hw, v.property w hw]

def restrictDual (H : Finset V) (x : FullDual V) : headTestSpace H →L[ℝ] ℝ :=
  x.comp ((UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V).comp (headTestSpace H).subtypeL)

theorem norm_restrictDual_le (H : Finset V) (x : FullDual V) : ‖restrictDual H x‖ ≤ ‖x‖ := by
  have _ := decidableEqV
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  have h := x.le_opNorm (u.val : Primal V)
  change ‖x (u.val : Primal V)‖ ≤ ‖x‖ * ‖u.val‖
  simpa only [UniformSpace.Completion.norm_coe] using h

end HeadTests

section NormingTest
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem norm_restrictDual_eq {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) : ‖restrictDual H x‖ = ‖x‖ := by
  apply le_antisymm (norm_restrictDual_le H x)
  apply dual_norm_le x (norm_nonneg (restrictDual H x))
  intro u
  let v : headTestSpace H := ⟨Test.ofFinsupp (u.coeff.filter (· ∈ H)), by
    intro w hw
    exact Finsupp.filter_apply _ _ _ |>.trans (ite_eq_right hw)⟩
  have he : x (u : Primal V) = restrictDual H x v := by
    calc
      x (u : Primal V) = head H x (u : Primal V) := congrArg (fun z : FullDual V => z (u : Primal V)) hx.symm
      _ = x ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V) := head_pairing H x u
      _ = restrictDual H x v := rfl
  rw [he]
  have h := (restrictDual H x).le_opNorm v
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_headTest_le hH u.coeff) (norm_nonneg (restrictDual H x)))


theorem exists_norming_head {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) (hne : x ≠ 0) :
    ∃ p : Test V, p.coeff.support ⊆ H ∧ ‖p‖ = 1 ∧ x (p : Primal V) = ‖x‖ := by
  obtain ⟨p, hp, hpx⟩ := exists_norming_unitBall (restrictDual H x)
  rw [norm_restrictDual_eq hH x hx] at hpx
  change ‖p.val‖ ≤ 1 at hp
  have hs : p.val.coeff.support ⊆ H := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv (p.property v hn)
  have hnorm : ‖p.val‖ = 1 := by
    have h := x.le_opNorm (p.val : Primal V)
    rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe,
      show x (p.val : Primal V) = ‖x‖ from hpx,
      abs_of_nonneg (norm_nonneg x)] at h
    have hxpos := norm_pos_iff.mpr hne
    apply le_antisymm hp
    nlinarith
  exact ⟨p.val, hs, hnorm, hpx⟩

end NormingTest

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem nonempty (μ : FiniteLaw Ω) : Nonempty Ω := by
  by_contra hn
  let : IsEmpty Ω := ⟨fun ω => hn ⟨ω⟩⟩
  have ht := μ.total
  simp at ht

theorem abs_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.mean f| ≤ μ.mean (fun ω => |f ω|) := by
  simpa only [expect_scalar, Real.norm_eq_abs] using μ.norm_expect_le f

theorem mean_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun ω => f ω * c) = μ.mean f * c := by
  simpa only [mul_comm] using μ.mean_mul c f

end FiniteLaw

section ConeReconstruction
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]



theorem cone_reconstruction {H : Finset V} (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (b : Ω → G → ℝ) (J : G → Ω → Finset V)
    (hJ : ∀ g ω, J g ω = ∅ ∨ SegmentSystem.isSegment (J g ω))
    (hcone : ∀ g ω v, v ∈ J g ω → g.val ≤ v) :
    ‖∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω))‖ ≤
      Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) := by
  classical
  let : Nonempty Ω := μ.nonempty
  apply dual_norm_le _ (Real.sqrt_nonneg _)
  intro u
  have hmax : ∀ g : G, ∃ w : Ω, ∀ ω, |∑ v ∈ J g ω, u.coeff v| ≤
      |∑ v ∈ J g w, u.coeff v| := by
    intro g
    obtain ⟨w, hw, hm⟩ := Finset.exists_max_image Finset.univ
      (fun ω => |∑ v ∈ J g ω, u.coeff v|) Finset.univ_nonempty
    exact ⟨w, fun ω => hm ω (Finset.mem_univ _)⟩
  choose choice hc using hmax
  let M : G → ℝ := fun g => |∑ v ∈ J g (choice g), u.coeff v|
  have hd : Pairwise fun g g' : G => Disjoint (J g (choice g)) (J g' (choice g')) := by
    intro g g' hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rcases TreeOrder.lower_chain (hcone g (choice g) v hv) (hcone g' (choice g') v hv') with h | h
    · exact hne (Subtype.ext (gates_incomparable (hG _ g.property) (hG _ g'.property) h))
    · exact hne (Subtype.ext (gates_incomparable (hG _ g'.property) (hG _ g.property) h).symm)
  have hsq : (∑ g : G, M g ^ 2) ≤ ‖u‖ ^ 2 := by
    change (∑ g : G, M g ^ 2) ≤ segmentSeminorm V u.coeff ^ 2
    simpa only [M, sq_abs] using indexed_test_bound u.coeff
      (fun g => J g (choice g)) (fun g => hJ g (choice g)) hd
  have hM : Real.sqrt (∑ g : G, M g ^ 2) ≤ ‖u‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω)))
      (u : Primal V) = ∑ g : G, μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v) := by
    simp only [_root_.sum_apply, FiniteLaw.expect, FiniteLaw.mean, _root_.smul_apply,
      smul_eq_mul, segmentFunctional_apply, mul_assoc]
  rw [he]
  calc
    |∑ g : G, μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| ≤
        ∑ g : G, |μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g : G, μ.mean (fun ω => |b ω g|) * M g := by
      apply Finset.sum_le_sum
      intro g hg
      calc
        |μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| ≤
            μ.mean (fun ω => |σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v|) := μ.abs_mean_le _
        _ ≤ μ.mean (fun ω => |b ω g| * M g) := by
          apply μ.mean_mono
          intro ω
          simp only [abs_mul]
          have hsb : |σ ω| * |b ω g| ≤ |b ω g| :=
            mul_le_of_le_one_left (abs_nonneg _) (hσ ω)
          exact mul_le_mul hsb (hc g ω) (abs_nonneg _) (abs_nonneg _)
        _ = μ.mean (fun ω => |b ω g|) * M g := μ.mean_mul_right _ _
    _ ≤ Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) *
        Real.sqrt (∑ g : G, M g ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) * ‖u‖ :=
      mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)

end ConeReconstruction


end SegmentLenses

end

end OAI
