import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.NoncommRing

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator-norm closed unit ball, as a subset of the ambient operators. -/
def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

@[simp] theorem mem_unitBall (M : VonNeumannAlgebra H) (x : H →L[ℂ] H) :
    x ∈ unitBall M ↔ x ∈ M ∧ ‖x‖ ≤ 1 := Iff.rfl

@[simp] theorem zero_mem_unitBall (M : VonNeumannAlgebra H) :
    0 ∈ unitBall M := ⟨zero_mem M, by simp⟩

theorem unitBall_nonempty (M : VonNeumannAlgebra H) : (unitBall M).Nonempty :=
  ⟨0, zero_mem_unitBall M⟩

theorem unitBall_bounded (M : VonNeumannAlgebra H) : Bornology.IsBounded (unitBall M) :=
  isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩

/-- Kadison and Kastler's ordinary distance, without matrix amplification. -/
noncomputable def kkDistance (M N : VonNeumannAlgebra H) : ℝ :=
  Metric.hausdorffDist (unitBall M) (unitBall N)

theorem unitBall_hausdorffEDist_ne_top (M N : VonNeumannAlgebra H) :
    Metric.hausdorffEDist (unitBall M) (unitBall N) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (unitBall_nonempty M) (unitBall_nonempty N) (unitBall_bounded M) (unitBall_bounded N)

theorem kkDistance_nonneg (M N : VonNeumannAlgebra H) : 0 ≤ kkDistance M N :=
  Metric.hausdorffDist_nonneg

@[simp] theorem kkDistance_self (M : VonNeumannAlgebra H) : kkDistance M M = 0 :=
  Metric.hausdorffDist_self_zero

theorem kkDistance_comm (M N : VonNeumannAlgebra H) : kkDistance M N = kkDistance N M :=
  Metric.hausdorffDist_comm

theorem kkDistance_triangle (M N P : VonNeumannAlgebra H) :
    kkDistance M P ≤ kkDistance M N + kkDistance N P :=
  Metric.hausdorffDist_triangle (unitBall_hausdorffEDist_ne_top M N)

theorem kkDistance_le_one (M N : VonNeumannAlgebra H) : kkDistance M N ≤ 1 := by
  apply Metric.hausdorffDist_le_of_mem_dist zero_le_one
  · intro x hx
    exact ⟨0, zero_mem_unitBall N, by simpa using hx.2⟩
  · intro x hx
    exact ⟨0, zero_mem_unitBall M, by simpa using hx.2⟩

/-- A strict distance bound supplies a contractive approximant in the other algebra. -/
theorem exists_unitBall_approx {M N : VonNeumannAlgebra H} {x : H →L[ℂ] H}
    (hx : x ∈ unitBall M) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ y ∈ unitBall N, ‖x - y‖ < r := by
  simpa only [dist_eq_norm] using
    Metric.exists_dist_lt_of_hausdorffDist_lt hx hr (unitBall_hausdorffEDist_ne_top M N)

/-- Conjugation by an ambient unitary operator. -/
def unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

@[simp] theorem unitaryConj_one (x : H →L[ℂ] H) : unitaryConj 1 x = x := by
  simp [unitaryConj]

@[simp] theorem norm_unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x‖ = ‖x‖ := by
  simp [unitaryConj, ← Unitary.coe_star]

theorem unitaryConj_sub (v : unitary (H →L[ℂ] H)) (x y : H →L[ℂ] H) :
    unitaryConj v (x - y) = unitaryConj v x - unitaryConj v y := by
  simp [unitaryConj, mul_sub, sub_mul]

theorem isometry_unitaryConj (v : unitary (H →L[ℂ] H)) : Isometry (unitaryConj v) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm, ← unitaryConj_sub, norm_unitaryConj]

@[simp] theorem unitaryConj_star_unitaryConj (v : unitary (H →L[ℂ] H))
    (x : H →L[ℂ] H) : unitaryConj (star v) (unitaryConj v x) = x := by
  simp only [unitaryConj, Unitary.coe_star, star_star]
  calc
    star (v : H →L[ℂ] H) * ((v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)) * v =
        (star (v : H →L[ℂ] H) * v) * x * (star (v : H →L[ℂ] H) * v) := by
      noncomm_ring
    _ = x := by rw [Unitary.star_mul_self_of_mem v.property]; simp

theorem unitaryConj_mul (v w : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    unitaryConj (v * w) x = unitaryConj v (unitaryConj w x) := by
  simp [unitaryConj, mul_assoc]

/-- This expresses `v M v* = N` in the original Hilbert space. -/
def Conjugates (v : unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H) : Prop :=
  unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H))

/-- The conclusion of strong stability, with a strict displacement bound. -/
def NearConjugacy (M N : VonNeumannAlgebra H) (ε : ℝ) : Prop :=
  ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ < ε

@[simp] theorem conjugates_one (M : VonNeumannAlgebra H) : Conjugates 1 M M := by
  simp [Conjugates]

theorem Conjugates.symm {M N : VonNeumannAlgebra H} {v : unitary (H →L[ℂ] H)}
    (hv : Conjugates v M N) : Conjugates (star v) N M := by
  change unitaryConj (star v) '' (N : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  rw [← hv, ← Set.image_comp]
  simp only [Function.comp_def, unitaryConj_star_unitaryConj, Set.image_id']

theorem Conjugates.trans {M N P : VonNeumannAlgebra H}
    {v w : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) (hw : Conjugates w N P) :
    Conjugates (w * v) M P := by
  change unitaryConj (w * v) '' (M : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  simp_rw [unitaryConj_mul]
  rw [← Set.image_image, hv, hw]

theorem nearConjugacy_self (M : VonNeumannAlgebra H) {ε : ℝ} (hε : 0 < ε) :
    NearConjugacy M M ε := by
  exact ⟨1, conjugates_one M, by simpa using hε⟩

theorem unitaryConj_unitBall {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    unitaryConj v '' unitBall M = unitBall N := by
  change unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) at hv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, by simpa using hx.2⟩
    change unitaryConj v x ∈ (N : Set (H →L[ℂ] H))
    rw [← hv]
    exact Set.mem_image_of_mem _ hx.1
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) from
      hv.symm ▸ hy.1)
    exact ⟨x, ⟨hx, by simpa using hy.2⟩, rfl⟩

/-- The elementary displacement estimate used at every matrix level in §2. -/
theorem norm_unitaryConj_sub_le (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x - x‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by
  have hid : unitaryConj v x - x =
      (((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H) +
        x * (star (v : H →L[ℂ] H) - 1) := by
    dsimp [unitaryConj]
    noncomm_ring
  have hstar : ‖star (v : H →L[ℂ] H) - 1‖ = ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [star_sub, star_one] using norm_star ((v : H →L[ℂ] H) - 1)
  calc
    ‖unitaryConj v x - x‖ ≤
        ‖(((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H)‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := hid ▸ norm_add_le _ _
    _ = ‖((v : H →L[ℂ] H) - 1) * x‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ +
          ‖x‖ * ‖star (v : H →L[ℂ] H) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by rw [hstar]; ring

theorem kkDistance_le_of_conjugates {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    kkDistance M N ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ := by
  have hb := unitaryConj_unitBall hv
  apply Metric.hausdorffDist_le_of_mem_dist (mul_nonneg (by norm_num) (norm_nonneg _))
  · intro x hx
    refine ⟨unitaryConj v x, hb ▸ Set.mem_image_of_mem _ hx, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' unitBall M from hb.symm ▸ hy)
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)

/-- The same unitary change of position leaves the distance unchanged. -/
theorem kkDistance_eq_of_conjugates {M N P Q : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hMN : Conjugates v M N) (hPQ : Conjugates v P Q) :
    kkDistance N Q = kkDistance M P := by
  unfold kkDistance
  rw [← unitaryConj_unitBall hMN, ← unitaryConj_unitBall hPQ]
  exact Metric.hausdorffDist_image (isometry_unitaryConj v)

/-- Moving one algebra by a small unitary increases its gap by at most twice
the unitary displacement (the ordinary-distance part of equation (2.1)). -/
theorem kkDistance_conjugate_le {M N P : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v N P) :
    kkDistance M P ≤ kkDistance M N + 2 * ‖(v : H →L[ℂ] H) - 1‖ :=
  (kkDistance_triangle M N P).trans (add_le_add le_rfl (kkDistance_le_of_conjugates hv))

/-- Errors add when two unitary changes of position are composed. -/
theorem norm_unitary_mul_sub_one_le (v w : unitary (H →L[ℂ] H)) :
    ‖((v * w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ ≤
      ‖(v : H →L[ℂ] H) - 1‖ + ‖(w : H →L[ℂ] H) - 1‖ := by
  have hid : (v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1 =
      (v : H →L[ℂ] H) * ((w : H →L[ℂ] H) - 1) + ((v : H →L[ℂ] H) - 1) := by
    noncomm_ring
  change ‖(v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp [add_comm])

theorem NearConjugacy.symm {M N : VonNeumannAlgebra H} {ε : ℝ}
    (h : NearConjugacy M N ε) : NearConjugacy N M ε := by
  obtain ⟨v, hv, hε⟩ := h
  refine ⟨star v, hv.symm, ?_⟩
  have heq : ‖((star v : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((v : H →L[ℂ] H) - 1)
  rw [heq]
  exact hε

theorem NearConjugacy.trans {M N P : VonNeumannAlgebra H} {ε η : ℝ}
    (hMN : NearConjugacy M N ε) (hNP : NearConjugacy N P η) :
    NearConjugacy M P (ε + η) := by
  obtain ⟨v, hv, hε⟩ := hMN
  obtain ⟨w, hw, hη⟩ := hNP
  refine ⟨w * v, hv.trans hw, ?_⟩
  exact (norm_unitary_mul_sub_one_le w v).trans_lt
    (by simpa only [add_comm] using add_lt_add hε hη)

end

end KadisonKastler

end OAI
