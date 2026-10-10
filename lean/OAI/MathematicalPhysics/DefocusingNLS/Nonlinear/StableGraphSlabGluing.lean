import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphReconstruction
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Set.UnionLift

namespace OAI

/-! # Gluing the finite trajectories selected by a stable endpoint sequence

Adjacent closed slabs agree at their endpoints.  Their locally finite cover
therefore gives one continuous trajectory, with the same geometric decay
between the discrete times.  This is a supporting construction; its inputs
are actual finite trajectories and their proved endpoint identities.
-/

open Set Filter Topology

namespace DefocusingNLS

def equalSlabInterval (M : ℝ) (n : ℕ) : Set ℝ :=
  Icc ((n : ℝ) * M) (((n : ℝ) + 1) * M)

theorem equalSlabInterval_floor (M : ℝ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t) :
    t ∈ equalSlabInterval M ⌊t / M⌋₊ := by
  constructor
  · exact (le_div_iff₀ hM).mp (Nat.floor_le (div_nonneg ht hM.le))
  · exact (div_lt_iff₀ hM).mp (Nat.lt_floor_add_one (t / M)) |>.le

theorem equalSlabInterval_cover (M : ℝ) (hM : 0 < M) :
    (⋃ n : ℕ, equalSlabInterval M n) = Ici 0 := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact (mul_nonneg (Nat.cast_nonneg n) hM.le).trans hn.1
  · intro ht
    exact mem_iUnion.mpr ⟨⌊t / M⌋₊, equalSlabInterval_floor M hM t ht⟩

theorem equalSlabInterval_locallyFinite (M : ℝ) (hM : 0 < M) :
    LocallyFinite (equalSlabInterval M) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ((x + 1) / M)
  refine ⟨Iio (x + 1), Iio_mem_nhds (by linarith), (finite_Iio N).subset ?_⟩
  rintro n ⟨t, ht, htx⟩
  have hn : (n : ℝ) < N :=
    ((lt_div_iff₀ hM).mpr (ht.1.trans_lt htx)).trans hN
  exact_mod_cast hn

section Topological

variable {E : Type*} [TopologicalSpace E]

noncomputable def equalSlabPiece (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E)) (n : ℕ) (t : ℝ) : E :=
  u n (projIcc 0 M hM.le (t - (n : ℝ) * M))

theorem continuous_equalSlabPiece (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E)) (n : ℕ) :
    Continuous (equalSlabPiece M hM u n) :=
  (u n).continuous.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))

theorem equalSlabPiece_compatible (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩)
    (i j : ℕ) (t : ℝ) (hi : t ∈ equalSlabInterval M i)
    (hj : t ∈ equalSlabInterval M j) :
    equalSlabPiece M hM u i t = equalSlabPiece M hM u j t := by
  have ordered (i j : ℕ) (hij : i < j) (hi : t ∈ equalSlabInterval M i)
      (hj : t ∈ equalSlabInterval M j) :
      equalSlabPiece M hM u i t = equalSlabPiece M hM u j t := by
    have hle : (j : ℝ) ≤ (i : ℝ) + 1 :=
      (mul_le_mul_iff_left₀ hM).mp (hj.1.trans hi.2)
    have hji : j = i + 1 := by
      have : j ≤ i + 1 := by exact_mod_cast hle
      omega
    subst j
    have ht : t = ((i : ℝ) + 1) * M := by
      have hh := hj.1
      push_cast at hh
      exact le_antisymm hi.2 hh
    have hleft : t - (i : ℝ) * M = M := by rw [ht]; ring
    have hright : t - ((i + 1 : ℕ) : ℝ) * M = 0 := by rw [ht]; push_cast; ring
    unfold equalSlabPiece
    rw [hleft, hright, projIcc_of_mem _ ⟨hM.le, le_rfl⟩,
      projIcc_of_mem _ ⟨le_rfl, hM.le⟩]
    exact hjoin i
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ordered i j hij hi hj
  · rfl
  · exact (ordered j i hji hj hi).symm

noncomputable def gluedSlabPath (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩)
    (t : ℝ) : E :=
  if ht : 0 ≤ t then
    Set.iUnionLift (equalSlabInterval M)
      (fun n x => equalSlabPiece M hM u n x)
      (equalSlabPiece_compatible M hM u hjoin) (Ici 0)
      (equalSlabInterval_cover M hM).symm.subset ⟨t, ht⟩
  else u 0 ⟨0, le_rfl, hM.le⟩

theorem gluedSlabPath_eq (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩)
    (n : ℕ) (t : ℝ) (ht : t ∈ equalSlabInterval M n) :
    gluedSlabPath M hM u hjoin t = equalSlabPiece M hM u n t := by
  have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg n) hM.le).trans ht.1
  rw [gluedSlabPath, dite_eq_left ht0]
  exact Set.iUnionLift_of_mem _ ht

theorem gluedSlabPath_at (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩)
    (n : ℕ) (s : Icc (0 : ℝ) M) :
    gluedSlabPath M hM u hjoin ((n : ℝ) * M + s) = u n s := by
  rw [gluedSlabPath_eq M hM u hjoin n _ ⟨by linarith [s.2.1], by linarith [s.2.2]⟩]
  unfold equalSlabPiece
  rw [add_sub_cancel_left, projIcc_of_mem _ s.2]

theorem continuousOn_gluedSlabPath (M : ℝ) (hM : 0 < M)
    (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩) :
    ContinuousOn (gluedSlabPath M hM u hjoin) (Ici 0) := by
  rw [← equalSlabInterval_cover M hM]
  apply (equalSlabInterval_locallyFinite M hM).continuousOn_iUnion
    (fun _ => isClosed_Icc)
  intro n
  exact (continuous_equalSlabPiece M hM u n).continuousOn.congr
    (fun t ht => gluedSlabPath_eq M hM u hjoin n t ht)

end Topological

theorem gluedSlabPath_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (M : ℝ) (hM : 0 < M) (u : ℕ → C(Icc (0 : ℝ) M, E))
    (hjoin : ∀ n, u n ⟨M, hM.le, le_rfl⟩ = u (n + 1) ⟨0, le_rfl, hM.le⟩)
    (C r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hu : ∀ n s, ‖u n s‖ ≤ C * r ^ n) :
    Tendsto (gluedSlabPath M hM u hjoin) atTop (𝓝 0) := by
  have hfloor : Tendsto (fun t : ℝ => ⌊t / M⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hM)
  have hdecay : Tendsto (fun t : ℝ => C * r ^ ⌊t / M⌋₊) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).comp hfloor).const_mul C
  apply squeeze_zero_norm' _ hdecay
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [gluedSlabPath_eq M hM u hjoin _ t (equalSlabInterval_floor M hM t ht)]
  exact hu _ _

end DefocusingNLS

end OAI
