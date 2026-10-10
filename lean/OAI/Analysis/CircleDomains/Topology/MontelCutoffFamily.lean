import OAI.Analysis.CircleDomains.Uniformization.MontelEquicontinuity
import Mathlib.Topology.Algebra.Support

namespace OAI

/-! Turn a locally bounded varying-domain holomorphic sequence into an
actual continuous family on the union, retaining every compact tail. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_montel_continuous_family (D : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ G : ℕ → C(ℂ, ℂ),
      (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
        ∀ᶠ n in atTop, EqOn (G n) (F (s n)) K) ∧
      Equicontinuous (fun n (x : ⋃ n, D n) => G n x) ∧
      (∀ x : ⋃ n, D n, ∃ B : ℝ, ∀ n, ‖G n x‖ ≤ B) := by
  obtain ⟨s,hs,φ,hφ,hφD,hφone⟩ := exists_montel_exhaustion_cutoffs D hD hmono
  have hcont (n : ℕ) : Continuous (fun z => φ n z • F (s n) z) := by
    apply ((φ n).continuous.continuousOn.smul (hF (s n)).continuousOn).continuous_of_tsupport_subset
      (hD (s n))
    exact (tsupport_smul_subset_left (f := (φ n : ℂ → ℝ)) (g := F (s n))).trans (hφD n)
  let G : ℕ → C(ℂ, ℂ) := fun n => ⟨fun z => φ n z • F (s n) z,hcont n⟩
  have heq (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ ⋃ n, D n) :
      ∀ᶠ n in atTop, EqOn (G n) (F (s n)) K := by
    filter_upwards [hφone K hK hKU] with n hn
    intro z hz
    change φ n z • F (s n) z = F (s n) z
    rw [hn z hz,one_smul]
  refine ⟨s,hs,G,heq,?_,?_⟩
  · apply equicontinuous_cutoffs_of_local_holomorphic_bounds (fun n => F (s n)) G
    intro x hx
    obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp (isOpen_iUnion hD) x hx
    let r := δ/2
    have hr : 0 < r := half_pos hδ
    have hrδ : r < δ := by dsimp [r]; linarith
    have hbU : closedBall x r ⊆ ⋃ n, D n :=
      (closedBall_subset_ball hrδ).trans hδU
    obtain ⟨M,hM⟩ := hbound (closedBall x r) (isCompact_closedBall x r) hbU
    refine ⟨r,hr,|M|+1,by positivity,?_⟩
    filter_upwards [hφone (closedBall x r) (isCompact_closedBall x r) hbU] with n hn
    have hbD : closedBall x r ⊆ D (s n) := by
      intro z hz
      apply hφD n
      apply subset_closure
      change φ n z ≠ 0
      rw [hn z hz]
      exact one_ne_zero
    refine ⟨(hF (s n)).mono (ball_subset_closedBall.trans hbD),?_,?_⟩
    · intro z hz
      have hm := hM (s n) z (ball_subset_closedBall hz) (hbD (ball_subset_closedBall hz))
      linarith [le_abs_self M]
    · intro z hz
      change φ n z • F (s n) z = F (s n) z
      rw [hn z (ball_subset_closedBall hz),one_smul]
  · intro x
    obtain ⟨M,hM⟩ := hbound {x.val} isCompact_singleton (singleton_subset_iff.mpr x.property)
    refine ⟨max 0 M,?_⟩
    intro n
    by_cases hx : x.val ∈ D (s n)
    · change ‖φ n x.val • F (s n) x.val‖ ≤ max 0 M
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφ n x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n x).2).trans
        ((hM (s n) x (mem_singleton _) hx).trans (le_max_right _ _))
    · have hz : φ n x.val = 0 := by
        by_contra hn
        exact hx (hφD n (subset_closure hn))
      change ‖φ n x.val • F (s n) x.val‖ ≤ max 0 M
      rw [hz,zero_smul,norm_zero]
      exact le_max_left _ _

end CircleDomainRigidity

end

end OAI
