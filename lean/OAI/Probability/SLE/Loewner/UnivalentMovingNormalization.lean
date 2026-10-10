import OAI.Probability.SLE.Loewner.UnivalentFamilyPropagation

namespace OAI

/-! Moving normalizations in a compact subset of the half-plane give a
 locally bounded subsequence, using the coarse Bloch estimate. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_moving_normalization_subsequence
    (f : ℕ → ℂ → ℂ) (z : ℕ → ℂ) (s M : ℝ) (hs : 0<s)
    (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hi : ∀ n, InjOn (f n) upperHalfPlane)
    (hz : ∀ n, ‖z n‖=1 ∧ s≤(z n).im)
    (hv : ∀ n, ‖f n (z n)‖≤M)
    (hd : ∀ n, ‖deriv (f n) (z n)‖≤M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ K : Set ℂ, IsCompact K → K⊆upperHalfPlane →
        ∃ C : ℝ, ∀ n, ∀ w∈K, ‖f (σ n) w‖≤C := by
  let K : Set ℂ := sphere 0 1 ∩ {w | s≤w.im}
  have hK : IsCompact K := (isCompact_sphere (0:ℂ) 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKH : K⊆upperHalfPlane := fun w hw => hs.trans_le hw.2
  have hzK (n : ℕ) : z n∈K := by
    exact ⟨by simpa only [mem_sphere,dist_zero_right] using (hz n).1,(hz n).2⟩
  obtain ⟨a,ha,φ,hφ,hlim⟩ := hK.tendsto_subseq hzK
  let R := s/2
  let ρ := R/(128*Real.pi)^2
  have hR : 0<R := half_pos hs
  have hρ : 0<ρ := div_pos hR (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ρ/2) (by positivity)
  let σ : ℕ → ℕ := fun n => φ (n+N)
  have hσ : StrictMono σ := hφ.comp (strictMono_id.add_const N)
  have hball (n : ℕ) : ball (z (σ n)) R ⊆ upperHalfPlane := by
    intro w hw
    have him := Complex.abs_im_le_norm (w-z (σ n))
    have hdw : ‖w-z (σ n)‖<R := by simpa only [mem_ball,dist_eq_norm] using hw
    rw [Complex.sub_im] at him
    have hlower := (abs_lt.mp (him.trans_lt hdw)).1
    have := (hz (σ n)).2
    change 0<w.im
    dsimp [R] at *
    linarith
  have hseed : (upperHalfPlane ∩ familyBoundedLocus (fun n => f (σ n))).Nonempty := by
    refine ⟨a,hKH ha,ρ/2,by positivity,R*M/(128*Real.pi)+M,?_⟩
    intro n w hw
    have hcenter : dist a (z (σ n))<ρ/2 := by
      simpa only [Function.comp_apply,dist_comm] using hN (n+N) (Nat.le_add_left N n)
    have hnear : w∈ball (z (σ n)) ρ := by
      rw [mem_ball] at hw ⊢
      have := dist_triangle w a (z (σ n))
      linarith
    have hg := univalent_coarse_local_bound hR ((hf (σ n)).mono (hball n))
      ((hi (σ n)).mono (hball n)) hnear
    calc
      ‖f (σ n) w‖ ≤ ‖f (σ n) w-f (σ n) (z (σ n))‖+‖f (σ n) (z (σ n))‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ R*‖deriv (f (σ n)) (z (σ n))‖/(128*Real.pi)+M := add_le_add hg.le (hv (σ n))
      _ ≤ R*M/(128*Real.pi)+M := by gcongr; exact hd (σ n)
  have hb := univalent_family_bound_propagates (fun n => f (σ n))
    (fun n => hf (σ n)) (fun n => hi (σ n)) hseed
  refine ⟨σ,hσ,fun L hL hLH => ?_⟩
  exact familyBoundedLocus_compact_bound _ hL (hLH.trans hb)

end SLEExactGauge

end

end OAI
