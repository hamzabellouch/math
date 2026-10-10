import OAI.MathematicalPhysics.RapidForcing.JointSmoothness

namespace OAI

open scoped BigOperators ENNReal Topology NNReal
open Set MeasureTheory
namespace RapidForcing

lemma spatialFDeriv_joint_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Field E} (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => fderiv ℝ (v p.1) p.2) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Space) × Space => v p.1.1 p.2) :=
    hv.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

lemma finite_interval_bounds {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v)
    (T : ℝ) : ∃ L C : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      ‖v t x‖ ≤ L ∧ ‖fderiv ℝ (v t) x‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod K_compact
  obtain ⟨L, hL⟩ := hc.exists_bound_of_continuousOn hv.continuous.continuousOn
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (spatialFDeriv_joint_smooth hv).continuous.continuousOn
  refine ⟨⟨max L 0, le_max_right _ _⟩, ⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact ⟨(hL (t, x) ⟨ht, hx⟩).trans (le_max_left _ _),
      (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)⟩
  · have hxt : x ∉ tsupport (v t) := fun h => hx (hs t ht.1 h)
    rw [hs.zero_off ht.1 hx, fderiv_of_notMem_tsupport ℝ hxt, norm_zero, norm_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

lemma finite_interval_lipschitz {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v)
    (T : ℝ) : ∃ L C : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x : Space, ‖v t x‖ ≤ L) ∧ LipschitzWith C (v t) := by
  obtain ⟨L, C, h⟩ := finite_interval_bounds hv hs T
  refine ⟨L, C, fun t ht => ⟨fun x => (h t ht x).1, ?_⟩⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact (hv.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · intro x
    exact_mod_cast (h t ht x).2

lemma exists_trajectoryOn {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v)
    (a : Space) {T : ℝ} (hT : 0 ≤ T) : ∃ γ : ℝ → Space, TrajectoryOn v a T γ := by
  obtain ⟨L, C, hb⟩ := finite_interval_lipschitz hv hs T
  let R : ℝ≥0 := L * ⟨T, hT⟩
  have hpl : IsPicardLindelof v (⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) a R 0 L C := by
    constructor
    · intro t ht
      exact (hb t ht).2.lipschitzOnWith
    · intro x _
      exact (hv.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht x _
      exact (hb t ht).1 x
    · dsimp [R]
      simp only [sub_zero, max_eq_left hT]
      rfl
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma trajectoryOn_unique {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v)
    {a : Space} {T : ℝ} {γ η : ℝ → Space}
    (hγ : TrajectoryOn v a T γ) (hη : TrajectoryOn v a T η) :
    EqOn γ η (Icc 0 T) := by
  obtain ⟨L, C, hb⟩ := finite_interval_lipschitz hv hs T
  apply ODE_solution_unique_of_mem_Icc_right (K := C) (s := fun _ => univ)
  · intro t ht
    exact (hb t ⟨ht.1, ht.2.le⟩).2.lipschitzOnWith
  · intro t ht
    exact (hγ.2 t ht).continuousWithinAt
  · intro t ht
    exact (hγ.2 t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · simp
  · intro t ht
    exact (hη.2 t ht).continuousWithinAt
  · intro t ht
    exact (hη.2 t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · simp
  · rw [hγ.1, hη.1]

lemma TrajectoryOn.mono {v : Field Space} {a : Space} {S T : ℝ} {γ : ℝ → Space}
    (h : TrajectoryOn v a T γ) (hST : S ≤ T) : TrajectoryOn v a S γ := by
  refine ⟨h.1, fun t ht => ?_⟩
  exact (h.2 t ⟨ht.1, ht.2.trans hST⟩).mono (Icc_subset_Icc_right hST)

theorem materialFlow_of_smooth_supported {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v) :
    ∃ X : ℝ → Space → Space, MaterialFlow v X := by
  classical
  have hex (a : Space) (n : ℕ) : ∃ γ : ℝ → Space, TrajectoryOn v a ((n : ℝ) + 1) γ :=
    exists_trajectoryOn hv hs a (by positivity)
  choose γ hγ using hex
  have hcoh (a : Space) (n m : ℕ) (t : ℝ) (ht : 0 ≤ t)
      (hn : t ≤ (n : ℝ) + 1) (hm : t ≤ (m : ℝ) + 1) : γ a n t = γ a m t := by
    exact trajectoryOn_unique hv hs ((hγ a n).mono (min_le_left _ _))
      ((hγ a m).mono (min_le_right _ _)) ⟨ht, le_min hn hm⟩
  let X : ℝ → Space → Space := fun t a => γ a (Nat.ceil t) t
  have he (a : Space) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)) :
      X t a = γ a n t := by
    exact hcoh a (Nat.ceil t) n t ht.1 (by have := Nat.le_ceil t; linarith) ht.2
  have hi (a : Space) : X 0 a = a := (hγ a (Nat.ceil 0)).1
  have hd (a : Space) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (fun s => X s a) (v t (X t a)) (Ici 0) t := by
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have htn : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, by linarith⟩
    have hN : Icc (0 : ℝ) ((n : ℝ) + 1) ∈ 𝓝[Ici 0] t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : t < (n : ℝ) + 1))] with s hs hs'
      exact ⟨hs, hs'⟩
    have hD := ((hγ a n).2 t htn).mono_of_mem_nhdsWithin hN
    rw [← he a n htn] at hD
    apply hD.congr_of_eventuallyEq
    · filter_upwards [hN] with s hs
      exact he a n hs
    · exact he a n htn
  refine ⟨X, hi, hd, ?_⟩
  intro T _ a η hη t ht
  have hX : TrajectoryOn v a T (fun s => X s a) :=
    ⟨hi a, fun s hs => (hd a s hs.1).mono Icc_subset_Ici_self⟩
  exact trajectoryOn_unique hv hs hη hX ht

theorem addressed_materialFlow (M : Machine) (w : M.Input) :
    ∃ X : ℝ → Space → Space, MaterialFlow (addressedVelocity M w) X :=
  materialFlow_of_smooth_supported (addressedVelocity_joint_smooth M w)
    (addressedVelocity_supported M w)

lemma solution_unique_Icc {v : Field Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry v)) (hs : Supported v)
    {A B : ℝ} (hA : 0 ≤ A) {γ η : ℝ → Space}
    (hγ : ∀ t ∈ Icc A B, HasDerivWithinAt γ (v t (γ t)) (Icc A B) t)
    (hη : ∀ t ∈ Icc A B, HasDerivWithinAt η (v t (η t)) (Icc A B) t)
    (he : γ A = η A) : EqOn γ η (Icc A B) := by
  obtain ⟨L, C, hb⟩ := finite_interval_lipschitz hv hs B
  apply ODE_solution_unique_of_mem_Icc_right (K := C) (s := fun _ => univ)
  · intro t ht
    exact (hb t ⟨hA.trans ht.1, ht.2.le⟩).2.lipschitzOnWith
  · intro t ht
    exact (hγ t ht).continuousWithinAt
  · intro t ht
    exact (hγ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · simp
  · intro t ht
    exact (hη t ht).continuousWithinAt
  · intro t ht
    exact (hη t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · simp
  · exact he

end RapidForcing

end OAI
