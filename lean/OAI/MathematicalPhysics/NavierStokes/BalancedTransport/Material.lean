import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_curve_on_interval {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ Continuous γ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt γ (v t (γ t)) (Icc 0 T) t := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let R : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.coe_nonneg hT⟩
  have hp : IsPicardLindelof v t₀ a R 0 L K := by
    constructor
    · intro t ht
      exact (hl t ht.1).lipschitzOnWith
    · intro x _
      exact (hc x).mono Icc_subset_Ici_self
    · intro t ht x _
      exact hb t ht.1 x
    · change (L : ℝ) * max (T - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (L : ℝ) * T - 0
      simp [t₀, max_eq_left hT]
  have ha : a ∈ closedBall a (0 : ℝ≥0) := by simp
  obtain ⟨γ, hγ⟩ := ODE.FunSpace.exists_isFixedPt_next hp ha
  have he : ∀ t ∈ Icc (0 : ℝ) T,
      γ.compProj t = ODE.picard v 0 a γ.compProj t := by
    intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp ha).mp hγ ⟨t, ht⟩
  refine ⟨γ.compProj, ?_, γ.continuous_compProj, fun t ht => ?_⟩
  · rw [he 0 ⟨le_rfl, hT⟩, ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc ⟨le_rfl, hT⟩ hp.continuousOn_uncurry
      γ.continuous_compProj.continuousOn
      (fun s hs => γ.compProj_mem_closedBall hp.mul_max_le) a ht).congr
      he (he t ht)

omit [CompleteSpace E] in
lemma hasDerivWithinAt_forward_of_Icc {γ : ℝ → E} {d : E} {t T : ℝ}
    (hd : HasDerivWithinAt γ d (Icc 0 T) t) (ht : t < T) :
    HasDerivWithinAt γ d (Ici 0) t := by
  apply hd.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs₀ hs₁
  exact ⟨hs₀, hs₁.le⟩

omit [CompleteSpace E] in
lemma curves_agree_on_overlap {v : ℝ → E → E} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {γ δ : ℝ → E} {S T : ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) S))
    (hδ : ContinuousOn δ (Icc (0 : ℝ) T))
    (hdγ : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt γ (v t (γ t)) (Icc 0 S) t)
    (hdδ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt δ (v t (δ t)) (Icc 0 T) t)
    (hinit : γ 0 = δ 0) {t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    γ t = δ t := by
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun s hs => (hl s hs.1).lipschitzOnWith)
      (hγ.mono (Icc_subset_Icc_right htS)) _ (fun _ _ => mem_univ _)
      (hδ.mono (Icc_subset_Icc_right htT)) _ (fun _ _ => mem_univ _) hinit ⟨ht, le_rfl⟩
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdγ s ⟨hs.1, hs.2.le.trans htS⟩)
      (hs.2.trans_le htS)).mono (Ici_subset_Ici.mpr hs.1)
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdδ s ⟨hs.1, hs.2.le.trans htT⟩)
      (hs.2.trans_le htT)).mono (Ici_subset_Ici.mpr hs.1)

theorem exists_global_curve {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t)) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧
      ∀ t, 0 ≤ t → HasDerivWithinAt γ (v t (γ t)) (Ici 0) t := by
  have hex (n : ℕ) := exists_curve_on_interval hc hb hl
    (T := (n : ℝ) + 1) (by positivity) a
  choose C hC₀ hCcts hCd using hex
  have hagree (m n : ℕ) {t : ℝ} (ht : 0 ≤ t)
      (htm : t ≤ (m : ℝ) + 1) (htn : t ≤ (n : ℝ) + 1) : C m t = C n t :=
    curves_agree_on_overlap hl (hCcts m).continuousOn (hCcts n).continuousOn
      (hCd m) (hCd n) ((hC₀ m).trans (hC₀ n).symm) ht htm htn
  let γ : ℝ → E := fun t => C ⌈t⌉₊ t
  have heq (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) : γ t = C n t :=
    hagree ⌈t⌉₊ n ht (by linarith [Nat.le_ceil t]) htn
  refine ⟨γ, hC₀ _, fun t ht => ?_⟩
  let n := ⌈t⌉₊
  have htlt : t < (n : ℝ) + 1 := by dsimp [n]; linarith [Nat.le_ceil t]
  have hd := hasDerivWithinAt_forward_of_Icc (hCd n t ⟨ht, htlt.le⟩) htlt
  have hne : γ =ᶠ[𝓝[Ici 0] t] C n := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt)] with s hs₀ hs₁
    exact heq n hs₀ hs₁.le
  rw [heq n ht htlt.le]
  exact hd.congr_of_eventuallyEq hne (heq n ht htlt.le)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric

theorem exists_materialFlow_of_bounded_lipschitz {U : Velocity} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => U t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖U t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t)) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  choose γ hγ₀ hγd using exists_global_curve hc hb hl
  exact ⟨fun t a => γ a t, hγ₀, hγd⟩

theorem materialFlow_unique {U : Velocity} {X Y : MaterialFlow} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t))
    (hX : IsMaterialFlow U X) (hY : IsMaterialFlow U Y)
    {t : ℝ} (ht : 0 ≤ t) (a : Space) : X t a = Y t a := by
  apply curves_agree_on_overlap hl
      (HasDerivWithinAt.continuousOn (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self))
      (HasDerivWithinAt.continuousOn (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self))
      (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self)
      (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self)
      ((hX.1 a).trans (hY.1 a).symm) ht le_rfl le_rfl

lemma norm_linearMap_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Space →L[ℝ] F) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (Pi.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have he : A x = ∑ i : Fin 3, x i • A (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ i : Fin 3, x i • A (Pi.single i 1)‖ ≤
        ∑ i : Fin 3, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (Pi.single i 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (Pi.single i 1)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

lemma spatial_lipschitz_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ K : ℝ≥0, ∀ t, 0 ≤ t → LipschitzWith K (U t) := by
  choose C hC hbound using fun i : Fin 3 => hb [some i]
  let K : ℝ≥0 := ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i)⟩
  refine ⟨K, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.slice t).differentiable (by simp)) (fun x => ?_)⟩
  change ‖fderiv ℝ (U t) x‖ ≤ ∑ i, C i
  apply (norm_linearMap_le_sum_basis _).trans
  exact Finset.sum_le_sum (fun i _ => hbound i t ht x)

theorem exists_materialFlow_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  obtain ⟨L, hL, hbound⟩ := hb []
  obtain ⟨K, hK⟩ := spatial_lipschitz_of_boundedMixed hU hb
  apply exists_materialFlow_of_bounded_lipschitz (L := ⟨L, hL⟩) (K := K)
  · intro x
    exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · exact hbound
  · exact hK

theorem exists_materialFlow_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) : ∃ X : MaterialFlow, IsMaterialFlow U X :=
  exists_materialFlow_of_boundedMixed hU (boundedMixed_of_compact_repeating hK hU hs hp)

end BalancedTransport.Geometry
end

end OAI
