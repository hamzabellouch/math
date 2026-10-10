import OAI.Geometry.NodalSets.Elliptic.RealCompactL2Product

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_compact_mul_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : MeasurableSet K)
    (eta u v : (Fin n → ℝ) → ℝ) (hs : tsupport eta ⊆ K)
    (huv : u =ᵐ[volume.restrict K] v) :
    (fun x ↦ eta x*u x) =ᵐ[volume] (fun x ↦ eta x*v x) := by
  have h := (ae_restrict_iff' hK).mp huv
  filter_upwards [h] with x hx
  by_cases hm : x ∈ K
  · rw [hx hm]
  · rw [image_eq_zero_of_notMem_tsupport (fun he ↦ hm (hs he)),zero_mul,zero_mul]

def realCompactL2Linear {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)) where
  toFun u := (real_compact_localL2_product hK eta u he hs (Lp.memLp u)).toLp (fun x ↦ eta x*u x)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(real_compact_localL2_product hK eta ((u+v : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) he hs (Lp.memLp _)).coeFn_toLp,
      Lp.coeFn_add
        ((real_compact_localL2_product hK eta u he hs (Lp.memLp _)).toLp (fun x ↦ eta x*u x))
        ((real_compact_localL2_product hK eta v he hs (Lp.memLp _)).toLp (fun x ↦ eta x*v x)),
      (real_compact_localL2_product hK eta u he hs (Lp.memLp _)).coeFn_toLp,
      (real_compact_localL2_product hK eta v he hs (Lp.memLp _)).coeFn_toLp,
      real_compact_mul_ae hK.measurableSet eta ((u+v : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) (fun x ↦ u x+v x) hs (Lp.coeFn_add u v)]
      with x h1 h2 h3 h4 h5
    rw [h1,h2,Pi.add_apply,h3,h4,h5,mul_add]
  map_smul' t u := by
    apply Lp.ext
    filter_upwards [(real_compact_localL2_product hK eta ((t • u : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) he hs (Lp.memLp _)).coeFn_toLp,
      Lp.coeFn_smul t
        ((real_compact_localL2_product hK eta u he hs (Lp.memLp _)).toLp (fun x ↦ eta x*u x)),
      (real_compact_localL2_product hK eta u he hs (Lp.memLp _)).coeFn_toLp,
      real_compact_mul_ae hK.measurableSet eta ((t • u : Lp ℝ 2 (volume.restrict K)) : (Fin n → ℝ) → ℝ) (fun x ↦ t*u x) hs (Lp.coeFn_smul t u)]
      with x h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1,h2,Pi.smul_apply,h3,h4]
    change eta x*(t*u x)=t*(eta x*u x)
    ring

theorem realCompactL2Linear_bound {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    ∃ C > 0, ∀ u : Lp ℝ 2 (volume.restrict K), ‖realCompactL2Linear hK eta he hs u‖ ≤ C*‖u‖ := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hK eta he
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u ↦ ?_⟩
  have hn : ‖realCompactL2Linear hK eta he hs u‖^2 = ∫ x, (eta x*u x)^2 :=
    real_toLp_norm_sq _ (real_compact_localL2_product hK eta u he hs (Lp.memLp u))
  have hz : (∫ x, (eta x*u x)^2) = ∫ x in K, (eta x*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),zero_mul,zero_pow (by decide)]
  have hu : ‖u‖^2 = ∫ x in K, (u x)^2 := by
    simpa only [Lp.toLp_coeFn] using real_toLp_norm_sq _ (Lp.memLp u)
  have hb' := (hb u (Lp.memLp u)).2
  rw [← hz,← hn,← hu] at hb'
  have hr : (Real.sqrt C*‖u‖)^2=C*‖u‖^2 := by rw [mul_pow,Real.sq_sqrt hC.le]
  nlinarith [norm_nonneg (realCompactL2Linear hK eta he hs u),
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg u)]

def realCompactL2Map {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  (realCompactL2Linear hK eta he hs).mkContinuous
    (realCompactL2Linear_bound hK eta he hs).choose
    (realCompactL2Linear_bound hK eta he hs).choose_spec.2

theorem realCompactL2Map_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (u : Lp ℝ 2 (volume.restrict K)) :
    (realCompactL2Map hK eta he hs u : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ eta x*u x) :=
  (real_compact_localL2_product hK eta u he hs (Lp.memLp u)).coeFn_toLp

theorem real_indicator_weighted_bound {n : ℕ} {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) :
    ∃ C > 0, ∀ u : (Fin n → ℝ) → ℝ, MemLp u 2 (volume.restrict Q) →
      MemLp (fun x ↦ eta x*Q.indicator u x) 2 volume ∧
      (∫ x, (eta x*Q.indicator u x)^2) ≤ C*(∫ x in Q, (u x)^2) := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hQ eta he
  refine ⟨C,hC,fun u hu ↦ ?_⟩
  have hind : (fun x ↦ eta x*Q.indicator u x)=Q.indicator (fun x ↦ eta x*u x) := by
    funext x
    by_cases hx : x ∈ Q
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,mul_zero]
  have hs : (fun x ↦ (eta x*Q.indicator u x)^2)=Q.indicator (fun x ↦ (eta x*u x)^2) := by
    funext x
    by_cases hx : x ∈ Q
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  refine ⟨?_,?_⟩
  · rw [hind]
    exact (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hb u hu).1
  · change (∫ x, (fun y ↦ (eta y*Q.indicator u y)^2) x) ≤ _
    rw [hs,integral_indicator hQ.measurableSet]
    exact (hb u hu).2

end Yau

end

end OAI
