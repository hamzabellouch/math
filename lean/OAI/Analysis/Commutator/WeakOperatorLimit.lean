import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem exists_ultralimit (ω : Ultrafilter ι) (T : ι → E →L[ℂ] F)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ∃ V : E →L[ℂ] F, ‖V‖ ≤ C ∧ ∀ x y,
      Tendsto (fun i => inner ℂ (T i x) y) (ω : Filter ι) (𝓝 (inner ℂ (V x) y)) := by
  have he : ∀ x : E, ∀ y : F, ∃ c : ℂ, ‖c‖ ≤ C*‖x‖*‖y‖ ∧
      Tendsto (fun i => inner ℂ (T i x) y) (ω : Filter ι) (𝓝 c) := by
    intro x y
    let f : ι → ℂ := fun i => inner ℂ (T i x) y
    have hf : ∀ i, f i ∈ Metric.closedBall (0 : ℂ) (C*‖x‖*‖y‖) := by
      intro i
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg y))
    obtain ⟨c,hc,hl⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖*‖y‖)).ultrafilter_le_nhds
      (ω.map f) (by
        rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap,Filter.comap_principal]
        exact Filter.le_principal_iff.mpr (Filter.Eventually.of_forall hf))
    exact ⟨c,by simpa only [Metric.mem_closedBall,dist_zero_right] using hc,hl⟩
  choose L hL hlim using he
  have haddY : ∀ x y z, L x (y+z)=L x y+L x z := by
    intro x y z
    apply tendsto_nhds_unique (hlim x (y+z))
    simpa only [inner_add_right] using (hlim x y).add (hlim x z)
  have hsmulY : ∀ x (a : ℂ) y, L x (a • y)=a * L x y := by
    intro x a y
    apply tendsto_nhds_unique (hlim x (a • y))
    simpa only [inner_smul_right] using tendsto_const_nhds.mul (hlim x y)
  let q : E → StrongDual ℂ F := fun x =>
    ({ toFun := L x
       map_add' := haddY x
       map_smul' := fun a y => hsmulY x a y } : F →ₗ[ℂ] ℂ).mkContinuous
      (C*‖x‖) (hL x)
  have hq : ∀ x y, q x y=L x y := fun _ _ => rfl
  have haddX : ∀ x z y, L (x+z) y=L x y+L z y := by
    intro x z y
    apply tendsto_nhds_unique (hlim (x+z) y)
    simpa only [map_add,inner_add_left] using (hlim x y).add (hlim z y)
  have hsmulX : ∀ (a : ℂ) x y, L (a • x) y=star a * L x y := by
    intro a x y
    apply tendsto_nhds_unique (hlim (a • x) y)
    simpa only [map_smul,inner_smul_left,RCLike.star_def] using
      tendsto_const_nhds.mul (hlim x y)
  let V₀ : E →ₗ[ℂ] F :=
    { toFun := fun x => (InnerProductSpace.toDual ℂ F).symm (q x)
      map_add' := by
        intro x z
        apply ext_inner_right ℂ
        intro y
        simp only [inner_add_left,InnerProductSpace.toDual_symm_apply,hq,haddX]
      map_smul' := by
        intro a x
        apply ext_inner_right ℂ
        intro y
        simp only [inner_smul_left,InnerProductSpace.toDual_symm_apply,hq,hsmulX,
          RingHom.id_apply,RCLike.star_def] }
  have hV : ∀ x, ‖V₀ x‖ ≤ C*‖x‖ := by
    intro x
    change ‖(InnerProductSpace.toDual ℂ F).symm (q x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg x)) (hL x)
  refine ⟨V₀.mkContinuous C hV,LinearMap.mkContinuous_norm_le _ hC hV,?_⟩
  intro x y
  change Tendsto _ _ (𝓝 (inner ℂ ((InnerProductSpace.toDual ℂ F).symm (q x)) y))
  rw [InnerProductSpace.toDual_symm_apply,hq]
  exact hlim x y

omit [CompleteSpace F] in
theorem norm_le_of_tendsto {l : Filter ι} [l.NeBot] {T : ι → E →L[ℂ] F}
    {V : E →L[ℂ] F} (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l
      (𝓝 (inner ℂ (V x) y))) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    apply le_of_tendsto (hlim x (V x)).norm
    filter_upwards [hT] with i hi
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg x))) (norm_nonneg _))
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [pow_two,mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorLimit

end

end
end

end OAI
