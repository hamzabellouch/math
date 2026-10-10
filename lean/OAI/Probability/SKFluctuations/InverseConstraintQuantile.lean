import Mathlib
import OAI.Probability.SKFluctuations.PhysicalProjection

namespace OAI

/-! Inverse Constraint Quantile. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverseConstraint_lower_slope {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M)
    {x y : ℝ} (hx : x ∈ Icc r₀ 1) (hy : y ∈ Icc r₀ 1) (hxy : x≤y) :
    c*(y-x) ≤ α.val y-α.val x := by
  apply le_trans _ (hα.2.2 x hx y hy hxy).1
  calc
    c*(y-x) = ∫ t in x..y, c := by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring
    _ ≤ ∫ t in x..y, k t := by
      apply intervalIntegral.integral_mono_on hxy intervalIntegrable_const
        ((hk.mono (Icc_subset_Icc hx.1 hy.2)).intervalIntegrable_of_Icc hxy)
      exact fun t ht => hkc t ((Icc_subset_Icc hx.1 hy.2) ht)

 theorem inverseConstraint_strictMonoOn {r₀ u₀ c : ℝ} {k M : ℝ → ℝ} (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M) :
    StrictMonoOn α.val (Icc r₀ 1) := by
  intro x hx y hy hxy
  have hh := inverseConstraint_lower_slope hk hkc hα hx hy hxy.le
  have hp := mul_pos hc (sub_pos.mpr hxy)
  linarith

 theorem inverseConstraint_coSlope {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M)
    {x y : ℝ} (hx : x ∈ Icc r₀ 1) (hy : y ∈ Icc r₀ 1) :
    c*dist x y ≤ dist (α.val x) (α.val y) := by
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (α.property.2 hxy)),neg_sub]
      using inverseConstraint_lower_slope hk hkc hα hx hy hxy
  · simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (α.property.2 hyx))]
      using inverseConstraint_lower_slope hk hkc hα hy hx hyx

 def inverseConstraintMap {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (α : inverseIntegralConstraints r₀ u₀ k M) (t : Icc r₀ 1) : Icc u₀ 1 :=
  ⟨α.val.val t,⟨by simpa only [α.property.1] using α.val.property.2 t.property.1,
    by simpa only [α.property.2.1] using α.val.property.2 t.property.2⟩⟩

 theorem inverseConstraintMap_surjective {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) : Function.Surjective (inverseConstraintMap α) := by
  intro u
  have hu : u.val ∈ Icc (α.val.val r₀) (α.val.val 1) := by
    simpa only [α.property.1,α.property.2.1] using u.property
  obtain ⟨r,hrmem,he⟩ := intermediate_value_Icc hr
    (inverseIntegralConstraints_lipschitz hm hM α.property).continuousOn hu
  exact ⟨⟨r,hrmem⟩,Subtype.ext he⟩

 def inverseConstraintOrderIso {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) : Icc r₀ 1 ≃o Icc u₀ 1 :=
  OrderIso.ofSurjective (OrderEmbedding.ofStrictMono (inverseConstraintMap α)
    (fun x y hxy => inverseConstraint_strictMonoOn hc hk hkc α.property
      x.property y.property hxy)) (inverseConstraintMap_surjective hr hm hM α)

 def constrainedQuantile {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) (u : Icc u₀ 1) : Icc r₀ 1 :=
  (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm u

 theorem constrainedQuantile_spec {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) (u : Icc u₀ 1) :
    α.val.val (constrainedQuantile hr hc hk hkc hm hM α u)=u.val := by
  exact congrArg Subtype.val ((inverseConstraintOrderIso hr hc hk hkc hm hM α).apply_symm_apply u)

 theorem constrainedQuantile_lipschitz {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) :
    LipschitzWith ⟨1/c,by positivity⟩ (constrainedQuantile hr hc hk hkc hm hM α) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := inverseConstraint_coSlope hk hkc α.property
    (constrainedQuantile hr hc hk hkc hm hM α u).property
    (constrainedQuantile hr hc hk hkc hm hM α v).property
  rw [constrainedQuantile_spec,constrainedQuantile_spec] at hh
  change dist (constrainedQuantile hr hc hk hkc hm hM α u).val
      (constrainedQuantile hr hc hk hkc hm hM α v).val ≤ (1/c)*dist u.val v.val
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem constrainedQuantile_joint_continuous {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1) :
    Continuous (fun p : inverseIntegralConstraints r₀ u₀ k M × Icc u₀ 1 =>
      (constrainedQuantile hr hc hk hkc hm hM p.1 p.2).val) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  let t := constrainedQuantile hr hc hk hkc hm hM p.1 p.2
  have hce : Continuous (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc u₀ 1 =>
      q.1.val.val t) :=
    (continuous_apply t.val).comp (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
  have he : Continuous (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc u₀ 1 =>
      (1/c)*dist q.2.val (q.1.val.val t)) :=
    continuous_const.mul ((continuous_subtype_val.comp continuous_snd).dist hce)
  have ht : Tendsto (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc u₀ 1 =>
      (1/c)*dist q.2.val (q.1.val.val t)) (𝓝 p) (𝓝 0) := by
    have hs : p.1.val.val t=p.2.val := constrainedQuantile_spec hr hc hk hkc hm hM p.1 p.2
    simpa only [hs,dist_self,mul_zero] using he.tendsto p
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ ht
  apply Eventually.of_forall
  intro q
  have hh := inverseConstraint_coSlope hk hkc q.1.property
    (constrainedQuantile hr hc hk hkc hm hM q.1 q.2).property t.property
  rw [constrainedQuantile_spec hr hc hk hkc hm hM] at hh
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)

 def constrainedQuantileMap {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) : C(Icc u₀ 1,ℝ) :=
  ⟨fun u => (constrainedQuantile hr hc hk hkc hm hM α u).val,
    continuous_subtype_val.comp (constrainedQuantile_lipschitz hr hc hk hkc hm hM α).continuous⟩

 theorem constrainedQuantileMap_continuous {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1) :
    Continuous (constrainedQuantileMap (u₀ := u₀) hr hc hk hkc hm hM) := by
  exact ContinuousMap.continuous_of_continuous_uncurry _
    (constrainedQuantile_joint_continuous hr hc hk hkc hm hM)

 theorem constrainedQuantileMap_compact {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1) :
    IsCompact (range (constrainedQuantileMap (u₀ := u₀) hr hc hk hkc hm hM)) := by
  let : CompactSpace (inverseIntegralConstraints r₀ u₀ k M) :=
    isCompact_iff_compactSpace.mp (inverseIntegralConstraints_compact r₀ u₀ k M hMc hm)
  exact isCompact_range (constrainedQuantileMap_continuous (u₀ := u₀) hr hc hk hkc hm hM)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Asymptotics
open scoped Topology NNReal

 theorem inverse_perturbation_quotient {A : Type*} {l : Filter A}
    (α ψ : ℝ → ℝ) (r h : A → ℝ) (x a C : ℝ)
    (ha : HasDerivAt α a x) (ha0 : a≠0) (hψ : ContinuousAt ψ x)
    (hr : Tendsto r l (𝓝 x)) (hh : ∀ᶠ t in l, h t≠0)
    (hbound : ∀ᶠ t in l, |r t-x|≤C*|h t|)
    (he : ∀ᶠ t in l, α (r t)+h t*ψ (r t)=α x) :
    Tendsto (fun t => (r t-x)/h t) l (𝓝 (-ψ x/a)) := by
  have hO : (fun t => r t-x) =O[l] h := by
    apply isBigO_iff.mpr
    exact ⟨C,by simpa only [Real.norm_eq_abs] using hbound⟩
  have hoe := (ha.isLittleO.comp_tendsto hr).trans_isBigO hO
  have hz := hoe.tendsto_div_nhds_zero
  simp only [Function.comp_def,smul_eq_mul] at hz
  have hl := ((hψ.tendsto.comp hr).neg.sub hz).div_const a
  simp only [sub_zero] at hl
  apply hl.congr'
  filter_upwards [he,hh] with t het hht
  simp only [Function.comp_def]
  field_simp
  linear_combination -het

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverse_affine_displacement {α ψ r : ℝ → ℝ} {s : Set ℝ} {c A t : ℝ}
    (hc : 0<c) (hco : ∀ x ∈ s, ∀ y ∈ s, c*|x-y|≤|α x-α y|)
    (hψ : ∀ x ∈ s, |ψ x|≤A) (hr0 : r 0 ∈ s) (hrt : r t ∈ s)
    (he : α (r t)+t*ψ (r t)=α (r 0)) :
    |r t-r 0|≤(A/c)*|t| := by
  have hh := hco (r t) hrt (r 0) hr0
  have hh' : α (r t)-α (r 0)=-(t*ψ (r t)) := by linarith
  rw [hh',abs_neg,abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_left (hψ (r t) hrt) (abs_nonneg t)
  have ht : c*|r t-r 0|≤A*|t| := hh.trans (by simpa only [mul_comm] using hb)
  rw [div_mul_eq_mul_div,le_div_iff₀ hc]
  simpa only [mul_comm] using ht

 theorem inverse_affine_hasDerivWithinAt {α ψ r : ℝ → ℝ} {s v : Set ℝ} {c A a : ℝ}
    (hc : 0<c) (hco : ∀ x ∈ s, ∀ y ∈ s, c*|x-y|≤|α x-α y|)
    (hψ : ∀ x ∈ s, |ψ x|≤A) (hψc : ContinuousAt ψ (r 0))
    (hr0 : r 0 ∈ s) (hr : ∀ᶠ t in 𝓝[v \ {0}] 0, r t ∈ s)
    (he : ∀ᶠ t in 𝓝[v \ {0}] 0, α (r t)+t*ψ (r t)=α (r 0))
    (ha : HasDerivAt α a (r 0)) (ha0 : a≠0) :
    HasDerivWithinAt r (-ψ (r 0)/a) v 0 := by
  have hbound : ∀ᶠ t in 𝓝[v \ {0}] 0, |r t-r 0|≤(A/c)*|t| := by
    filter_upwards [hr,he] with t ht het
    exact inverse_affine_displacement hc hco hψ hr0 ht het
  have hlim : Tendsto r (𝓝[v \ {0}] 0) (𝓝 (r 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun t => (A/c)*|t|) (𝓝[v \ {0}] 0) (𝓝 0) from ?_)
    · simpa only [Real.norm_eq_abs] using hbound
    · simpa only [abs_zero,mul_zero] using
        ((continuous_abs.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).const_mul (A/c)
  have hne : ∀ᶠ t in 𝓝[v \ {0}] 0, t≠0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht.2
  have hh := inverse_perturbation_quotient α ψ r id (r 0) a (A/c) ha ha0 hψc hlim hne hbound he
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : slope r 0 = fun t => (r t-r 0)/(t-0) := funext fun t => slope_def_field _ _ _
  rw [hs]
  simpa only [sub_zero,id_eq] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem ae_inverse_pullback {f g : ℝ → ℝ} {s t : Set ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hg : MapsTo g t s)
    (hfg : ∀ u ∈ t, f (g u)=u) {P : ℝ → Prop}
    (hP : ∀ᵐ x ∂volume, x ∈ s → P x) :
    ∀ᵐ u ∂volume, u ∈ t → P (g u) := by
  let B : Set ℝ := {x | x ∈ s ∧ ¬P x}
  have hB : volume B=0 := by
    simpa only [B,Classical.not_imp_iff_and_not] using (ae_iff.mp hP)
  have hi : volume (f '' B)=0 := by
    have hle := (hf.mono (show B ⊆ s from fun x hx => hx.1)).hausdorffMeasure_image_le
      (show (0:ℝ)≤1 by norm_num)
    rw [hausdorffMeasure_real,hB,mul_zero] at hle
    exact le_antisymm hle bot_le
  have hae : ∀ᵐ u ∂volume, u ∉ f '' B := ae_iff.mpr (by simpa only [not_not,ofPred_mem_eq] using hi)
  filter_upwards [hae] with u hu hut
  by_contra hh
  exact hu ⟨g u,⟨hg hut,hh⟩,hfg u hut⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverse_affine_ae_derivative {a b c A : ℝ} {C D : ℝ≥0}
    (hab : a ≤ b) (hc : 0<c) {α ψ : ℝ → ℝ} {r : ℝ → ℝ → ℝ} {s v : Set ℝ}
    (hα : LipschitzOnWith C α (Icc a b)) (hψ : LipschitzOnWith D ψ (Icc a b))
    (hco : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, c*|x-y| ≤ |α x-α y|)
    (hψb : ∀ x ∈ Icc a b, |ψ x| ≤ A)
    (hr0 : MapsTo (r 0) s (Icc a b)) (he0 : ∀ u ∈ s, α (r 0 u)=u)
    (hr : ∀ᶠ t in 𝓝[v \ {0}] 0, MapsTo (r t) s (Icc a b))
    (he : ∀ᶠ t in 𝓝[v \ {0}] 0, ∀ u ∈ s, α (r t u)+t*ψ (r t u)=u)
    (hd : ∀ᵐ x, x ∈ Icc a b → deriv α x≠0) :
    ∀ᵐ u, u ∈ s → HasDerivWithinAt (fun t => r t u)
      (-ψ (r 0 u)/deriv α (r 0 u)) v 0 := by
  have hac : AbsolutelyContinuousOnInterval α a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hab] using hα
  have hdiff : ∀ᵐ x, x ∈ Icc a b → DifferentiableAt ℝ α x := by
    simpa only [uIcc_of_le hab] using hac.ae_differentiableAt
  have hne : ∀ᵐ x : ℝ, x≠a ∧ x≠b := by
    exact (show ∀ᵐ x : ℝ, x≠a from by simp [ae_iff]).and
      (show ∀ᵐ x : ℝ, x≠b from by simp [ae_iff])
  have hg : ∀ᵐ u, u ∈ s → DifferentiableAt ℝ α (r 0 u) ∧
      deriv α (r 0 u)≠0 ∧ ContinuousAt ψ (r 0 u) := by
    apply ae_inverse_pullback (P := fun x => DifferentiableAt ℝ α x ∧ deriv α x≠0 ∧ ContinuousAt ψ x) hα hr0 he0
    filter_upwards [hd,hdiff,hne] with x hx hdx hnx hxi
    exact ⟨hdx hxi,hx hxi,hψ.continuousOn.continuousAt
      (Icc_mem_nhds (lt_of_le_of_ne hxi.1 (Ne.symm hnx.1)) (lt_of_le_of_ne hxi.2 hnx.2))⟩
  filter_upwards [hg] with u hu hus
  exact inverse_affine_hasDerivWithinAt hc hco hψb (hu hus).2.2 (hr0 hus)
    (hr.mono fun t ht => ht hus) (he.mono fun t ht => by rw [he0 u hus]; exact ht u hus)
    (hu hus).1.hasDerivAt (hu hus).2.1

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def sourceInverseConstraints (r₀ u₀ : ℝ) (k M f : ℝ → ℝ) : Prop :=
   f r₀=u₀ ∧ f 1=1 ∧ ∃ C : ℝ≥0, LipschitzOnWith C f (Icc r₀ 1) ∧
     ∀ᵐ t, t ∈ Icc r₀ 1 → k t≤deriv f t ∧ deriv f t≤M (f t)

 theorem sourceInverseConstraints_monotone {r₀ u₀ : ℝ} {k M f : ℝ → ℝ}
    (hr : r₀≤1) (hk : ContinuousOn k (Icc r₀ 1))
    (hk0 : ∀ t ∈ Icc r₀ 1, 0≤k t) (hf : sourceInverseConstraints r₀ u₀ k M f) :
    MonotoneOn f (Icc r₀ 1) := by
  obtain ⟨h₀,h₁,C,hC,hae⟩ := hf
  have hl := (lipschitz_ae_deriv_lower_iff hr hC hk).mp
    (hae.mono fun t ht hti => (ht hti).1)
  intro x hx y hy hxy
  have hi : 0≤∫ t in x..y, k t := intervalIntegral.integral_nonneg
    hxy (fun t ht => hk0 t ⟨hx.1.trans ht.1,ht.2.trans hy.2⟩)
  linarith [hl x hx y hy hxy]

 def sourceInverseExtension {r₀ u₀ : ℝ} {k M f : ℝ → ℝ}
    (hr : r₀≤1) (hu : 0≤u₀) (hk : ContinuousOn k (Icc r₀ 1))
    (hk0 : ∀ t ∈ Icc r₀ 1, 0≤k t) (hf : sourceInverseConstraints r₀ u₀ k M f) :
    boundedMassProfiles :=
  ⟨IccExtend hr (fun t : Icc r₀ 1 => f t), by
    have hm := sourceInverseConstraints_monotone hr hk hk0 hf
    constructor
    · intro t
      change f (projIcc r₀ 1 hr t) ∈ Icc (0:ℝ) 1
      constructor
      · calc
          0 ≤ u₀ := hu
          _ = f r₀ := hf.1.symm
          _ ≤ _ := hm ⟨le_rfl,hr⟩ (projIcc r₀ 1 hr t).property
            (projIcc r₀ 1 hr t).property.1
      · calc
          _ ≤ f 1 := hm (projIcc r₀ 1 hr t).property ⟨hr,le_rfl⟩
              (projIcc r₀ 1 hr t).property.2
          _ = 1 := hf.2.1
    · exact (show Monotone (fun t : Icc r₀ 1 => f t) from
        fun x y hxy => hm x.property y.property hxy).IccExtend hr⟩

 theorem sourceInverseExtension_on {r₀ u₀ : ℝ} {k M f : ℝ → ℝ}
    (hr : r₀≤1) (hu : 0≤u₀) (hk : ContinuousOn k (Icc r₀ 1))
    (hk0 : ∀ t ∈ Icc r₀ 1, 0≤k t) (hf : sourceInverseConstraints r₀ u₀ k M f)
    {t : ℝ} (ht : t ∈ Icc r₀ 1) :
    (sourceInverseExtension hr hu hk hk0 hf).val t=f t := by
  simp only [sourceInverseExtension,IccExtend,Function.comp_apply,projIcc_of_mem hr ht]

 theorem sourceInverseExtension_mem {r₀ u₀ : ℝ} {k M f : ℝ → ℝ}
    (hr : r₀≤1) (hu : 0≤u₀) (hk : ContinuousOn k (Icc r₀ 1))
    (hk0 : ∀ t ∈ Icc r₀ 1, 0≤k t) (hM : Continuous M)
    (hf : sourceInverseConstraints r₀ u₀ k M f) :
    sourceInverseExtension hr hu hk hk0 hf ∈ inverseIntegralConstraints r₀ u₀ k M := by
  refine ⟨?_,?_,?_⟩
  · rw [sourceInverseExtension_on _ _ _ _ _ ⟨le_rfl,hr⟩]; exact hf.1
  · rw [sourceInverseExtension_on _ _ _ _ _ ⟨hr,le_rfl⟩]; exact hf.2.1
  · obtain ⟨C,hC,hae⟩ := hf.2.2
    have hl := (lipschitz_ae_deriv_lower_iff hr hC hk).mp
      (hae.mono fun t ht hti => (ht hti).1)
    have hh := (lipschitz_ae_deriv_upper_iff hr hC (hM.comp_continuousOn hC.continuousOn)).mp
      (hae.mono fun t ht hti => (ht hti).2)
    intro x hx y hy hxy
    simp only [sourceInverseExtension_on _ _ _ _ _ hx,sourceInverseExtension_on _ _ _ _ _ hy]
    refine ⟨hl x hx y hy hxy,?_⟩
    apply (hh x hx y hy hxy).trans_eq
    apply intervalIntegral.integral_congr_Ioo_of_le hxy
    intro t ht
    change M (f t) = M ((sourceInverseExtension hr hu hk hk0 hf).val t)
    exact congrArg M (sourceInverseExtension_on hr hu hk hk0 hf
      ⟨hx.1.trans ht.1.le,ht.2.le.trans hy.2⟩).symm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

section
variable {r₀ u₀ c T : ℝ} {k M ψ : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)
variable (α : inverseIntegralConstraints r₀ u₀ k M)
variable (hT : 0 ≤ T)
variable (hfeas : ∀ t ∈ Icc (0:ℝ) T,
  sourceInverseConstraints r₀ u₀ k M (fun r => α.val.val r+t*ψ r))

 def sourceInverseCurve (t : ℝ) : inverseIntegralConstraints r₀ u₀ k M := by
  classical
  exact if ht : t ∈ Icc (0:ℝ) T then
    ⟨sourceInverseExtension hr hu.1 hk (fun r hr => hc.le.trans (hkc r hr)) (hfeas t ht),
      sourceInverseExtension_mem hr hu.1 hk (fun r hr => hc.le.trans (hkc r hr)) hMc (hfeas t ht)⟩
    else α

 theorem sourceInverseCurve_on {t r : ℝ} (ht : t ∈ Icc (0:ℝ) T) (hr' : r ∈ Icc r₀ 1) :
    (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t).val.val r=α.val.val r+t*ψ r := by
  simp only [sourceInverseCurve,dite_eq_left ht]
  exact sourceInverseExtension_on _ _ _ _ _ hr'

 def sourceForwardCurve (t u : ℝ) : ℝ :=
   (constrainedQuantile hr hc hk hkc hm hM
     (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t) (projIcc u₀ 1 hu.2 u)).val

 theorem sourceForwardCurve_mem (t u : ℝ) :
    sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t u ∈ Icc r₀ 1 :=
   (constrainedQuantile hr hc hk hkc hm hM
     (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t) (projIcc u₀ 1 hu.2 u)).property

 theorem sourceForwardCurve_equation {t u : ℝ} (ht : t ∈ Icc (0:ℝ) T)
    (hU : u ∈ Icc u₀ 1) :
    α.val.val (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t u)+
      t*ψ (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t u)=u := by
  rw [← sourceInverseCurve_on hr hu hc hk hkc hMc α hfeas ht
    (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas t u)]
  unfold sourceForwardCurve
  rw [constrainedQuantile_spec,projIcc_of_mem _ hU]

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

section
variable {r₀ u₀ c T B : ℝ} {k M ψ : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)
variable (α : inverseIntegralConstraints r₀ u₀ k M)
variable (hfeas : ∀ t ∈ Icc (0:ℝ) T,
  sourceInverseConstraints r₀ u₀ k M (fun r => α.val.val r+t*ψ r))

 theorem sourceForwardCurve_initial (hT : 0 ≤ T) {u : ℝ} (hU : u ∈ Icc u₀ 1) :
    α.val.val (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)=u := by
  simpa using sourceForwardCurve_equation hr hu hc hk hkc hm hM hMc α hfeas ⟨le_rfl,hT⟩ hU

 theorem sourceForwardCurve_continuous (t : ℝ) :
    Continuous (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t) := by
  exact continuous_subtype_val.comp
    ((constrainedQuantile_lipschitz hr hc hk hkc hm hM _).continuous.comp continuous_projIcc)

 theorem sourceForwardCurve_displacement (hT : 0 ≤ T) (hψ : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B)
    {t u : ℝ} (ht : t ∈ Icc (0:ℝ) T) (hU : u ∈ Icc u₀ 1) :
    |sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t u-
      sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u| ≤ (B/c)*|t| := by
  apply inverse_affine_displacement hc (α := α.val.val) (ψ := ψ)
    (r := fun v => sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas v u)
    (fun x hx y hy => by simpa only [Real.dist_eq] using inverseConstraint_coSlope hk hkc α.property hx hy)
    hψ (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)
    (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas t u)
  rw [sourceForwardCurve_initial hr hu hc hk hkc hm hM hMc α hfeas hT hU]
  exact sourceForwardCurve_equation hr hu hc hk hkc hm hM hMc α hfeas ht hU

 theorem sourceForwardCurve_ae_derivative (hT : 0 ≤ T) {D : ℝ≥0}
    (hψ : LipschitzOnWith D ψ (Icc r₀ 1)) (hψb : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B) :
    ∀ᵐ u, u ∈ Icc u₀ 1 → HasDerivWithinAt
      (fun t => sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas t u)
      (-ψ (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u)/
        deriv α.val.val (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas 0 u))
      (Icc (0:ℝ) T) 0 := by
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hd : ∀ᵐ r, r ∈ Icc r₀ 1 → deriv α.val.val r≠0 := by
    have hl := (lipschitz_ae_deriv_lower_iff hr hα hk).mpr
      (fun x hx y hy hxy => (α.property.2.2 x hx y hy hxy).1)
    filter_upwards [hl] with r hr' hri
    exact (hc.trans_le ((hkc r hri).trans (hr' hri))).ne'
  apply inverse_affine_ae_derivative hr hc hα hψ
    (fun x hx y hy => by simpa only [Real.dist_eq] using inverseConstraint_coSlope hk hkc α.property hx hy)
    hψb (fun u hu' => sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)
    (fun u hu' => sourceForwardCurve_initial hr hu hc hk hkc hm hM hMc α hfeas hT hu')
    (Eventually.of_forall fun t u hu' => sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas t u) _ hd
  filter_upwards [self_mem_nhdsWithin] with t ht u hu'
  exact sourceForwardCurve_equation hr hu hc hk hkc hm hM hMc α hfeas ht.1 hu'

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverse_velocity_measurable {a b : ℝ} {α ψ r : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Icc a b)) (hr : Continuous r)
    (hm : ∀ u, r u ∈ Icc a b) :
    Measurable (fun u => -ψ (r u)/deriv α (r u)) := by
  exact ((hψ.comp_continuous hr hm).measurable.neg).div (measurable_deriv α |>.comp hr.measurable)

 theorem inverse_velocity_bound {a b c B : ℝ} {α ψ r : ℝ → ℝ} {C : ℝ≥0}
    (hc : 0<c) (hB : 0 ≤ B) (hα : LipschitzOnWith C α (Icc a b))
    (hr : ∀ u ∈ α '' Icc a b, r u ∈ Icc a b)
    (hαr : ∀ u ∈ α '' Icc a b, α (r u)=u)
    (hψ : ∀ x ∈ Icc a b, |ψ x| ≤ B)
    (hd : ∀ᵐ x, x ∈ Icc a b → c ≤ deriv α x) :
    ∀ᵐ u, u ∈ α '' Icc a b → |-ψ (r u)/deriv α (r u)| ≤ B/c := by
  have hp := ae_inverse_pullback hα hr hαr hd
  filter_upwards [hp] with u hu hui
  have hd' := hu hui
  rw [abs_div,abs_neg,abs_of_pos (hc.trans_le hd')]
  exact (div_le_div_of_nonneg_right (hψ (r u) (hr u hui)) (hc.le.trans hd')).trans
    (div_le_div_of_nonneg_left hB hc hd')

 theorem bounded_measurable_intervalIntegrable {a b C : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : Measurable f) (hb : ∀ᵐ u, u ∈ Icc a b → |f u| ≤ C) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact (ae_restrict_iff' measurableSet_Icc).mpr (hb.mono fun u hu hui => by
    simpa only [Real.norm_eq_abs] using hu hui)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def omittedCurve (u₀ : ℝ) (F : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
   if u₀ ≤ u then F (R t u) else 0

 theorem omittedCurve_measurable {u₀ : ℝ} {F : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hF : Continuous F) (hR : ∀ t, Continuous (R t)) (t : ℝ) :
    Measurable (omittedCurve u₀ F R t) := by
  exact Measurable.ite measurableSet_Ici (hF.comp (hR t)).measurable measurable_const

 theorem omittedCurve_bound {u₀ a b D : ℝ} {F : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hD : 0 ≤ D) (hF : ∀ x ∈ Icc a b, |F x| ≤ D)
    (hR : ∀ t u, R t u ∈ Icc a b) (t u : ℝ) : |omittedCurve u₀ F R t u| ≤ D := by
  by_cases hu : u₀ ≤ u
  · simp only [omittedCurve,ite_eq_left hu]; exact hF _ (hR t u)
  · simp only [omittedCurve,ite_eq_right hu,abs_zero]; exact hD

 theorem omittedCurve_integrable {u₀ a b : ℝ} {F : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hF : Continuous F) (hR : ∀ t, Continuous (R t))
    (hm : ∀ t u, R t u ∈ Icc a b) (t : ℝ) :
    IntervalIntegrable (omittedCurve u₀ F R t) volume 0 1 := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  have hD' : ∀ x ∈ Icc a b, |F x| ≤ D := by simpa only [Real.norm_eq_abs] using hD
  apply bounded_measurable_intervalIntegrable (by norm_num) (omittedCurve_measurable hF hR t)
  exact Eventually.of_forall fun u _ => omittedCurve_bound (le_max_left 0 D)
    (fun x hx => (hD' x hx).trans (le_max_right 0 D)) hm t u

 theorem omittedCurve_displacement {u₀ a b A : ℝ} {F : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    {K : ℝ≥0} (hA : 0 ≤ A) (hF : LipschitzOnWith K F (Icc a b))
    (hR : ∀ t u, R t u ∈ Icc a b) {t : ℝ}
    (hd : ∀ u ∈ Icc u₀ 1, |R t u-R 0 u| ≤ A*|t|) :
    ∀ u ∈ Icc (0:ℝ) 1, |omittedCurve u₀ F R t u-omittedCurve u₀ F R 0 u| ≤ |t| *((K:ℝ)*A) := by
  intro u hu
  by_cases hh : u₀ ≤ u
  · simp only [omittedCurve,ite_eq_left hh]
    have hl := hF.dist_le_mul (R t u) (hR t u) (R 0 u) (hR 0 u)
    rw [Real.dist_eq,Real.dist_eq] at hl
    exact hl.trans ((mul_le_mul_of_nonneg_left (hd u ⟨hh,hu.2⟩) K.coe_nonneg).trans_eq (by ring))
  · simp only [omittedCurve,ite_eq_right hh,sub_self,abs_zero]
    exact mul_nonneg (abs_nonneg t) (mul_nonneg K.coe_nonneg hA)

 theorem omittedCurve_hasDerivWithinAt {u₀ a b : ℝ} {F F' V : ℝ → ℝ}
    {R : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hm : ∀ t u, R t u ∈ Icc a b)
    (hd : ∀ᵐ u, u ∈ Icc u₀ 1 → HasDerivWithinAt (fun t => R t u) (V u) s 0) :
    ∀ᵐ u, u ∈ Ioc (0:ℝ) 1 → HasDerivWithinAt (fun t => omittedCurve u₀ F R t u)
      (if u₀ ≤ u then F' (R 0 u)*V u else 0) s 0 := by
  filter_upwards [hd] with u hu hui
  by_cases hh : u₀ ≤ u
  · simp only [omittedCurve,ite_eq_left hh]
    convert (hF (R 0 u) (hm 0 u)).comp_hasDerivWithinAt 0 (hu ⟨hh,hui.2⟩) using 1
    rfl
  · simpa only [omittedCurve,ite_eq_right hh] using (hasDerivWithinAt_const (0:ℝ) s (0:ℝ))

 theorem omittedCurve_rate_integrable {u₀ a b D : ℝ} {F' V R : ℝ → ℝ}
    (hF' : ContinuousOn F' (Icc a b)) (hR : Continuous R)
    (hm : ∀ u, R u ∈ Icc a b) (hV : Measurable V) (hD : 0 ≤ D)
    (hb : ∀ᵐ u, u ∈ Icc u₀ 1 → |V u| ≤ D) :
    IntervalIntegrable (fun u => if u₀ ≤ u then F' (R u)*V u else 0) volume 0 1 := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'
  have hC' : ∀ x ∈ Icc a b, |F' x| ≤ C := by simpa only [Real.norm_eq_abs] using hC
  apply bounded_measurable_intervalIntegrable (C := max 0 C*D) (by norm_num)
    (Measurable.ite measurableSet_Ici ((hF'.comp_continuous hR hm).measurable.mul hV) measurable_const)
  filter_upwards [hb] with u hu hui
  by_cases hh : u₀ ≤ u
  · rw [ite_eq_left hh]
    change |F' (R u)*V u| ≤ max 0 C*D
    rw [abs_mul]
    exact mul_le_mul ((hC' (R u) (hm u)).trans (le_max_right 0 C))
      (hu ⟨hh,hui.2⟩) (abs_nonneg _) (le_max_left 0 C)
  · rw [ite_eq_right hh,abs_zero]
    exact mul_nonneg (le_max_left 0 C) hD

end SKFluctuations.Hierarchy

end

end OAI
