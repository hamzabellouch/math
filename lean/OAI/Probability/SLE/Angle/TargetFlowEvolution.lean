import OAI.Probability.SLE.Angle.TargetPositiveFlow
import OAI.Probability.SLE.Loewner.TargetInverseProperties

namespace OAI

/-! On each surviving time interval the selected raw flow is a single
positive cutoff trajectory. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma flow_eq_cutoff_on_interval
    (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (j : ℕ) (hj : 1 ≤ j)
    (hmin : (j:ℝ)⁻¹ < sInf ((fun s : ℝ => (cutoffFlow κ b j z s).im) '' Icc 0 T))
    (u : ℝ) (hu : u ∈ Icc 0 T) :
    flow κ b z u=cutoffFlow κ b j z u := by
  have hheight := surviving_cutoff_height κ b z T j hj hmin
  have hj0 : (0:ℝ)<j := by exact_mod_cast (Nat.succ_le_iff.mp hj)
  apply (flow_eq_of_positive_trajectory κ b z u hu.1 (cutoffFlow κ b j z)
    ((cutoffFlow_continuousOn κ b j hj z).mono Icc_subset_Ici_self)
    (cutoffFlow_zero κ b j hj z) ((j:ℝ)⁻¹) (inv_pos.mpr hj0)
    (fun s hs => (hheight s ⟨hs.1,hs.2.trans hu.2⟩).le) ?_).2
  intro s hs
  have hd := (cutoffFlow_hasDerivWithinAt κ b j hj z s hs.1).mono
    (Ici_subset_Ici.mpr hs.1)
  rw [cutoffField_eq_reciprocal κ b j s _
    (cutoff_inactive_of_height j hj _ _
      (hheight s ⟨hs.1,hs.2.le.trans hu.2⟩).le)] at hd
  exact hd

lemma flow_hasDerivWithinAt_of_later_survival
    (κ : ℝ) (b : Driver) (z : ℂ) (T S : ℝ) (hT : 0 ≤ T) (hTS : T<S)
    (hs : Surviving κ b z S) :
    HasDerivWithinAt (flow κ b z)
      ((a κ:ℂ)/(flow κ b z T-driverValue b T)) (Ici 0) T := by
  obtain ⟨j,hj,hmin⟩ := hs
  have hS : 0 ≤ S := hT.trans hTS.le
  have he : flow κ b z =ᶠ[𝓝[Ici 0] T] cutoffFlow κ b j z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hTS)] with u hu huS
    exact flow_eq_cutoff_on_interval κ b z S hS j hj hmin u ⟨hu,huS.le⟩
  have hval := flow_eq_cutoff_on_interval κ b z S hS j hj hmin T ⟨hT,hTS.le⟩
  have hd := cutoffFlow_hasDerivWithinAt κ b j hj z T hT
  rw [cutoffField_eq_reciprocal κ b j T _
    (cutoff_inactive_of_height j hj _ _
      (surviving_cutoff_height κ b z S j hj hmin T ⟨hT,hTS.le⟩).le)] at hd
  rw [← hval] at hd
  exact hd.congr_of_eventuallyEq he hval

lemma flow_zero (κ : ℝ) (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    flow κ b z 0=z := by
  obtain ⟨j,hj,hjz⟩ := Real.exists_nat_pos_inv_lt (show 0 < z.im from hz)
  have hmin : (j:ℝ)⁻¹ < sInf
      ((fun s : ℝ => (cutoffFlow κ b j z s).im) '' Icc 0 0) := by
    simpa only [Icc_self,image_singleton,cutoffFlow_zero κ b j hj,csInf_singleton] using hjz
  exact (flow_eq_cutoff_on_interval κ b z 0 le_rfl j hj hmin 0 ⟨le_rfl,le_rfl⟩).trans
    (cutoffFlow_zero κ b j hj z)

lemma physical_flow_hasDerivWithinAt
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (z : ℂ) (T S : ℝ≥0) (hTS : T<S)
    (hs : Surviving κ b z (κ*S)) :
    HasDerivWithinAt (fun u : ℝ => flow κ b z (κ*u.toNNReal))
      (2/(flow κ b z (κ*T)-(b (κ.toNNReal*T):ℂ))) (Ici 0) T := by
  have hd := flow_hasDerivWithinAt_of_later_survival κ b z (κ*T) (κ*S)
    (mul_nonneg hκ.le T.coe_nonneg) (mul_lt_mul_of_pos_left hTS hκ) hs
  have hi : HasDerivWithinAt (fun u : ℝ => κ*u) κ (Ici 0) T := by
    simpa using ((hasDerivAt_id (T:ℝ)).const_mul κ).hasDerivWithinAt (s := Ici 0)
  have hmaps : MapsTo (fun u : ℝ => κ*u) (Ici 0) (Ici 0) :=
    fun u hu => mul_nonneg hκ.le hu
  have hc := hd.scomp (T:ℝ) hi hmaps
  have he : (fun u : ℝ => flow κ b z (κ*u.toNNReal)) =ᶠ[𝓝[Ici 0] (T:ℝ)]
      (fun u : ℝ => flow κ b z (κ*u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Real.coe_toNNReal u hu]
  have hc' := hc.congr_of_eventuallyEq he (by simp only [Real.toNNReal_coe,Function.comp_apply])
  convert hc' using 1
  simp only [driverValue,Real.toNNReal_mul hκ.le,Real.toNNReal_coe,Complex.real_smul]
  have hcoef : (κ:ℂ)*(a κ:ℂ)=2 := by
    rw [← Complex.ofReal_mul]
    have ha : κ*a κ=2 := by dsimp [a]; field_simp [hκ.ne']
    rw [ha]
    norm_num
  simp only [div_eq_mul_inv]
  rw [← mul_assoc,hcoef]

end SLEExactGauge.Target

end

end OAI
