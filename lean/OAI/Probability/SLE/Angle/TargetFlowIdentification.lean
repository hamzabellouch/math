import OAI.Probability.SLE.Loewner.TargetCutoffTrajectory
import OAI.Probability.SLE.LoewnerReflection

namespace OAI

/-! Identification of the prescribed Euler flow with an actual capacity-two
Loewner witness, including its geometric surviving domain. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

private lemma negative_clock_coefficient (κ : ℝ) (hκ : 0 < κ) (w : ℂ) :
    ((-κ:ℝ):ℂ) * ((a κ:ℂ)/w) = -2*w⁻¹ := by
  have hc : (κ:ℂ)*(a κ:ℂ)=2 := by
    rw [← Complex.ofReal_mul]
    have hr : κ*a κ=2 := by dsimp [a]; field_simp [hκ.ne']
    rw [hr]
    norm_num
  calc
    ((-κ:ℝ):ℂ) * ((a κ:ℂ)/w) = -((κ:ℂ)*(a κ:ℂ))*w⁻¹ := by
      simp only [Complex.ofReal_neg,div_eq_mul_inv]
      ring
    _ = -2*w⁻¹ := by rw [hc]

lemma surviving_cutoff_identifies
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (z : ℂ) (j : ℕ) (hj : 1 ≤ j)
    (hmin : (j:ℝ)⁻¹ < sInf
      ((fun s : ℝ => (cutoffFlow κ b j z s).im) '' Icc 0 (κ*T))) :
    z ∈ survivingDomain γ T ∧ G T z=cutoffFlow κ b j z (κ*T) := by
  let Q (s : ℝ) := cutoffFlow κ b j z (κ*((T:ℝ)-s))
  let w := cutoffFlow κ b j z (κ*T)
  have hj0 : (0:ℝ)<j := by exact_mod_cast (Nat.succ_le_iff.mp hj)
  have ha : 0 < (j:ℝ)⁻¹ := inv_pos.mpr hj0
  have hheight := surviving_cutoff_height κ b z (κ*T) j hj hmin
  have hwheight : (j:ℝ)⁻¹ ≤ w.im :=
    (hheight (κ*T) ⟨mul_nonneg hκ.le T.coe_nonneg,le_rfl⟩).le
  have hQ0 : Q 0=w := by simp only [Q,sub_zero,w]
  have hQd (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) :
      HasDerivWithinAt Q (reverseField (j:ℝ)⁻¹ (U ((T:ℝ)-s).toNNReal) (Q s))
        (Icc 0 (T:ℝ)) s := by
    have hs0 : 0 ≤ (T:ℝ)-s := sub_nonneg.mpr hs.2
    have ht : κ*((T:ℝ)-s) ∈ Icc 0 (κ*T) := by
      constructor
      · exact mul_nonneg hκ.le hs0
      · exact mul_le_mul_of_nonneg_left (sub_le_self _ hs.1) hκ.le
    have hmaps : MapsTo (fun r : ℝ => κ*((T:ℝ)-r)) (Icc 0 (T:ℝ)) (Ici 0) := by
      intro r hr
      exact mul_nonneg hκ.le (sub_nonneg.mpr hr.2)
    have hinner : HasDerivWithinAt (fun r : ℝ => κ*((T:ℝ)-r)) (-κ)
        (Icc 0 (T:ℝ)) s := by
      simpa using (((hasDerivAt_id s).const_sub (T:ℝ)).const_mul κ).hasDerivWithinAt
    have hd := (cutoffFlow_hasDerivWithinAt κ b j hj z _ ht.1).scomp s hinner hmaps
    have hd' : HasDerivWithinAt Q
        ((-κ) • cutoffField κ b j (κ*((T:ℝ)-s)) (Q s)) (Icc 0 (T:ℝ)) s := hd
    apply hd'.congr_deriv
    have hh : (j:ℝ)⁻¹ ≤ (Q s).im := (hheight _ ht).le
    rw [cutoffField_eq_reciprocal κ b j _ (Q s)
      (cutoff_inactive_of_height j hj _ _ hh)]
    simp only [Complex.real_smul]
    rw [negative_clock_coefficient κ hκ,reverseField,reverseCenter_eq hh,hU _ hs0]
  have hback := hw.reverse_flow_identifies T w ha hwheight Q hQ0 hQd
  have hzF : z=F T w := by
    simpa only [Q,sub_self,mul_zero,cutoffFlow_zero κ b j hj z] using hback
  have hwH : w ∈ upperHalfPlane := ha.trans_le hwheight
  constructor
  · rw [hzF]
    exact hw.2.2.2.2.2.2.1 T hwH
  · change G T z=w
    exact (congrArg (G T) hzF).trans (hw.2.2.2.2.2.2.2.2.1 T w hwH)

private lemma rescaled_witness_trajectory
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    let Y := fun s : ℝ => G (s/κ).toNNReal z
    ContinuousOn Y (Icc 0 (κ*T)) ∧ Y 0=z ∧
      (∀ s ∈ Icc 0 (κ*T), (G T z).im ≤ (Y s).im) ∧
      (∀ s ∈ Ico 0 (κ*T), HasDerivWithinAt Y
        ((a κ:ℂ)/(Y s-driverValue b s)) (Ici s) s) := by
  let Y := fun s : ℝ => G (s/κ).toNNReal z
  have hmaps : MapsTo (fun s : ℝ => s/κ) (Icc 0 (κ*T)) (Icc 0 (T:ℝ)) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hκ.le,(div_le_iff₀ hκ).2 (by simpa only [mul_comm] using hs.2)⟩
  have hY : ContinuousOn Y (Icc 0 (κ*T)) :=
    (hw.time_continuousOn T z hz).comp (continuous_id.div_const κ).continuousOn hmaps
  refine ⟨hY,?_,?_,?_⟩
  · simpa only [Y,zero_div,Real.toNNReal_zero] using hw.initial_value z hz.1.1
  · intro s hs
    have hi := hw.imag_antitoneOn T z hz (hmaps hs) ⟨T.coe_nonneg,le_rfl⟩ (hmaps hs).2
    simpa only [Y,Real.toNNReal_coe] using hi
  · intro s hs
    have hs' := hmaps (Ico_subset_Icc_self hs)
    have hinner : HasDerivWithinAt (fun r : ℝ => r/κ) (1/κ)
        (Icc 0 (κ*T)) s := ((hasDerivAt_id s).div_const κ).hasDerivWithinAt
    have hd := (hw.time_derivative T z hz (s/κ) hs').scomp s hinner hmaps
    have hu : U (s/κ).toNNReal=driverValue b s := by
      rw [hU _ hs'.1,mul_div_cancel₀ _ hκ.ne']
    have hd' : HasDerivWithinAt Y
        ((1/κ) • (2/(Y s-(U (s/κ).toNNReal:ℂ)))) (Icc 0 (κ*T)) s := hd
    have hcoef : (1/κ) • (2/(Y s-(U (s/κ).toNNReal:ℂ))) =
        (a κ:ℂ)/(Y s-driverValue b s) := by
      rw [hu]
      simp only [Complex.real_smul,a,div_eq_mul_inv]
      push_cast
      ring
    exact hasDerivWithinAt_Ici_of_Icc hs (hd'.congr_deriv hcoef)

lemma surviving_iff_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (z : ℂ) : Surviving κ b z (κ*T) ↔ z ∈ survivingDomain γ T := by
  constructor
  · rintro ⟨j,hj,hmin⟩
    exact (surviving_cutoff_identifies κ hκ b U γ G F hw hU T z j hj hmin).1
  · intro hz
    obtain ⟨hY,hY0,hh,hYd⟩ := rescaled_witness_trajectory κ hκ b U γ G F hw hU T z hz
    exact surviving_of_positive_trajectory κ b z (κ*T) (mul_nonneg hκ.le T.coe_nonneg)
      _ hY hY0 (G T z).im (hw.imag_positive T z hz) hh hYd

lemma flow_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    flow κ b z (κ*T)=G T z := by
  have hs := (surviving_iff_witness κ hκ b U γ G F hw hU T z).2 hz
  rw [flow,dite_eq_left hs]
  exact (surviving_cutoff_identifies κ hκ b U γ G F hw hU T z
    (Nat.find hs) (Nat.find_spec hs).1 (Nat.find_spec hs).2).2.symm

lemma surviving_iff_witness_real_time
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    Surviving κ b z t ↔ z ∈ survivingDomain γ (t/κ).toNNReal := by
  have he : κ*((t/κ).toNNReal:ℝ)=t := by
    rw [Real.coe_toNNReal _ (div_nonneg ht hκ.le),mul_div_cancel₀ _ hκ.ne']
  simpa only [he] using surviving_iff_witness κ hκ b U γ G F hw hU (t/κ).toNNReal z

lemma flow_eq_witness_real_time
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (t : ℝ) (ht : 0 ≤ t) (z : ℂ)
    (hz : z ∈ survivingDomain γ (t/κ).toNNReal) :
    flow κ b z t=G (t/κ).toNNReal z := by
  have he : κ*((t/κ).toNNReal:ℝ)=t := by
    rw [Real.coe_toNNReal _ (div_nonneg ht hκ.le),mul_div_cancel₀ _ hκ.ne']
  simpa only [he] using flow_eq_witness κ hκ b U γ G F hw hU (t/κ).toNNReal z hz

lemma inverseFlow_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) (w : ℂ) (hwH : w ∈ upperHalfPlane) :
    inverseFlow κ b (κ*T) w=F T w := by
  classical
  have hF : F T w ∈ survivingDomain γ T := hw.2.2.2.2.2.2.1 T hwH
  have hex : ∃ z : ℂ, Surviving κ b z (κ*T) ∧ flow κ b z (κ*T)=w :=
    ⟨F T w,(surviving_iff_witness κ hκ b U γ G F hw hU T _).2 hF,
      (flow_eq_witness κ hκ b U γ G F hw hU T _ hF).trans
        (hw.2.2.2.2.2.2.2.2.1 T w hwH)⟩
  rw [inverseFlow,ite_eq_left hex]
  let z := Classical.epsilon (fun z => Surviving κ b z (κ*T) ∧ flow κ b z (κ*T)=w)
  have hz := Classical.epsilon_spec hex
  have hzH : z ∈ survivingDomain γ T :=
    (surviving_iff_witness κ hκ b U γ G F hw hU T z).1 hz.1
  have he : G T z=w :=
    (flow_eq_witness κ hκ b U γ G F hw hU T z hzH).symm.trans hz.2
  change z=F T w
  calc
    z=F T (G T z) := (hw.2.2.2.2.2.2.2.1 T z hzH).symm
    _=F T w := congrArg (F T) he

lemma trace_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (T : ℝ≥0) : trace κ b T=γ T := by
  have hUT : driverValue b (κ*T)=U T := by
    simpa only [Real.toNNReal_coe] using (hU T T.coe_nonneg).symm
  have he : (fun ε : ℝ => inverseFlow κ b (κ*T)
        (driverValue b (κ*T)+ε*Complex.I)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => F T ((U T:ℂ)+ε*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have hp : ((driverValue b (κ*T):ℂ)+ε*Complex.I) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,
        Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,
        mul_zero,zero_add,add_zero] using hε
    rw [inverseFlow_eq_witness κ hκ b U γ G F hw hU T _ hp,hUT]
  have htip := hw.2.2.2.2.2.2.2.2.2.2.2.2 T
  exact (htip.congr' he.symm).limUnder_eq

end SLEExactGauge.Target

end

end OAI
