import OAI.Analysis.BernoulliCone.PositiveFoliation

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

def upperTrace (x:Space 7) (l:ℝ) :ℝ := κ*l*upperSigned (l⁻¹ • x)
lemma upperTrace_continuous (x:Space 7) : ContinuousOn (upperTrace x) (Ioi 0) := by
  intro l hl
  exact ((continuousAt_const.mul continuousAt_id).mul
    (upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ (ne_of_gt hl)).smul continuousAt_const))).continuousWithinAt
lemma upperFamily_eq_max {l:ℝ} (hl:0≤l) (x:Space 7) :
    upperFamily l x=max (upperTrace x l) 0 := by
  rw [upperFamily,upperTrace,mul_max_of_nonneg _ _ (mul_nonneg κ_pos.le hl),mul_zero]
lemma radiusSq_inv_smul_le_iff {l:ℝ} (hl:0<l) (x:Space 7) :
    Cylindrical.radiusSq axis (l⁻¹ • x)≤1 ↔ Cylindrical.radiusSq axis x≤l^2 := by
  rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos hl),one_mul]
lemma upperTrace_right_derivative (x:Space 7) {l:ℝ} (hl:0<l) (hp:0<upperTrace x l) :
    ∃v:ℝ, 0<v ∧ HasDerivWithinAt (upperTrace x) v (Ici l) l := by
  have hqp:=Cylindrical.radiusSq_nonneg axis x axis_norm
  have hs:(fun t:ℝ=>t⁻¹ • x) l=l⁻¹ • x:=rfl
  have hps:0<upperSigned (l⁻¹ • x):=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
  by_cases hq:Cylindrical.radiusSq axis (l⁻¹ • x)≤1
  · have hc:=smoothCap_contDiffAt hq
    let v:=κ*(smoothCap (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient smoothCap (l⁻¹ • x)))
    refine ⟨v,mul_pos κ_pos (smoothCap_radial_defect_pos hq (by rwa [upperSigned_cap hq] at hps)),?_⟩
    have hd:HasDerivAt (fun t:ℝ=>κ*(t*smoothCap (t⁻¹ • x))) v l:=
      (Foliation.hasDerivAt_dilate x hl.ne' (hc.differentiableAt (by norm_num))).const_mul κ
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos:0<t:=hl.trans_le ht
      have hqt:Cylindrical.radiusSq axis (t⁻¹ • x)≤1 := by
        rw [radiusSq_inv_smul_le_iff htpos]
        exact ((radiusSq_inv_smul_le_iff hl x).mp hq).trans ((sq_le_sq₀ hl.le htpos.le).mpr ht)
      rw [upperTrace,upperSigned_cap hqt]
      ring
    · rw [upperTrace,upperSigned_cap hq]
      ring
  · have hq1:1<Cylindrical.radiusSq axis (l⁻¹ • x):=not_le.mp hq
    have hqp':0<Cylindrical.radiusSq axis (l⁻¹ • x):=by linarith
    obtain ⟨hx0,ha⟩:=radiusSq_pos_data hqp'
    let v:=κ*(outerSigned (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient outerSigned (l⁻¹ • x)))
    refine ⟨v,?_,?_⟩
    · rw [show v=κ*(3*capAmplitude*KSup (l⁻¹ • x)) by dsimp [v]; rw [outerSigned_radial_defect hx0 ha]]
      exact mul_pos κ_pos (mul_pos (mul_pos (by norm_num) capAmplitude_pos) (KSup_pos hx0 ha))
    · have hd:HasDerivAt (fun t:ℝ=>κ*(t*outerSigned (t⁻¹ • x))) v l:=
        (Foliation.hasDerivAt_dilate x hl.ne'
          ((outerSigned_contDiffAt (n:=1) hx0 ha).differentiableAt (by norm_num))).const_mul κ
      have hcont:ContinuousAt (fun t:ℝ=>Cylindrical.radiusSq axis (t⁻¹ • x)) l:=
        (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
          ((continuousAt_id.inv₀ hl.ne').smul continuousAt_const)
      apply hd.hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [(hcont.eventually (lt_mem_nhds hq1)).filter_mono nhdsWithin_le_nhds] with t ht
        rw [upperTrace,upperSigned_outer ht.le]
        ring
      · rw [upperTrace,upperSigned_outer hq1.le]
        ring
lemma upperFamily_monotone (x:Space 7) : MonotoneOn (fun l=>upperFamily l x) (Ioi 0) := by
  intro a ha b hb hab
  change upperFamily a x ≤ upperFamily b x
  rw [upperFamily_eq_max ha.le,upperFamily_eq_max hb.le]
  exact Foliation.monotone_positive_part hab
    ((upperTrace_continuous x).mono (fun t ht=>ha.trans_le ht.1))
    (fun t ht hp=>upperTrace_right_derivative x (ha.trans_le ht.1) hp)
lemma upperFamily_strict {x:Space 7} {a b:ℝ} (ha:0<a) (hab:a<b) (hp:0<upperFamily a x) :
    upperFamily a x<upperFamily b x := by
  have hb:0<b:=ha.trans hab
  rw [upperFamily_eq_max ha.le] at hp ⊢
  rw [upperFamily_eq_max hb.le]
  have hpa:0<upperTrace x a:=by simpa using hp
  have hh:=Foliation.strict_increase_above_zero hab
    ((upperTrace_continuous x).mono (fun t ht=>ha.trans_le ht.1)) hpa
    (fun t ht hpt=>upperTrace_right_derivative x (ha.trans_le ht.1) hpt)
  rw [max_eq_left hpa.le,max_eq_left (hpa.trans hh).le]
  exact hh
end Bernoulli.DeSilvaJerison

end
end

end OAI
