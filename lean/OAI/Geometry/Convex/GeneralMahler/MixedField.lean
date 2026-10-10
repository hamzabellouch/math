import OAI.Geometry.Convex.GeneralMahler.pRapid
import OAI.Geometry.Convex.GeneralMahler.Cutoff

namespace OAI
/-! Layer integrals and error estimates. -/
noncomputable section
open Filter Set Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

lemma mixed_integral_right {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {f : X → Rn m → F} (h : mixed f) (hm : ∀ x, AEStronglyMeasurable (f x) (normal m)) :
    rapid fun x => ∫ g, f x g ∂normal m := by
  intro n
  obtain ⟨C,k,hc,H⟩ := h n
  let F := fun g:Rn m => C*(1+‖g‖)^k
  have hi : Integrable F (normal m) := (integrable_envelope _).const_mul _
  refine ⟨(∫ g, F g ∂normal m),integral_nonneg (by intro g; dsimp only [F]; positivity), fun x => ?_⟩
  let d := (1+‖x‖)^n
  have hd : 0 < d := by dsimp [d]; positivity
  have he (g : Rn m) : ‖f x g‖ ≤ F g / d := (le_div_iff₀ hd).mpr (H _ _)
  change ‖_‖ * d ≤ _
  apply (le_div_iff₀ hd).mp
  calc
    _ ≤ _ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, F g / d ∂normal m :=
      integral_mono (((hi.div_const _).mono' (hm x) (ae_of_all _ he)).norm) (hi.div_const _) he
    _ = _ := by rw [integral_div]

namespace ProjField
variable (q : ProjField m)
def Gstep (z : ℝ) : Mat m := st z • (1:Mat m)
def Pstep (z : ℝ) (g : Rn m) : Mat m := q.Pmat z g - Gstep z
def PD (z : ℝ) (g : Rn m) : Mat m := p z • (1:Mat m) - q.Pmat z g

lemma meas_XT : Continuous (q.XT.uncurry) := by
  unfold XT sample affineN Function.uncurry
  exact (coneProj_lip q.C).continuous.comp
    ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst))

lemma meas_YT : Continuous (q.YT.uncurry) :=
  (coneProj_lip q.D).continuous.comp
    (((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)).neg)

lemma Pstep_sm : StronglyMeasurable q.Pstep.uncurry := by
  apply StronglyMeasurable.sub
  · apply (strongly_projJac q.C).comp_measurable
    apply Continuous.measurable
    exact (q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)
  · exact (measurable_st.stronglyMeasurable.comp_measurable measurable_fst).smul stronglyMeasurable_const

lemma PD_sm : StronglyMeasurable q.PD.uncurry := by
  apply StronglyMeasurable.sub
  · exact (cp.stronglyMeasurable.comp_measurable measurable_fst).smul stronglyMeasurable_const
  · apply (strongly_projJac q.C).comp_measurable
    exact ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)).measurable

section
variable [NeZero m]
omit [NeZero m] in
lemma one_op_le : ‖(1:Mat m)‖ ≤ 1 := by
  rw [← op_norm,_root_.map_one]
  exact ContinuousLinearMap.norm_id_le

omit [NeZero m] in
lemma Pstep_norm (s g) : ‖q.Pstep s g‖ ≤ 2 := by
  have h : ‖Gstep s (m := m)‖ ≤ 1 := by
    unfold Gstep st; split_ifs <;> simp only [one_smul,zero_smul]
    · exact one_op_le
    simp
  exact (norm_sub_le ..).trans (by linarith [show ‖q.Pmat s g‖ ≤ 1 from projJac_norm ..])

variable (m) in
lemma uniform_Pstep {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ q : ProjField m, q.Bound K → ∀ x y,
      ‖q.Pstep x y‖*(1+‖x‖)^n ≤ C*(1+‖y‖)^n := by
  obtain ⟨a,ha,hh⟩ := negative_cutoff m hK
  obtain ⟨b,hb,hi⟩ := positive_cutoff m hK
  let c := a+b
  have hc : 1 ≤ c := by dsimp [c]; linarith
  refine ⟨2*(1+c)^n,by positivity,?_⟩
  intro q hq x y
  by_cases h : ‖x‖ ≤ c*(1+‖y‖)
  · calc
      _ ≤ 2*((1+c)*(1+‖y‖))^n := by
        have hu := q.Pstep_norm x y
        have hv : 1+‖x‖ ≤ (1+c)*(1+‖y‖) := by linarith [norm_nonneg y]
        gcongr
      _ = _ := by rw [mul_pow,mul_assoc]
  · suffices he : q.Pstep x y = 0 by rw [he,norm_zero,zero_mul]; positivity
    unfold Pstep Gstep st; split_ifs with ht
    · have hx : b*(1+‖y‖) < x := by
        rw [Real.norm_of_nonneg ht] at h; dsimp [c] at h
        nlinarith [norm_nonneg y]
      have he : q.Pmat x y = 1 := projJac_id q.C (hi q hq _ y hx)
      rw [he,one_smul,sub_self]
    · have hx : a*(1+‖y‖) < -x := by
        rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge ht)] at h; dsimp [c] at h
        nlinarith [norm_nonneg y]
      have he : q.Pmat x y = 0 := projJac_zero q.C (by simpa only [neg_neg] using hh q hq _ _ hx)
      rw [he,zero_smul,sub_zero]

lemma Pstep_mixed : mixed q.Pstep := by
  obtain ⟨k,hk⟩ := Field_isBound q
  intro n
  obtain ⟨c,hc,h⟩ := uniform_Pstep m hk.one_le n
  exact ⟨c,n,hc,h q hk⟩

lemma mixed_PD : mixed q.PD := by
  let f := fun z (_:Rn m) => (p z-st z) • (1:Mat m)
  have H : q.PD = fun z g => f z g - q.Pstep z g := by
    ext z g; simp [f,PD,Pstep,Gstep,sub_smul]
  rw [H]
  have hu : mixed f := (mixed.of_rapid (Y := Rn m) rapid_p).mono (fun x y => by
    dsimp only [f]; rw [norm_smul]; exact mul_le_of_le_one_right (by positivity) one_op_le)
  exact hu.sub q.Pstep_mixed

-- h minus its step decays rapidly
lemma tail_H : rapid (fun z : ℝ => q.avH z - st z * q.s0) := by
  let l : Mat m →L[ℝ] ℝ :=
    trL.comp (ContinuousLinearMap.mul ℝ (Mat m) q.covMat)
  have hl (A : Mat m) : l A = trN (q.covMat*A) := by simp [l]
  have hi (z) : Integrable (q.Pstep z) (normal m) :=
    (meanJac_integrable q.C q.root (q.shift z)).sub (integrable_const _)
  have he (z:ℝ) :
      q.avH z - st z * q.s0 = ∫ g, l (q.Pstep z g) ∂normal m := by
    let P (x : Rn m) := q.Pmat z x
    have hm : Integrable P (normal m) := meanJac_integrable ..
    change _ = ∫ g, l (q.Pstep z g) ∂normal m
    rw [l.integral_comp_comm (hi z)]
    have hh : (∫ g, q.Pstep z g ∂normal m) = meanJac q.C q.root (q.shift z) - Gstep z := by
      change ∫ g, (P g-Gstep z) ∂_ = _
      rw [integral_sub hm (integrable_const _)]
      simp [meanJac,P,Pmat,Z,affineN]
    rw [hh,_root_.map_sub,Gstep,_root_.map_smul,hl,hl]
    simp only [smul_eq_mul,mul_one]; rfl
  rw [show (fun z => _) = _ from funext he]
  have hu : mixed (fun z g => l (q.Pstep z g)) := by
    let f := fun (_:ℝ) (_:Rn m) => ‖l‖
    have hf : PolyBound f.uncurry := PolyBound.const ‖l‖
    exact q.Pstep_mixed.product hf (by
      intro x y
      apply (l.le_opNorm _).trans_eq
      change ‖l‖ * _ = _ * ‖‖l‖‖
      rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm])
  exact mixed_integral_right hu fun x => (l.integrable_comp (hi x)).aestronglyMeasurable
end
end ProjField
end GeneralMahler

end

end OAI
