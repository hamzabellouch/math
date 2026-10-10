import Mathlib
import OAI.Probability.SKValue.GroundState.TreeWidths

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

theorem finite_step_guerra_upper {n : ℕ} (hn : 0 < n) (T : GaussianTree)
    (hgrid : ValidTreeGrid 0 T) (hscale : TreeScale 0 T) :
    expectedMaximum n ≤ (n : ℝ)*(fieldProfile 0 T 0-treeCorrection 0 T) := by
  have hm := cascadeMean_mem_closure (auxShape_scale n 0 hscale)
  have hh : closure (range (fun w : CascadeWidths (auxShape n 0 T) ↦
      ∫ y,y ∂cascadeLaw (auxShape n 0 T) w)) ⊆
      {y : ℝ | expectedMaximum n+y ≤ (n : ℝ)*fieldProfile 0 T 0+gumbelTreeMean T} := by
    apply closure_minimal
    · rintro y ⟨w,rfl⟩
      have hu := randomized_tree_guerra_upper hn (resizeTree n 0 T w) (resizeTree_valid n hgrid w)
      change expectedMaximum n+(∫ y,y ∂scalarTreeLaw (auxAmplitude n) 0 (resizeTree n 0 T w))≤_ at hu
      rw [resizeTree_scalarLaw] at hu
      have hf := fieldTreeEval_mean_upper n (resizeTree_scale n 0 hscale w) 0 (fun _ ↦ 0)
      rw [resizeTree_profile,resizeTree_gumbelMean] at hf
      simpa only [Set.mem_ofPred_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hu.trans hf
    · exact isClosed_le (continuous_const.add continuous_id) continuous_const
  have hf := hh hm
  change expectedMaximum n+cascadeMean (auxShape n 0 T) ≤ (n : ℝ)*fieldProfile 0 T 0+gumbelTreeMean T at hf
  rw [auxShape_mean n (by norm_num) hgrid hscale] at hf
  nlinarith

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def profileTree (q : ℝ) : SKValue.HeatProfile → GaussianTree
  | [] => []
  | p::l => ⟨0,q+p.1,p.2⟩::profileTree (q+p.1) l

lemma profileTree_valid {q : ℝ} {l : SKValue.HeatProfile} (h : q+SKValue.profileTime l=1) :
    ValidTreeGrid q (profileTree q l) := by
  induction l generalizing q with
  | nil => simpa only [profileTree,ValidTreeGrid,SKValue.profileTime,add_zero] using h
  | cons p l ih =>
    exact ⟨le_add_of_nonneg_right p.1.coe_nonneg,ih (by simpa only [SKValue.profileTime,add_assoc] using h)⟩

lemma profileTree_scale {a q : ℝ} {l : SKValue.HeatProfile} (ha : 0 ≤ a)
    (hl : l.Pairwise (fun p r ↦ p.2<r.2)) (hb : ∀ p∈l,a<(p.2 : ℝ)) :
    TreeScale a (profileTree q l) := by
  induction l generalizing a q with
  | nil => exact ha
  | cons p l ih =>
    obtain ⟨hpl,hl⟩ := List.pairwise_cons.mp hl
    exact ⟨ha,hb p (List.mem_cons_self ..),ih p.2.coe_nonneg hl (fun r hr ↦ hpl r hr)⟩

lemma profileTree_value (q : ℝ) (l : SKValue.HeatProfile) :
    fieldProfile q (profileTree q l)=SKValue.profileValue abs l 0 := by
  induction l generalizing q with
  | nil => rfl
  | cons p l ih =>
    simp only [profileTree,fieldProfile,SKValue.profileValue,SKValue.patchTime_left _ _ p.1.coe_nonneg,sub_zero,add_sub_cancel_left,ih]

lemma coleHopf_mono_lipschitz {ψ χ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    {m : ℝ} (hm : 0 < m) (h : ℝ) (hb : ∀ x,ψ x≤χ x) (x : ℝ) :
    SKValue.coleHopf m h ψ x≤SKValue.coleHopf m h χ x := by
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat]
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (SKValue.lipschitz_exp_integral_pos hψ hm.le x (Real.sqrt h))
  apply integral_mono (SKValue.lipschitz_exp_integrable hψ hm.le _ _) (SKValue.lipschitz_exp_integrable hχ hm.le _ _)
  intro z
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (hb _) hm.le

lemma profileTree_le_smooth {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
    {a q : ℝ} {l : SKValue.HeatProfile} (h : TreeScale a (profileTree q l)) :
    ∀ x,fieldProfile q (profileTree q l) x≤SKValue.profileValue ψ l 0 x := by
  induction l generalizing a q with
  | nil => exact hb
  | cons p l ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0<(p.2 : ℝ) := ha.trans_lt ham
    have hχ := (hψ.profile_evolution l).slices 0 ⟨le_rfl,SKValue.profileTime_nonneg l⟩
    intro x
    simp only [profileTree,fieldProfile,SKValue.profileValue,SKValue.patchTime_left _ _ p.1.coe_nonneg,sub_zero,add_sub_cancel_left]
    exact coleHopf_mono_lipschitz (fieldProfile_lipschitz hT _) hχ.lipschitz hm _ (ih hT) x

lemma patchTime_integral {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    (∫ s in (0 : ℝ)..(a+b),SKValue.patchTime a f g s)=(∫ s in (0 : ℝ)..a,f s)+(∫ s in (0 : ℝ)..b,g s) := by
  have hi := SKValue.patchTime_intervalIntegrable ha hb hf hg
  have h1 := hi.mono_set (show uIcc (0 : ℝ) a⊆uIcc (0 : ℝ) (a+b) by
    rw [uIcc_of_le ha,uIcc_of_le (add_nonneg ha hb)]; exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hb))
  have h2 := hi.mono_set (show uIcc a (a+b)⊆uIcc (0 : ℝ) (a+b) by
    rw [uIcc_of_le (le_add_of_nonneg_right hb),uIcc_of_le (add_nonneg ha hb)]; exact Icc_subset_Icc ha le_rfl)
  rw [←intervalIntegral.integral_add_adjacent_intervals h1 h2,SKValue.patchTime_integral_left ⟨ha,le_rfl⟩,
    SKValue.patchTime_integral_right (le_add_of_nonneg_right hb),add_sub_cancel_left]

lemma profile_weighted_integrable (q : ℝ) (l : SKValue.HeatProfile) :
    IntervalIntegrable (fun s ↦ (q+s)*SKValue.profileCoeff l s) volume 0 (SKValue.profileTime l) :=
  (SKValue.profileCoeff_integrable l).continuousOn_mul (continuous_const.add continuous_id).continuousOn

lemma profileTree_correction (q : ℝ) (l : SKValue.HeatProfile) :
    treeCorrection q (profileTree q l)=(1/2 : ℝ)*(∫ s in (0 : ℝ)..SKValue.profileTime l,(q+s)*SKValue.profileCoeff l s) := by
  induction l generalizing q with
  | nil => simp [profileTree,treeCorrection,SKValue.profileTime]
  | cons p l ih =>
    have he : (fun s ↦ (q+s)*SKValue.profileCoeff (p::l) s)=
        SKValue.patchTime (p.1 : ℝ) (fun s ↦ (q+s)*(p.2 : ℝ))
          (fun s ↦ (q+(p.1 : ℝ)+s)*SKValue.profileCoeff l s) := by
      funext s
      change (q+s)*(if s≤(p.1 : ℝ) then (p.2 : ℝ) else SKValue.profileCoeff l (s-p.1)) =
        if s≤(p.1 : ℝ) then (q+s)*(p.2 : ℝ) else
          (q+(p.1 : ℝ)+(s-p.1))*SKValue.profileCoeff l (s-p.1)
      split_ifs
      · rfl
      · congr 1; ring
    rw [he,SKValue.profileTime,patchTime_integral p.1.coe_nonneg (SKValue.profileTime_nonneg l)
      ((by fun_prop : Continuous (fun s : ℝ ↦ (q+s)*(p.2 : ℝ))).intervalIntegrable ..) (profile_weighted_integrable _ l)]
    have he2 : (∫ s in (0 : ℝ)..(p.1 : ℝ),(q+s)*(p.2 : ℝ))=
        (p.2 : ℝ)*((q+(p.1 : ℝ))^2-q^2)/2 := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_add (f := fun _ : ℝ ↦ q) (g := fun s : ℝ ↦ s)
        intervalIntegrable_const (continuous_id.intervalIntegrable ..)]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,integral_id]
      ring
    rw [he2,profileTree,treeCorrection,ih]
    ring

end SKValueG

end

end OAI
