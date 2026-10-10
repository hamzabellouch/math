import OAI.Analysis.KadisonKastler.RemoteScalingSequence
import OAI.Analysis.KadisonKastler.ScalingAdjointCommutator

namespace OAI

/-! # Strong convergence of conjugations by remote scaling coisometries -/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem coisometry_conjugation_error_le (w a : Algebra M) (hw : w*star w=1)
    (η : H) : ‖(w*a*star w-a).val η‖ ≤ ‖(a*star w-star w*a).val η‖ := by
  have he : w*a*star w-a=w*(a*star w-star w*a) := by
    rw [mul_sub,← mul_assoc w (star w),hw,one_mul,mul_assoc]
  rw [he]
  have hn : ‖w.val‖ ≤ 1 := coisometry_norm_le w hw
  have ht := w.val.le_opNorm ((a*star w-star w*a).val η)
  change ‖w.val ((a*star w-star w*a).val η)‖ ≤ _
  exact ht.trans (mul_le_of_le_one_left (norm_nonneg _) hn)

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

theorem remoteCopy_adjoint_commutator_tendsto (d : ModularConjugationData M Ω)
    (r : ℕ → ℝ) (v : ℕ → Algebra M) (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (r n) (v n).val)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcr : ∀ᶠ n in atTop, c ≤ r n)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (a*star (S.remoteCopy n (v n))-star (S.remoteCopy n (v n))*a).val η)
      atTop (𝓝 0) := by
  let w (n : ℕ) := S.remoteCopy n (v n)
  have hw (n : ℕ) : w n*star (w n)=1 := by
    change S.remoteCopy n (v n)*star (S.remoteCopy n (v n))=1
    rw [← map_star,← map_mul,hv,map_one]
  have hwscale (n : ℕ) : StateScales M Ω (r n) (w n).val :=
    S.remoteCopy_scales n (v n) (hs n)
  have hbound (n : ℕ) : ‖a*star (w n)-star (w n)*a‖ ≤ 2*‖a‖ := by
    have hn : ‖star (w n)‖ ≤ 1 := by rw [norm_star]; exact coisometry_norm_le _ (hw n)
    calc
      _ ≤ ‖a*star (w n)‖+‖star (w n)*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖star (w n)‖+‖star (w n)‖*‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith [norm_nonneg a]
  apply algebra_strong_tendsto_of_reference Ω
    (commutant_cyclic_of_separating_reference Ω S.separating)
    (fun n => a*star (w n)-star (w n)*a) (2*‖a‖) (by positivity) hbound ?_ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 2*(1+c) := by positivity
  obtain ⟨⟨k,b⟩,hb⟩ := S.twoRatioMatrix_local_cyclic.exists_dist_lt (a.val Ω)
    (div_pos (mul_pos hε hc) hden)
  let bM : Algebra M := ⟨b.val,S.twoRatioMatrix_le k b.property⟩
  have hbM : ‖(a-bM).val Ω‖ < ε*c/(2*(1+c)) := by
    change dist (a.val Ω) (b.val Ω) < _ at hb
    simpa only [bM,AddSubgroupClass.coe_sub,sub_apply,dist_eq_norm] using hb
  filter_upwards [hcr,eventually_ge_atTop k] with n hcn hn
  have hcomm : Commute bM (star (w n)) := by
    apply Subtype.ext
    have hh := S.remoteCopy_commutes_stage n (star (v n)) b.val
      (S.twoRatioMatrix_increasing hn b.property)
    rw [map_star] at hh
    exact hh.eq
  have hest := (hwscale n).coisometry_adjoint_commutator_bound d hc hc1 hcn
    (w n) (hw n) a bM hcomm
  have he : ‖(a*star (w n)-star (w n)*a).val Ω‖ < ε := by
    have hm := (lt_div_iff₀ hden).mp hbM
    nlinarith
  simpa only [dist_zero_right] using he

theorem remoteCopy_conjugation_tendsto (d : ModularConjugationData M Ω)
    (r : ℕ → ℝ) (v : ℕ → Algebra M) (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (r n) (v n).val)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcr : ∀ᶠ n in atTop, c ≤ r n)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (S.remoteCopy n (v n)*a*star (S.remoteCopy n (v n))).val η)
      atTop (𝓝 (a.val η)) := by
  let w (n : ℕ) := S.remoteCopy n (v n)
  have hw (n : ℕ) : w n*star (w n)=1 := by
    change S.remoteCopy n (v n)*star (S.remoteCopy n (v n))=1
    rw [← map_star,← map_mul,hv,map_one]
  have ht := S.remoteCopy_adjoint_commutator_tendsto d r v hv hs hc hc1 hcr a η
  have hn (n : ℕ) : ‖(w n*a*star (w n)-a).val η‖ ≤
      ‖(a*star (w n)-star (w n)*a).val η‖ :=
    coisometry_conjugation_error_le (w n) a (hw n) η
  have hz := squeeze_zero (fun n => norm_nonneg ((w n*a*star (w n)-a).val η)) hn
    (by simpa only [norm_zero] using ht.norm)
  have htzero := tendsto_zero_iff_norm_tendsto_zero.mpr hz
  have hout := htzero.add_const (a.val η)
  simpa only [AddSubgroupClass.coe_sub,sub_apply,sub_add_cancel,zero_add] using hout

end PointedMatrixSites

end

end KadisonKastler

end OAI
