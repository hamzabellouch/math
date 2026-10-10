import OAI.Geometry.Convex.GeneralMahler.LogDet
import OAI.Geometry.Convex.GeneralMahler.Edge

namespace OAI
/-! Path z↦c(z)I+∫_{-∞}^z WP, for fixed standard input. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace Edge
variable (e:Edge m) (x:Rn m)
def H (z:ℝ) := ∫ y in Iic z,e.WP y x
lemma H_diff (z w:ℝ) :
    e.H x w-e.H x z= ∫ t in z..w,e.WP t x := by
  unfold H
  exact (intervalIntegral.integral_Iic_sub_Iic (a:=z) (b:=w)
    (e.wp_slice_i x).integrableOn (e.wp_slice_i x).integrableOn)
lemma H_nonneg (z:ℝ) : 0 ≤ e.H x z :=
  (psd_integral (e.wp_slice_i x).integrableOn (ae_of_all _ fun y=>(e.wp_psd y x).posSemidef)).nonneg
lemma H_lip : LipschitzWith 1 (e.H x) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm,dist_eq_norm,e.H_diff]
  have hi (t:ℝ) : ‖e.WP t x‖ ≤ 1 := by
    rw [WP,norm_smul,Real.norm_of_nonneg (mw_pos t).le]
    exact (mul_le_mul_of_nonneg_right (mw_le t) (norm_nonneg _)).trans
      (by simpa only [one_mul] using e.Pcont t x)
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _=>hi t)
lemma H_deriv :
    ∀ᵐ z:ℝ, HasDerivAt (e.H x) (e.WP z x) z := by
  have h := LocallyIntegrable.ae_hasDerivAt_integral (e.wp_slice_i x).locallyIntegrable
  filter_upwards [h] with z hz
  have he : e.H x= fun t=> e.H x 0+∫ y in (0:ℝ)..t,e.WP y x := by
    funext t; rw [← e.H_diff]; abel
  rw [he]; exact (hz 0).const_add _

def path (z:ℝ) := scalar m (MillsC z)+e.H x z
lemma path_pd (z) : (e.path x z).PosDef :=
  (form_posDef (mc_pos z) (show scalar m (MillsC z)∈specBox m (MillsC z) (MillsC z) from
    ⟨scalar_sym ..,le_rfl,le_rfl⟩)).add_posSemidef (e.H_nonneg x z).posSemidef
lemma path_d :
    ∀ᵐ z:ℝ, HasDerivAt (e.path x) ((-MillsW z) • (1-e.P z x)) z := by
  filter_upwards [e.H_deriv x] with z hz
  have h : HasDerivAt (fun t=> scalar m (MillsC t)) ((-MillsW z)•1) z :=
    (d_mc z).smul_const _
  have hh := h.add hz
  simp only [smul_sub,neg_smul,sub_neg_eq_add] at hh ⊢
  exact hh
lemma path_lip : LipschitzWith 2 (e.path x) := by
  have h : LipschitzWith 1 (fun z=>scalar m (MillsC z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp_rw [scalar,dist_eq_norm,← sub_smul,norm_smul]
    have he := mc_lip.dist_le_mul z w
    simpa [dist_eq_norm] using he
  convert h.add (e.H_lip x) using 1 <;> first | rfl | norm_num

def Fedge (z:ℝ) := logD (e.path x z)
lemma F_AC (a b:ℝ) : AbsolutelyContinuousOnInterval (e.Fedge x) a b := by
  let f := e.path x
  have hi := e.path_lip x
  have hf : Continuous f := hi.continuous
  let S := f '' (uIcc a b)
  have hc : IsCompact S := isCompact_uIcc.image hf
  have hl : LocallyLipschitzOn S logD := by
    rintro q ⟨t,ht,rfl⟩
    have h : ContDiffAt ℝ 1 logD (f t) :=
      (D_log (e.path_pd x t)).of_le le_top
    obtain ⟨K,s,hs,hK⟩ := h.exists_lipschitzOnWith
    exact ⟨K,s,mem_nhdsWithin_of_mem_nhds hs,hK⟩
  obtain ⟨K,hK⟩ := hl.exists_lipschitzOnWith_of_compact hc
  exact (hK.comp hi.lipschitzOnWith
    (show MapsTo f (uIcc a b) S from mapsTo_image _ _)).absolutelyContinuousOnInterval

def Sh (z:ℝ) := (MillsC z)⁻¹ • e.H x z
def beta (z:ℝ) := MillsJ z * trN (thresh (e.Sh x z)*(1-e.P z x))
def h1 (z:ℝ) := trN (e.P z x)
lemma Sh_nonneg (z:ℝ) : 0 ≤ e.Sh x z :=
  smul_nonneg (inv_pos.mpr (mc_pos _)).le (e.H_nonneg _ _)
lemma beta_bound (z:ℝ) : 0 ≤ e.beta x z ∧ e.beta x z ≤ MillsJ z := by
  have h := thresh_unit (e.Sh_nonneg x z)
  have hi := trN_prod_unit h.1 h.2 (sub_nonneg.mpr (e.le_one z x))
    (sub_le_self _ (e.psd z x))
  exact ⟨mul_nonneg (mj_pos z).le hi.1, mul_le_of_le_one_right (mj_pos z).le hi.2⟩

lemma Fedge_d :
    ∀ᵐ z:ℝ, HasDerivAt (e.Fedge x)
      (-MillsJ z*(1-e.h1 x z)+e.beta x z) z := by
  filter_upwards [e.path_d x] with z hz
  have hp := e.path_pd x z
  have hd := deriv_logD hz hp
  set c := MillsC z
  set B := 1+e.Sh x z
  have hc : 0<c := mc_pos z
  have hb : e.path x z=c•B := by
    simp only [path,B,Sh,smul_add,smul_smul]; change c•1+_ = c•1+ (c*c⁻¹)•_
    rw [mul_inv_cancel₀ hc.ne',one_smul]
  have he : (e.path x z)⁻¹=c⁻¹ • B⁻¹ := by
    have hpd : B.PosDef := thresh_pd (e.Sh_nonneg x z)
    apply left_inv_eq_left_inv (inv_mul' hp)
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul, inv_mul_cancel₀ hc.ne',inv_mul' hpd,one_smul]
  rw [he, smul_mul_assoc,mul_smul_comm,smul_smul,trN_smul] at hd
  have he' : c⁻¹ * -MillsW z = -MillsJ z := by change c⁻¹ * -(MillsJ z*c)=_; field_simp
  rw [he'] at hd
  suffices H : -MillsJ z*(1-e.h1 x z)+e.beta x z =
      -MillsJ z*trN (B⁻¹*(1-e.P z x)) by rw [H]; exact hd
  unfold beta thresh h1
  rw [sub_mul,one_mul,trN_sub,trN_sub,trN_one]
  unfold B; ring

-- Endpoint saturation from cutoff
lemma path_neg {z:ℝ} (h : z < -e.radius x) :
    e.H x z=0 ∧ e.Fedge x z=LC z ∧ e.beta x z=0 ∧ e.h1 x z=0 := by
  have he (y:ℝ) (hy : y≤z) : e.P y x=0 :=
    e.tend_neg y x (show e.radius x < -y by linarith)
  have hh : e.H x z=0 := by
    calc
      _ = ∫ y in Iic z,(0:Mat m) :=
        setIntegral_congr_fun measurableSet_Iic fun y hy=> by simp only [WP,he y hy,smul_zero]
      _ = 0 := integral_zero ..
  refine ⟨hh, ?_, ?_, ?_⟩
  · unfold Fedge path LC; rw [hh,add_zero,logD_scalar]
  · unfold beta Sh thresh; simp [hh,trN]
  unfold h1; rw [he z le_rfl]; simp [trN]

lemma path_pos {z:ℝ} (h : e.radius x < z) :
    e.Fedge x z=logD (e.Jedge x) ∧ e.beta x z=0 ∧ e.h1 x z=1 := by
  have he (y:ℝ) (hy:z≤y) := e.tend_pos y x (h.trans_le hy)
  have hh := integral_add_compl measurableSet_Iic (e.wp_slice_i x) (s:=Iic z)
  rw [compl_Iic] at hh
  have hi : (∫ y in Ioi z,e.WP y x)=scalar m (MillsC z) := by
    rw [← (mw_tail z).2,scalar, ← integral_smul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy=>by rw [WP,he y (mem_Ioi.mp hy).le]
  change e.H x z+ _ = e.Jedge x at hh
  rw [hi,add_comm] at hh
  exact ⟨congrArg logD hh, by unfold beta; simp [he z le_rfl,trN],
    by unfold h1; rw [he z le_rfl,trN_one]⟩

end Edge
end GeneralMahler

end

end OAI
