import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_normalised_physical_kernel_horizon (P L H : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) H, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C := by
  let K : Set (ℝ × Vec × Vec × Vec × Vec) :=
    Icc 0 H ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P ×ˢ
      closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  let r : (ℝ × Vec × Vec × Vec × Vec) → ℝ := Prod.fst
  let n : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.1
  let v : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.1
  let E : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.1
  let B : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.2
  have hr : Continuous r := continuous_fst
  have hn : Continuous n := continuous_snd.fst
  have hv : Continuous v := continuous_snd.snd.fst
  have hE : Continuous E := continuous_snd.snd.snd.fst
  have hB : Continuous B := continuous_snd.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha : Continuous (fun p => fderiv ℝ velocity (v p) (E p+cross (velocity (v p)) (B p))) :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp hv).clm_apply
      (hE.add ((contDiff_cross (k:=1)).continuous.comp (hu.prodMk hB)))
  have hd : Continuous (fun p => 1-dot (n p) (velocity (v p))) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hk := hd.continuousOn.smul (continuousOn_normalisedElectricKernel
    hr.continuousOn hn.continuousOn hu.continuousOn ha.continuousOn (S:=K) (by
      intro p hp
      exact (cone_denom_pos (v p) (n p) (by simpa only [n,mem_sphere,dist_zero_right] using hp.2.1)).ne'))
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hk).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r hr n hn v hv E B hE hB
  apply le_trans (hC _ ⟨(r,n,v,E,B),?_,rfl⟩) (le_max_right _ _)
  exact ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv,
    by simpa only [mem_closedBall_zero_iff] using hE,
    by simpa only [mem_closedBall_zero_iff] using hB⟩

lemma normalisedElectricKernel_affine_acceleration (r : ℝ) (n u b : Vec) (a : ℝ) :
    normalisedElectricKernel r n u (a • b)=
      (1-a) • normalisedElectricKernel r n u 0 + a • normalisedElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,dot_smul_right,dot_zero_right_rvm,zero_smul,
    smul_zero,sub_zero,add_zero,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  ring

lemma uniform_normalised_physical_kernel_affine (P H : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) H, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec,
      ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C*(1+‖E‖+‖B‖) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_physical_kernel_horizon P 1 H
  refine ⟨2*C,by positivity,?_⟩
  intro r hr n hn v hv E B
  let L : ℝ := 1+‖E‖+‖B‖
  have hL : 1≤L := by dsimp [L]; linarith [norm_nonneg E,norm_nonneg B]
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hE : ‖L⁻¹ • E‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL0)]
    exact (inv_mul_le_one₀ hL0).mpr (by dsimp [L]; linarith [norm_nonneg E,norm_nonneg B])
  have hB : ‖L⁻¹ • B‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL0)]
    exact (inv_mul_le_one₀ hL0).mpr (by dsimp [L]; linarith [norm_nonneg E,norm_nonneg B])
  have hsmall := hb r hr n hn v hv (L⁻¹ • E) (L⁻¹ • B) hE hB
  have hzero := hb r hr n hn v hv 0 0 (by simp) (by simp)
  let b := fderiv ℝ velocity v (L⁻¹ • E+cross (velocity v) (L⁻¹ • B))
  have hacc : fderiv ℝ velocity v (E+cross (velocity v) B)=L • b := by
    dsimp [b]
    rw [← map_smul,smul_add,cross_smul_right,smul_smul,smul_smul,
      mul_inv_cancel₀ hL0.ne',one_smul,one_smul]
  rw [hacc,normalisedElectricKernel_affine_acceleration,smul_add,
    smul_comm (1-dot n (velocity v)) (1-L),smul_comm (1-dot n (velocity v)) L]
  have hz : ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v) 0‖≤C := by
    have hc0 : cross (velocity v) 0=0 := (crossCLM (velocity v)).map_zero
    simpa only [hc0,add_zero,map_zero] using hzero
  calc
    _ ≤ ‖(1-L) • ((1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v) 0)‖ +
      ‖L • ((1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v) b)‖ := norm_add_le _ _
    _ = (L-1)*‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v) 0‖ +
      L*‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v) b‖ := by
        simp only [norm_smul,Real.norm_eq_abs,
          abs_of_nonpos (by linarith : 1-L≤0),abs_of_pos hL0]; ring
    _ ≤ (L-1)*C+L*C := add_le_add (mul_le_mul_of_nonneg_left hz (by linarith))
      (mul_le_mul_of_nonneg_left hsmall hL0.le)
    _ ≤ (2*C)*(1+‖E‖+‖B‖) := by change _≤(2*C)*L; nlinarith

end RVM
end

end OAI
