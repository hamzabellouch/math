import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLongWindow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfilePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueKernelPairing

namespace OAI

/-! The actual theta kernel can be paired with the incoming forcing in an
arbitrarily high compact annulus. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncomingForcingWeight_low (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaIncomingForcingWeight s v=0 :=
  cubicThetaIncomingForcing_zero_closed s (Or.inl hv)

lemma cubicThetaLongForcingWeight_low_one {H : ℝ} (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaLongForcingWeight H (by linarith) s v=0 :=
  cubicThetaLongForcingWeight_low (by linarith) s (by linarith)

lemma cubicThetaLongForcingWeight_low_two {H : ℝ} (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤2) :
    cubicThetaLongForcingWeight H (by linarith) s v=0 :=
  cubicThetaLongForcingWeight_low (by linarith) s (by linarith)

def cubicThetaLongWindowTest (H : ℝ) (hH : 2≤H) (s : ℂ) : cubicThetaSmoothTests :=
  cubicThetaRadialProfileTest (cubicThetaLongWindowWeight H (by linarith) s)
    (fun _ hv => cubicThetaLongWindowHeight_low (by linarith) s hv)
    (cubicThetaLongWindowHeight_smooth H s)

def cubicThetaLongWindowDefect (H : ℝ) (hH : 2≤H) (s : ℂ) : C_c(ℝ,ℂ) :=
  cubicThetaLongForcingWeight H (by linarith) s-cubicThetaIncomingForcingWeight s

lemma cubicThetaLongWindowDefect_low (H : ℝ) (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaLongWindowDefect H hH s v=0 := by
  change cubicThetaLongForcingWeight H _ s v-cubicThetaIncomingForcingWeight s v=0
  rw [cubicThetaLongForcingWeight_low_one hH s v hv,cubicThetaIncomingForcingWeight_low s v hv,sub_self]

def cubicThetaLongWindowDefectSection (H : ℝ) (hH : 2≤H) (s : ℂ) : CubicThetaSection :=
  cubicThetaRadialProfileSection (cubicThetaLongWindowDefect H hH s)
    (cubicThetaLongWindowDefect_low H hH s)

lemma cubicThetaLongWindowDefectSection_compact (H : ℝ) (hH : 2≤H) (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaLongWindowDefectSection H hH s)) :=
  cubicThetaRadialProfileSection_compact _ _

lemma cubicThetaLongWindowDefectSection_eq (H : ℝ) (hH : 2≤H) (s : ℂ) :
    cubicThetaLongWindowDefectSection H hH s=
      cubicThetaRadialProfileSection (cubicThetaLongForcingWeight H (by linarith) s)
        (cubicThetaLongForcingWeight_low_one hH s)-cubicThetaForcingSection s := by
  exact cubicThetaRadialProfileSection_sub _ _ (cubicThetaLongForcingWeight_low_one hH s)
    (cubicThetaIncomingForcingWeight_low s)

lemma cubicThetaLongWindowDefectL2 (H : ℝ) (hH : 2≤H) (s : ℂ) :
    (cubicThetaCompactSection_memLp (cubicThetaLongWindowDefectSection H hH s)
      (cubicThetaLongWindowDefectSection_compact H hH s)).toLp _=
      cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) s)
        (cubicThetaLongForcingWeight_low_two hH s)-cubicThetaForcingL2 s := by
  let A := cubicThetaRadialProfileSection (cubicThetaLongForcingWeight H (by linarith) s)
    (cubicThetaLongForcingWeight_low_one hH s)
  have hmA := cubicThetaCompactSection_memLp A (cubicThetaRadialProfileSection_compact _ _)
  have hmF := cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)
  calc
    _ = (hmA.sub hmF).toLp _ := by
      apply MemLp.toLp_congr
      filter_upwards with q
      exact congrArg (fun F : CubicThetaSection => cubicThetaSectionRepresentative F q)
        (cubicThetaLongWindowDefectSection_eq H hH s)
    _ = _ := MemLp.toLp_sub hmA hmF

lemma cubicThetaLongWindow_coordinate_equation (H : ℝ) (hH : 2≤H) (s : ℂ)
    (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaLongWindowTest H hH s)) p=
      s*(s-2)*cubicThetaSectionFunction (cubicThetaLongWindowTest H hH s) p-
        cubicThetaSectionFunction (cubicThetaLongWindowDefectSection H hH s) p := by
  apply cubicThetaRadialProfile_coordinate_equation (p:=p) (hp:=hp)
  intro v hv
  have he := cubicThetaLongWindowHeight_equation (show 1≤H by linarith) s hv
  change cubicThetaRadialEuler (cubicThetaLongWindowHeight H s) v=
    s*(s-2)*cubicThetaLongWindowHeight H s v-
      (cubicThetaLongForcingWeight H _ s v-cubicThetaIncomingForcing s v)
  linear_combination he

lemma cubicThetaLongWindow_global_weak (H : ℝ) (hH : 2≤H) (s : ℂ)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalGradient (cubicThetaLongWindowTest H hH s))+
      s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalMass (cubicThetaLongWindowTest H hH s))=
      inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) s)
          (cubicThetaLongForcingWeight_low_two hH s)-cubicThetaForcingL2 s) := by
  have he := cubicThetaSmooth_global_weak (cubicThetaLongWindowTest H hH s)
    (cubicThetaLongWindowDefectSection H hH s) (cubicThetaLongWindowDefectSection_compact H hH s)
    (s*(s-2)) (cubicThetaLongWindow_coordinate_equation H hH s) v
  rwa [cubicThetaLongWindowDefectL2] at he

lemma cubicThetaKernel_long_window_balance (H : ℝ) (hH : 2≤H)
    (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3))=
      inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) (4/3))
          (cubicThetaLongForcingWeight_low_two hH (4/3))) := by
  have hR := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (4/3:ℂ))
    (cubicThetaGlobalEnergyTest (cubicThetaLongWindowTest H hH (4/3))) v
  rw [hv,inner_zero_right,cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_one,map_ofNat,inner_conj_symm,
    cubicThetaGlobalSpectralParameter] at hR'
  norm_num [starRingEnd_apply] at hR'
  have hW := cubicThetaLongWindow_global_weak H hH (4/3) v
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaLongWindowTest H hH (4/3)))+
      (4/3:ℂ)*((4/3:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalMass (cubicThetaLongWindowTest H hH (4/3)))=0 := by
    norm_num at hR' ⊢
    linear_combination -hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

theorem cubicThetaResidue_long_kernel_pairing (H : ℝ) (hH : 2≤H)
    (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=
      (17/6:ℂ)*star (inner ℂ
        (cubicThetaCuspFourierTest 0 (cubicThetaLongForcingWeight H (by linarith) (4/3)))
        (cubicThetaCuspRestriction v)) := by
  rw [cubicThetaResidue_kernel_pairing v hv,cubicThetaKernel_long_window_balance H hH v hv,
    ←inner_conj_symm,cubicThetaRadialProfilePairing_energy]
  norm_num [cubicThetaGlobalSpectralParameter]

end CubicFirstMoment

end

end OAI
