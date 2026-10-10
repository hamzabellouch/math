import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionFirm
import OAI.Probability.LatticeSurface.Convexity.ClusterDynamicsDefs

namespace OAI

noncomputable section

namespace ClusterDisplacement

open Set

variable {V I : Type*} [Fintype V] [Fintype I]

lemma energy_difference (u v : V → ℝ) :
    energy (fun x => u x-v x)=energy u+energy v-2*(∑x,u x*v x) := by
  simp only [energy,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx;ring

lemma firm_iff (K : Kernel V) : Firm K ↔ ∀u,energy (K.apply u)≤∑x,u x*K.apply u x := by
  constructor <;> intro h u
  · have hf := h u
    rw [energy_difference] at hf
    linarith
  · rw [energy_difference]
    linarith [h u]

def Kernel.mixture (w : I → ℝ) (hw : ∀i,0≤w i) (hs : (∑i,w i)=1) (K : I → Kernel V) : Kernel V where
  val x y := ∑i,w i*(K i).val x y
  nonneg x y := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) ((K i).nonneg x y)
  row x := by
    calc
      _ = ∑i,w i*(∑y,(K i).val x y) := by rw [Finset.sum_comm];simp only [Finset.mul_sum]
      _ ≤ ∑i,w i := Finset.sum_le_sum fun i _ => by simpa using mul_le_mul_of_nonneg_left ((K i).row x) (hw i)
      _ = 1 := hs
  col y := by
    calc
      _ = ∑i,w i*(∑x,(K i).val x y) := by rw [Finset.sum_comm];simp only [Finset.mul_sum]
      _ ≤ ∑i,w i := Finset.sum_le_sum fun i _ => by simpa using mul_le_mul_of_nonneg_left ((K i).col y) (hw i)
      _ = 1 := hs

lemma Kernel.mixture_apply (w : I → ℝ) (hw : ∀i,0≤w i) (hs : (∑i,w i)=1) (K : I → Kernel V) (u : V → ℝ) (x : V) :
    (Kernel.mixture w hw hs K).apply u x=∑i,w i*(K i).apply u x := by
  simp only [Kernel.apply,Kernel.mixture,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro y hy
  ring

lemma Kernel.mixture_firm (w : I → ℝ) (hw : ∀i,0≤w i) (hs : (∑i,w i)=1) (K : I → Kernel V)
    (hfirm : ∀i,Firm (K i)) : Firm (Kernel.mixture w hw hs K) := by
  rw [firm_iff]
  intro u
  calc
    _ = ∑x,(∑i,w i*(K i).apply u x)^2 := by simp only [energy,Kernel.mixture_apply]
    _ ≤ ∑x,∑i,w i*((K i).apply u x)^2 := Finset.sum_le_sum fun x _ => weighted_sq_le w _ hw hs.le
    _ = ∑i,w i*energy ((K i).apply u) := by rw [Finset.sum_comm];simp only [energy,Finset.mul_sum]
    _ ≤ ∑i,w i*(∑x,u x*(K i).apply u x) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((firm_iff (K i)).mp (hfirm i) u) (hw i)
    _ = _ := by
      simp only [Finset.mul_sum,Kernel.mixture_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro i hi;ring

def Kernel.cutoff (r : V → ℝ) (hr : ∀x,r x∈Icc (0:ℝ) 1) : Kernel V := by
  classical
  exact {val := fun x y => if x=y then r x else 0
         nonneg := fun x y => by split_ifs;exact (hr x).1;norm_num
         row := fun x => by simpa using (hr x).2
         col := fun y => by simpa using (hr y).2}

lemma Kernel.cutoff_apply (r : V → ℝ) (hr : ∀x,r x∈Icc (0:ℝ) 1) (u : V → ℝ) (x : V) :
    (Kernel.cutoff r hr).apply u x=r x*u x := by classical simp [Kernel.cutoff,Kernel.apply]

lemma Kernel.cutoff_firm (r : V → ℝ) (hr : ∀x,r x∈Icc (0:ℝ) 1) : Firm (Kernel.cutoff r hr) := by
  rw [firm_iff]
  intro u
  apply Finset.sum_le_sum
  intro x hx
  simp only [Kernel.cutoff_apply]
  have hp := mul_nonneg (mul_nonneg (hr x).1 (sub_nonneg.mpr (hr x).2)) (sq_nonneg (u x))
  nlinarith

end ClusterDisplacement

namespace ProjectionComparison

open ClusterDisplacement

variable {V E : Type*} [Fintype V]

def averagingKernel (S : System V E) (F : Finset E) : Kernel V where
  val := faceKernel S F
  nonneg := faceKernel_nonneg S F
  row := faceKernel_row S F
  col := faceKernel_column S F

lemma averagingKernel_apply (S : System V E) (F : Finset E) (u : V → ℝ) :
    (averagingKernel S F).apply u=faceAverage S F u := by
  funext x
  exact (faceAverage_eq_sum S F u x).symm

lemma averagingKernel_firm (S : System V E) (F : Finset E) : Firm (averagingKernel S F) := by
  intro u
  rw [averagingKernel_apply]
  exact (faceAverage_energy_identity S F u).le

variable [Fintype E]

theorem projection_update_kernel (S : System V E) (b v₀ v₁ h₀ h₁ : V → ℝ)
    (hp₀ : IsProjection S b v₀ h₀) (hp₁ : IsProjection S b v₁ h₁) :
    ∃ K : Kernel V,Firm K ∧ K.apply (fun y => v₁ y-v₀ y)=(fun x => h₁ x-h₀ x) := by
  obtain ⟨w,hw,hs,heq⟩:=projection_mixture S b v₀ v₁ h₀ h₁ hp₀ hp₁
  refine ⟨Kernel.mixture w hw hs (averagingKernel S),Kernel.mixture_firm w hw hs _ (averagingKernel_firm S),?_⟩
  funext x
  simpa only [Kernel.mixture_apply,averagingKernel_apply] using (heq x).symm

end ProjectionComparison

end

end OAI
