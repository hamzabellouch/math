import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellAssignedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeProgression PrimeCellReplacement PrimeCellFreezing Characters.RationalHistory

theorem exists_grid_smooth_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (M : ℕ) [NeZero M]
        (lo hi η Z : ι → ℝ),
        (∀ i, L₀ ≤ lo i ∧ lo i ≤ hi i ∧ 0 < η i ∧ η i ≤ 1 ∧
          ⌊Real.exp (hi i)⌋₊ ≤ N i ∧ 0 < Z i ∧
          (M:ℝ) ≤ Real.exp (d*(lo i)^(1/3:ℝ))) →
        ∀ ε B : ℝ, 0 ≤ ε → 1 ≤ B →
          (∀ (j : GridBoxIndex lo hi η) i,
            (K/Z i)*Real.exp (-d*(boxLower lo hi η j i)^(1/3:ℝ))+
              (Z i*Real.exp (boxLower lo hi η j i))⁻¹ ≤ ε) →
          (∀ (j : GridBoxIndex lo hi η) i,
            |harmonicIntegral M (boxLower lo hi η j i) (boxUpper lo hi η j i)/Z i|+
              ((K/Z i)*Real.exp (-d*(boxLower lo hi η j i)^(1/3:ℝ))+
                (Z i*Real.exp (boxLower lo hi η j i))⁻¹) ≤ B) →
        ∀ (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) (D mesh A : ℝ),
          0 ≤ D → 0 ≤ mesh → (∀ i, η i ≤ mesh) →
          (∀ z∈logRectangle lo hi,DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z) →
          (∀ z∈logRectangle lo hi,∀ i,
            ‖deriv (fun t => f (Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D) →
          (∀ z∈logRectangle lo hi, ‖f (fun i => Real.exp (z i))‖ ≤ A) →
          ‖smoothJointTestSum N M lo hi Z F f-principalIntegral M lo hi Z f*
            ∑ u : ι → (ZMod M)ˣ,F u‖ ≤
            (2*((Fintype.card ι:ℝ)*D*mesh)*principalMass M lo hi Z+
              ((Fintype.card ι:ℝ)*D*mesh+A)*
                (Fintype.card (GridBoxIndex lo hi η)*(Fintype.card ι*ε*B^Fintype.card ι)))*
              ∑ u : ι → (ZMod M)ˣ,‖F u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_assigned_joint_primeCell_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro ι _ _ N M _ lo hi η Z hcell ε B hε hB hE hbound F f D mesh A hD hm hmesh hf hderiv hA
  classical
  have horder : ∀ i, lo i ≤ hi i := fun i => (hcell i).2.1
  have hlo : ∀ i, 0 < lo i := fun i => lt_of_lt_of_le (by linarith) (hcell i).1
  have hη : ∀ i, 0 < η i := fun i => (hcell i).2.2.1
  have hZ : ∀ i, 0 < Z i := fun i => (hcell i).2.2.2.2.2.1
  let v : ℝ := (Fintype.card ι:ℝ)*D*mesh
  let E : ℝ := Fintype.card ι*ε*B^Fintype.card ι
  let T : ℝ := ∑ u : ι → (ZMod M)ˣ,‖F u‖
  let mass : GridBoxIndex lo hi η → ℝ :=
    fun j => principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlocal (j : GridBoxIndex lo hi η) :
      ‖smoothAssignedJointTestSum N M lo hi η Z j F f-
        principalIntegral M (boxLower lo hi η j) (boxUpper lo hi η j) Z f*
          ∑ u : ι → (ZMod M)ˣ,F u‖ ≤ (v*(2*mass j+E)+A*E)*T := by
    have hbase : boxLower lo hi η j∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j) :=
      fun i _ => ⟨le_rfl,box_order lo hi η horder j i⟩
    have hb := assigned_smooth_replacement_of_errors (error := E) N lo hi η Z hZ hlo horder j F f hD hm
      (fun i => (box_width_le lo hi η horder hη j i).trans (hmesh i))
      (fun z hz => hf z (closedBox_subset lo hi η horder j hz))
      (fun z hz => hderiv z (closedBox_subset lo hi η horder j hz)) hbase
    have he := hAP ι N M lo hi η Z hcell j ε B hε hB (hE j) (hbound j) F
    have heAbs := hAP ι N M lo hi η Z hcell j ε B hε hB (hE j) (hbound j)
      (fun u => (‖F u‖:ℂ))
    have he' : ‖assignedJointComplexTestSum N M lo hi η Z j F-
        (mass j:ℂ)*∑ u : ι → (ZMod M)ˣ,F u‖ ≤ E*T := by
      simpa only [mass,principalMass,boxLower,boxUpper,Complex.ofReal_prod,E,T] using he
    have heAbs' : ‖assignedJointComplexTestSum N M lo hi η Z j (fun u => (‖F u‖:ℂ))-
        (mass j:ℂ)*∑ u : ι → (ZMod M)ˣ,(‖F u‖:ℂ)‖ ≤ E*T := by
      simpa only [mass,principalMass,boxLower,boxUpper,Complex.ofReal_prod,E,T,
        Complex.norm_real,Real.norm_eq_abs,abs_norm] using heAbs
    exact (hb he' heAbs').trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (hA _ (closedBox_subset lo hi η horder j hbase)) hE0)) hT0)
  have hsum : (∑ j : GridBoxIndex lo hi η,(v*(2*mass j+E)+A*E)) =
      2*v*principalMass M lo hi Z+(v+A)*(Fintype.card (GridBoxIndex lo hi η)*E) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp only [← mul_assoc,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (∑ j : GridBoxIndex lo hi η,mass j)=principalMass M lo hi Z from
      (principalMass_eq_sum_boxes M lo hi η Z horder hlo).symm]
    ring
  rw [smoothJointTestSum_eq_sum_assigned N lo hi η Z horder F f,
    principalIntegral_eq_sum_boxes M lo hi η Z horder hlo f
      (fun z hz => (hf z hz).continuousAt.continuousWithinAt),Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : GridBoxIndex lo hi η,
        ‖smoothAssignedJointTestSum N M lo hi η Z j F f-
          principalIntegral M (boxLower lo hi η j) (boxUpper lo hi η j) Z f*
            ∑ u : ι → (ZMod M)ˣ,F u‖ := norm_sum_le _ _
    _ ≤ ∑ j : GridBoxIndex lo hi η,(v*(2*mass j+E)+A*E)*T :=
      Finset.sum_le_sum fun j _ => hlocal j
    _ = _ := by rw [← Finset.sum_mul,hsum]

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
