import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerToTracial

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

lemma positive_contraction_square_le {D : Type*} [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] {x : D} (hx : 0≤x) (hx1 : x≤1) : x*x≤x := by
  have he : CFC.sqrt x*CFC.sqrt x=x := CFC.sqrt_mul_sqrt_self x hx
  calc
    x*x = CFC.sqrt x*x*CFC.sqrt x := by
      have hh : (CFC.sqrt x*CFC.sqrt x)*(CFC.sqrt x*CFC.sqrt x)=
          CFC.sqrt x*(CFC.sqrt x*CFC.sqrt x)*CFC.sqrt x := by noncomm_ring
      simpa only [he] using hh
    _ ≤ CFC.sqrt x*1*CFC.sqrt x := conjugate_le_conjugate_of_nonneg hx1 (CFC.sqrt_nonneg _)
    _ = x := by simpa only [mul_one] using he

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "Λ" => familyLimitTrace T U

theorem tracial_annihilator_zero (z : FamilyUltrapower T U)
    (hzb : ∀ b : A, z*quotientInclusion U b=0) : z=0 := by
  have hz : familyTwoNorm Λ z≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let r : ℝ := ε/(‖z‖+1)
    have hr : 0<r := div_pos hε (by positivity)
    obtain ⟨b,hbp,hbn,hbt⟩ := uniform_trace_approximate_unit (A := A) (r^2) (sq_pos_of_pos hr)
    let B : Unitization ℂ A := Unitization.inr b
    have hBp : 0≤B := map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) hbp
    have hB1 : B≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg B hBp).mp (by
      simpa only [B,Unitization.norm_inr] using hbn.le)
    have hxp : 0≤1-B := sub_nonneg.mpr hB1
    have hx1 : 1-B≤1 := sub_le_self _ hBp
    have hnorm : familyTwoNorm T (1-B)≤r := by
      apply ciSup_le
      intro τ
      have hm := (τ.unitized.functional.monotone (positive_contraction_square_le hxp hx1)).1
      have hs := traceTwoNorm_sq τ.unitized (1-B)
      rw [hxp.isSelfAdjoint.star_eq] at hs
      change (τ.unitized.functional ((1-B)*(1-B))).re≤(τ.unitized.functional (1-B)).re at hm
      simp only [B,map_sub,τ.unitized.normalized,NormalizedTrace.unitized_inr,Complex.sub_re,Complex.one_re] at hm
      have hb := hbt τ
      change 1-r^2<(τ.functional b).re at hb
      change _≤1-(τ.functional b).re at hm
      nlinarith [traceTwoNorm_nonneg τ.unitized (1-B)]
    have hqnorm : familyTwoNorm Λ (1-quotientInclusion U b)≤r := by
      rw [quotientInclusion_apply,←map_one (familyUltrapowerMap T U),←map_sub,
        familyTwoNorm_ultrapowerMap]
      exact hnorm
    have heq : z=z*(1-quotientInclusion U b) := by simp only [mul_sub,mul_one,hzb,sub_zero]
    calc
      familyTwoNorm Λ z = familyTwoNorm Λ (z*(1-quotientInclusion U b)) := congrArg _ heq
      _ ≤ ‖z‖*familyTwoNorm Λ (1-quotientInclusion U b) := familyTwoNorm_mul_left Λ _ _
      _ ≤ ‖z‖*r := mul_le_mul_of_nonneg_left hqnorm (norm_nonneg _)
      _ ≤ 0+ε := by
        have he : (‖z‖+1)*r=ε := by dsimp [r]; field_simp
        nlinarith
  apply limitTrace_detects_zero T U z
  intro s
  exact le_antisymm ((traceTwoNorm_le_family Λ s z).trans hz) (traceTwoNorm_nonneg _ _)

theorem norm_annihilator_in_trace_kernel (y : N)
    (hy : ∀ a : A, y*normInclusion U a=0) : normToTracial U y=0 := by
  apply tracial_annihilator_zero U
  intro b
  simpa only [map_mul,normToTracial_inclusion,map_zero] using congrArg (normToTracial U) (hy b)

end NonunitalGamma

end
end

end OAI
