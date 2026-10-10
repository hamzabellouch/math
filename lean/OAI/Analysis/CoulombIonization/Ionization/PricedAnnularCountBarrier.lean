import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCellGeometryBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation CoulombBarrier

 theorem exists_priced_annular_count_constant {alpha beta : ℝ} (ha : 0 < alpha) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D u : ℝ), 0 ≤ D → 0 < u →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      rawAnnularMoment psi (alpha*u) (beta*u) ≤ C*(annularOffsetMass D u)^2 := by
  classical
  obtain ⟨T,hT,hcover⟩ := exists_annularCellStencil ha beta
  let K := annularCellScaleConstant alpha beta
  let C := max (((T.card:ℝ)^2)*universalCellCountConstant*K^2) 1
  refine ⟨C,le_max_right _ _,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D u hD hu he
  let U := T.image (fun v => u • v)
  let m := annularOffsetMass D u
  have hm0 : 0 ≤ m := le_trans zero_le_one (annularOffsetMass_one_le D u)
  have hc := rawAnnularMoment_le_cover hpsi.sobolevVector (alpha*u) (beta*u) U localCellRadius
    (fun _ h1 h2 => annularCell_scaled_cover hu T hcover h1 h2)
  have hc0 : 0 ≤ universalCellCountConstant := le_trans zero_le_one universalCellCountConstant_one_le
  have hm' (v : Space) (hv : v ∈ U) :
      rawCountMoment psi v (localCellRadius v) ≤ universalCellCountConstant*K^2*m^2 := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hw0 : w ≠ 0 := norm_pos_iff.mp (ha.trans_le (hT w hw).1)
    have hv0 : u • w ≠ 0 := smul_ne_zero hu.ne' hw0
    have hscale := localOffsetMass_annular_bound ha hu hD (hT w hw).1 (hT w hw).2
    have hh := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le D (u • w))) hscale 2
    calc _ ≤ universalCellCountConstant*(localOffsetMass D (u • w))^2 :=
              (priced_local_cell_count hpsi hm hZ hlam hv0).trans
                (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le _ _))
                    (localOffsetMass_mono he _) 2) hc0)
         _ ≤ universalCellCountConstant*(K*m)^2 := mul_le_mul_of_nonneg_left hh hc0
         _ = _ := by ring
  have hcard : (U.card:ℝ) ≤ (T.card:ℝ) := by exact_mod_cast Finset.card_image_le
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg U.card) hcard 2
  calc
    _ ≤ (U.card:ℝ)*∑ v ∈ U, rawCountMoment psi v (localCellRadius v) := hc
    _ ≤ (U.card:ℝ)*∑ _v ∈ U, universalCellCountConstant*K^2*m^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hm') (Nat.cast_nonneg U.card)
    _ = (U.card:ℝ)^2*universalCellCountConstant*K^2*m^2 := by simp; ring
    _ ≤ (T.card:ℝ)^2*universalCellCountConstant*K^2*m^2 := by gcongr
    _ ≤ C*m^2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg m)

end CoulombAtom

end

end OAI
