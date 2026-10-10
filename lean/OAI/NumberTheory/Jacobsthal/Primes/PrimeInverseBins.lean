import OAI.NumberTheory.Jacobsthal.Estimates.SourceMarginalRate

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeInverseBins

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel GridWeightComparison DerivativeWeights MarginalProfiles

variable {w ell S : ℝ} {start : Node}

noncomputable def inverseWeight : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => ENNReal.ofReal (1/weight h.node.side h.node.ratio)

noncomputable def inverseBin (w ell S : ℝ) (start : Node) (m n j : ℕ) : ℝ≥0∞ :=
  ∫⁻ z in bin m j,inverseWeight z ∂pathLaw w ell S start n

theorem actual_inverse_bin_local : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,3 ≤ S → ∀ start : Node,
      Valid start.side start.ratio → start.side = .even → start.ratio ≤ S →
      ∀ m n j : ℕ,Valid (sideAfter .even n) (point m j) →
        inverseBin w ell S start m n j ≤
          ENNReal.ofReal (Real.exp (L*(1+S)^3*width m)/weight (sideAfter .even n) (point m j))*
            mass w ell S start m n j := by
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨L,hL,?_⟩
  intro w ell S hS start hs hi hsS m n j hj
  let c := Real.exp (L*(1+S)^3*width m)/weight (sideAfter .even n) (point m j)
  have hpoint : ∀ᵐ z ∂(pathLaw w ell S start n).restrict (bin m j),inverseWeight z ≤ ENNReal.ofReal c := by
    filter_upwards [ae_restrict_of_ae (pathLaw_side hi n),ae_restrict_mem (bin_measurable m j)] with z hz hbin
    cases z with
    | none => exact False.elim hbin
    | some h =>
      have hcell := (mem_bin h m j).mp hbin
      have hgv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have hgS : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
      have hj' : Valid h.node.side (point m j) := by rwa [hz]
      have hlast : h.node.ratio ≤ point m j+width m := by
        rw [point_succ] at hcell
        exact hcell.2.le
      have hr := hlocal S hS h.node.side (point m j) h.node.ratio (width m) hj' hgv hgS hcell.1 hlast
      have hratio : 1/weight h.node.side h.node.ratio ≤
          Real.exp (L*(1+S)^3*width m)/weight h.node.side (point m j) := by
        have heq : 1/weight h.node.side h.node.ratio =
            (weight h.node.side (point m j)/weight h.node.side h.node.ratio)/weight h.node.side (point m j) := by
          field_simp [(weight_pos hj').ne']
        rw [heq]
        exact div_le_div_of_nonneg_right hr (weight_pos hj').le
      change ENNReal.ofReal (1/weight h.node.side h.node.ratio) ≤ _
      apply ENNReal.ofReal_le_ofReal
      simpa only [c,hz] using hratio
  calc
    _ ≤ ∫⁻ _z in bin m j,ENNReal.ofReal c ∂pathLaw w ell S start n := lintegral_mono_ae hpoint
    _ = _ := by rw [setLIntegral_const]; rfl

theorem cancel_inverse_bin {C E F : ℝ} {m n j : ℕ}
    (hE : 0 ≤ E)
    (hj : Valid (sideAfter .even n) (point m j))
    (hlocal : inverseBin w ell S start m n j ≤
      ENNReal.ofReal (E/weight (sideAfter .even n) (point m j))*mass w ell S start m n j)
    (hmass : mass w ell S start m n j ≤
      ENNReal.ofReal (C*width m*weight (sideAfter .even n) (point m j)*F)) :
    inverseBin w ell S start m n j ≤ ENNReal.ofReal (E*C*width m*F) := by
  have hφ := weight_pos hj
  have hw := width_nonneg m
  refine hlocal.trans ((mul_le_mul_of_nonneg_left hmass zero_le).trans ?_)
  rw [← ENNReal.ofReal_mul (div_nonneg hE hφ.le)]
  apply le_of_eq
  congr 1
  field_simp

theorem profile_le_nineteen {m : ℕ} {i : Side} {t : ℝ}
    (hm : width m ≤ 1) (ht : regularLower i ≤ t) : profile m i t ≤ 19 := by
  cases i with
  | even => norm_num [profile]
  | odd =>
    have ht1 : 1 ≤ t := ht
    have hW := W_le_six (by linarith : (1:ℝ)/2 ≤ t)
    have hW0 := (WeightFutureIntegrals.W_pos (by linarith : 0 < t)).le
    have hw := width_nonneg m
    have hh : width m*W t ≤ 6 :=
      (mul_le_mul hm hW hW0 zero_le_one).trans_eq (one_mul 6)
    have hinv : 0 ≤ 1/t^2 := by positivity
    change 1-1/t^2+3*width m*W t ≤ 19
    nlinarith

end NumberTheoryLean.PrimeInverseBins

end

end Erdos970

end OAI
