import OAI.MeasureTheory.Falconer.Measures.RegularProductParameters

namespace OAI

/-! Absorb the explicit packing and rounding constants of the actual
width-three product configuration into an arbitrarily small power loss. -/
namespace Falconer

theorem wide_product_parameters {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let x := (N:ℝ)*Real.log 2
      let D := Real.exp (ε*x)
      let R := Real.exp (η*x)
      let W := Real.exp (θ*x)
      1 ≤ D ∧ 1 ≤ R ∧ 4*(361^2*R) ≤ W ∧ 4*(361^2*R)*D ≤ W ∧
        (10:ℝ)^22*R^2*D^4 ≤ W ∧ 884450*D^4 ≤ W ∧
        Real.log 7+ε*x ≤ 4*κ*x ∧ 25*D^2 ≤ Real.exp ((η/2)*x) := by
  obtain ⟨ε,η,N1,hε,hη,hN1,hbase⟩ := regular_product_parameters
    (by positivity : 0 < θ/4) hκ
  obtain ⟨N2,hN2,hlarge⟩ := scalar_fixed_losses hθ
    (by norm_num : (0:ℝ) < 10^22) (by norm_num : (0:ℝ) < 1)
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  let x := (N:ℝ)*Real.log 2
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W0 := Real.exp ((θ/4)*x)
  let W := Real.exp (θ*x)
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hW0 : 0 ≤ W0 := (Real.exp_pos _).le
  obtain ⟨hD,hR,hRc,hRD,hGc,hPc,hlog,h25⟩ := hbase N ((le_max_left _ _).trans hN)
  have hfixed : (10:ℝ)^22*W0 ≤ W := by
    simpa only [W0,W,x,mul_assoc] using (hlarge N ((le_max_right _ _).trans hN)).1
  have hRcost : 4*(361^2*R) ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hRc (by norm_num : (0:ℝ) ≤ 361^2)
    have hh' : (361:ℝ)^2*W0 ≤ (10:ℝ)^22*W0 :=
      mul_le_mul_of_nonneg_right (by norm_num) hW0
    exact (show 4*(361^2*R) ≤ (361:ℝ)^2*W0 by nlinarith only [hh]).trans (hh'.trans hfixed)
  have hRDcost : 4*(361^2*R)*D ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hRD (by norm_num : (0:ℝ) ≤ 361^2)
    have hh' : (361:ℝ)^2*W0 ≤ (10:ℝ)^22*W0 :=
      mul_le_mul_of_nonneg_right (by norm_num) hW0
    exact (show 4*(361^2*R)*D ≤ (361:ℝ)^2*W0 by nlinarith only [hh]).trans (hh'.trans hfixed)
  have hpoly : R^2*D^4 ≤ W0 := by
    have hpos : 0 ≤ R^2*D^4 := mul_nonneg (sq_nonneg _) (pow_nonneg hD0 _)
    have hh : R^2*D^4 ≤ 4*R^2*(16+400*D^4) := by
      nlinarith only [hpos,sq_nonneg R]
    exact hh.trans hGc
  have hGcost : (10:ℝ)^22*R^2*D^4 ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ) ≤ 10^22)
    exact (show (10:ℝ)^22*R^2*D^4 ≤ (10:ℝ)^22*W0 by nlinarith only [hh]).trans hfixed
  have hDpoly : D^4 ≤ W0 := by nlinarith only [hPc,pow_nonneg hD0 4]
  have hPcost : 884450*D^4 ≤ W := by
    calc
      _ ≤ 884450*W0 := mul_le_mul_of_nonneg_left hDpoly (by norm_num)
      _ ≤ (10:ℝ)^22*W0 := mul_le_mul_of_nonneg_right (by norm_num) hW0
      _ ≤ W := hfixed
  exact ⟨hD,hR,hRcost,hRDcost,hGcost,hPcost,hlog,h25⟩

end Falconer

end OAI
