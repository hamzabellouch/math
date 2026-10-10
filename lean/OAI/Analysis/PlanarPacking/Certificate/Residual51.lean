import OAI.Analysis.PlanarPacking.ResidualBase
import OAI.Analysis.PlanarPacking.Certificate.TableMoments51

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Residual51
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def node : Node := ⟨51,by norm_num [residues]⟩
noncomputable def box0_0 : RBox := (RBox.rat (-10361) 10000000000).add ((tm1_51_0.realAnswer).mul (qiBox 51))
lemma contains0_0 : box0_0.Contains (tableResidual false (node,false)) := by
  rw [tableResidual_value]
  have hv := RBox.contains_rat (-10361) 10000000000 (by norm_num)
  have hq := qiBox_contains 51 (by norm_num [residues])
  have hh := RBox.contains_add hv (RBox.contains_mul tm1_51_0.KContains hq)
  convert hh using 1 <;> norm_num [box0_0,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg]
lemma bound0_0 : |tableResidual false (node,false)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_0 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
noncomputable def box0_1 : RBox := (RBox.rat (29035) 10000000000).add ((tm1_51_1.realAnswer.add (((dBox 51).mul tm1_51_0.realAnswer).neg)).mul (qiBox 51))
lemma contains0_1 : box0_1.Contains (tableResidual false (node,true)) := by
  rw [tableResidual_deriv]
  have hv := RBox.contains_rat (29035) 10000000000 (by norm_num)
  have hq := qiBox_contains 51 (by norm_num [residues])
  have hd := dBox_contains 51 (by norm_num [residues])
  have hh := RBox.contains_add hv (RBox.contains_mul (RBox.contains_add tm1_51_1.KContains (RBox.neg_contains (RBox.contains_mul hd tm1_51_0.KContains))) hq)
  convert hh using 1 <;> norm_num [box0_1,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg]
lemma bound0_1 : |tableResidual false (node,true)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_1 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
noncomputable def box1_0 : RBox := (RBox.rat (9641) 10000000000).add ((tm0_51_0.realAnswer).mul (qiBox 51))
lemma contains1_0 : box1_0.Contains (tableResidual true (node,false)) := by
  rw [tableResidual_value]
  have hv := RBox.contains_rat (9641) 10000000000 (by norm_num)
  have hq := qiBox_contains 51 (by norm_num [residues])
  have hh := RBox.contains_add hv (RBox.contains_mul tm0_51_0.KContains hq)
  convert hh using 1 <;> norm_num [box1_0,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg]
lemma bound1_0 : |tableResidual true (node,false)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains1_0 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
noncomputable def box1_1 : RBox := (RBox.rat (-21534) 10000000000).add ((tm0_51_1.realAnswer.add (((dBox 51).mul tm0_51_0.realAnswer).neg)).mul (qiBox 51))
lemma contains1_1 : box1_1.Contains (tableResidual true (node,true)) := by
  rw [tableResidual_deriv]
  have hv := RBox.contains_rat (-21534) 10000000000 (by norm_num)
  have hq := qiBox_contains 51 (by norm_num [residues])
  have hd := dBox_contains 51 (by norm_num [residues])
  have hh := RBox.contains_add hv (RBox.contains_mul (RBox.contains_add tm0_51_1.KContains (RBox.neg_contains (RBox.contains_mul hd tm0_51_0.KContains))) hq)
  convert hh using 1 <;> norm_num [box1_1,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg]
lemma bound1_1 : |tableResidual true (node,true)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains1_1 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
end SharpPlanar.Residual51

end OAI
