import OAI.Analysis.PlanarPacking.Envelopes
import OAI.Analysis.PlanarPacking.TableNorms
import OAI.Analysis.PlanarPacking.FullMomentBridge

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma table_direct_bound (a : Bool) (ell : ℕ) (s : ℝ) :
    |cardinalSeries (tableData a) ell s| ≤ 80*Real.pi^ell := by
  apply (direct_spectral_bound _ _ _).trans
  have h0:=pow_nonneg Real.pi_pos.le ell
  have hd:=mul_le_mul_of_nonneg_left (direct_envelope_coarse ell)
    (show 0 ≤ |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ by positivity)
  have hm:=table_coeff_mass a
  have hc:=table_constant_bound a
  have hs : (∑ j : Fin 6,densityCap j/6)=(47321:ℝ)/1500 := by
    norm_num [densityCap,densityNum,densityDen,Fin.sum_univ_succ]
  rw [hs] at hd
  nlinarith [mul_le_mul_of_nonneg_right hc h0,mul_le_mul_of_nonneg_right hm.le h0]
lemma table_jet_envelope (a : Bool) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |tableHJet a ell t| ≤ 80*Real.pi^ell+(23:ℝ)/10*transformEnvelope ell s+
      (17:ℝ)/1000*atomicEnvelope ell s := by
  have hk:=sharp_moment_bound (tableData (!a)) ell (hs.trans hst)
  change |K (tableData (!a)) ell t| ≤ 
    (|(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖)*transformEnvelope ell t+
    |(tableData (!a)).C| *atomicEnvelope ell t at hk
  have h1:=mul_le_mul (show |(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖ ≤ (23:ℝ)/10 by linarith [table_coeff_mass (!a)])
    (transformEnvelope_antitone ell hs hst) (transformEnvelope_nonneg ell (hs.trans hst)) (by norm_num : (0:ℝ) ≤ 23/10)
  have h2:=mul_le_mul (table_constant_bound (!a)) (atomicEnvelope_antitone ell hst)
    (atomicEnvelope_nonneg ell t) (by norm_num : (0:ℝ) ≤ 17/1000)
  exact (abs_add_le _ _).trans (by linarith [table_direct_bound a ell t])
end SharpPlanar

end OAI
