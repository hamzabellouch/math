import OAI.Analysis.LipschitzHilbert.Fourier.SignedAnnularSymbol
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSymbolBound
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteCommutatorSquare

namespace OAI

/-! The signed symbols are exactly the corresponding sums of the actual
vertical L2 projections, with an operator norm independent of the scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_neg (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (-f : SchwartzMap (ℝ×ℝ) ℂ) omega= -planarFourier f omega := by
  simpa only [neg_one_smul,neg_one_mul] using planarFourier_smul f (-1) omega

def signedAnnularOperator (N : ℕ) (s : ℕ → Bool) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  ∑ n∈Finset.range (2*N+1), if s n then
    verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n)
  else -verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n)

def signedAnnularImage (N : ℕ) (s : ℕ → Bool) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  ∑ n∈Finset.range (2*N+1), if s n then
    schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f
  else -schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f

theorem signedAnnularOperator_onSchwartz (N : ℕ) (s : ℕ → Bool)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    signedAnnularOperator N s (f.toLp 2 planeMeasure)=
      (signedAnnularImage N s f).toLp 2 planeMeasure := by
  unfold signedAnnularOperator signedAnnularImage
  simp only [sum_apply]
  change _=(SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure)
    (∑ n∈Finset.range (2*N+1), if s n then
      schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f
    else -schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs
  · exact verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos N n) f
  · simp only [neg_apply,map_neg]
    exact congrArg Neg.neg (verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos N n) f)

theorem signedAnnularImage_fourier (N : ℕ) (s : ℕ → Bool)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (signedAnnularImage N s f) omega=
      signedAnnularSymbol N s omega.2*planarFourier f omega := by
  unfold signedAnnularImage signedAnnularSymbol
  rw [planarFourier_schwartz_sum]
  simp only [sum_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs
  · simp only [schwartzVerticalProjection_fourier,sub_zero,dilatedSlopeWindow_apply]
  · simp only [planarFourier_neg,schwartzVerticalProjection_fourier,sub_zero,
      neg_apply,dilatedSlopeWindow_apply,neg_mul]

theorem signedAnnularOperator_eq_multiplier (N : ℕ) (s : ℕ → Bool) :
    signedAnnularOperator N s=verticalL2Projection (signedAnnularSymbol N s) 1 := by
  have he := l2_maps_eq_onSchwartz ((signedAnnularOperator N s).restrictScalars ℝ)
    ((verticalL2Projection (signedAnnularSymbol N s) 1).restrictScalars ℝ) (fun f => by
      change signedAnnularOperator N s (f.toLp 2 planeMeasure)=
        verticalL2Projection (signedAnnularSymbol N s) 1 (f.toLp 2 planeMeasure)
      rw [signedAnnularOperator_onSchwartz,verticalL2Projection_onSchwartz _ _ (by norm_num)]
      congr 1
      apply planar_schwartz_ext_fourier
      intro omega
      rw [signedAnnularImage_fourier,schwartzVerticalProjection_fourier]
      simp only [sub_zero,one_mul])
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T f) he

theorem signedAnnularOperator_norm (N : ℕ) (s : ℕ → Bool) :
    ‖signedAnnularOperator N s‖≤signedAnnularMihlinConstant := by
  rw [signedAnnularOperator_eq_multiplier]
  exact verticalL2Projection_symbol_norm _ 1 _ (by norm_num)
    signedAnnularMihlinConstant_nonneg (signedAnnularSymbol_norm N s)

end LipschitzHilbert.PacketRepresentation

end

end OAI
