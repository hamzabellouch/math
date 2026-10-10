import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRowMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFourier

namespace OAI

/-! The actual inverted row Fourier expansion, with absolute integrated
summability proved before interchanging its heat integral and lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaInvertedGaussCoefficient_norm {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    ‖cubicThetaInvertedGaussCoefficient c h‖ ≤ (Nat.card (Residues c):ℝ) := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  unfold cubicThetaInvertedGaussCoefficient
  rw [tsum_fintype,Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues c, ‖cubicSymbol c (3*residueRepresentative c x)*
        (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
          ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues c, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul,Circle.norm_coe,mul_one]
      exact norm_cubicSymbol_le_one hc _
    _ = _ := by simp

def cubicThetaInvertedRowFourierCoefficient (c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaInvertedGaussCoefficient c h*
    (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

lemma cubicThetaInvertedWeightedHeat_summable {v : ℝ} (hv : 0<v) {s : ℂ}
    (hs : 1<s.re) {c : Eisenstein} (hc : primary c) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaInvertedRowFourierCoefficient c z h*
        cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  have ht := (cubicThetaDualHeat_mass_summable hv hs).mul_left (Nat.card (Residues c):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [cubicThetaInvertedRowFourierCoefficient,norm_mul,Circle.norm_coe,mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaInvertedGaussCoefficient_norm hc h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

lemma cubicThetaInvertedRow_heat_poisson {c : Eisenstein} (hc : primary c)
    (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0<t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaInvertedGaussianRow c z t=
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedRowFourierCoefficient c z h*
          cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  rw [cubicThetaInvertedGaussianRow_poisson hc z ht]
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  have he := cubicThetaRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(9*Real.sqrt 3):ℂ)*(cubicThetaInvertedGaussCoefficient c h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))))=_
  calc
    _ = (2/(9*Real.sqrt 3):ℂ)*cubicThetaInvertedRowFourierCoefficient c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))) := by
      unfold cubicThetaInvertedRowFourierCoefficient
      ring
    _ = _ := by rw [he]; ring

theorem cubicThetaInvertedRow_fourier {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaInvertedRowFourierCoefficient c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1<s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaInvertedRowFourierCoefficient c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h=0
    · simp [hh]
    · exact (cubicThetaRowHeatScale_pos hh).le
  have hi := integral_tsum_of_summable_integral_norm hFi
    (cubicThetaInvertedWeightedHeat_summable hp hs1 hc p.1)
  rw [cubicThetaInvertedRow_mellin hc hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein,
          cubicThetaInvertedRowFourierCoefficient c p.1 h*
            cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
      congr 1
      rw [←integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaInvertedRow_heat_poisson hc p.1 p.2 s ht)
    _ = _ := by
      rw [←hi]
      simp only [integral_const_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
