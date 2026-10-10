import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedGaussReduction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryUnitTwist

namespace OAI

/-! Explicit translated-cusp Gauss coefficients. The only new support
condition is the ramified congruence; the unramified factor is the same
primary Fourier coefficient already identified from the actual residue. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaSymbolFourier_congr {c : Eisenstein} (hc : c≠0)
    {h k : Eisenstein} (he : c ∣ h-k) :
    cubicThetaSymbolFourier c hc h=cubicThetaSymbolFourier c hc k := by
  unfold cubicThetaSymbolFourier
  have hm := residue_eq_of_dvd_sub he
  apply tsum_congr
  intro x
  rw [hm]

lemma cubicThetaInvertedGaussCoefficient_shift {c : Eisenstein} (hc : primary c)
    (k h : Eisenstein) (he : c ∣ 3*k-h) :
    cubicThetaInvertedGaussCoefficient c k=
      cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  have hcub := cubicSymbol_cube_of_isCoprime hc lambdaE (primary_coprime_lambda hc)
  have hs : star (cubicSymbol c 3)=cubicSymbol c lambdaE := by
    rw [cubicThetaSymbol_three hc,star_pow,←cubicSymbol_sq_eq_star hc]
    calc
      (cubicSymbol c lambdaE^2)^2=(cubicSymbol c lambdaE)^3*cubicSymbol c lambdaE := by ring
      _ = _ := by rw [hcub,one_mul]
  have hG : cubicThetaSymbolFourier c (primary_ne_zero hc) h=
      cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) k := by
    rw [←cubicThetaSymbolFourier_congr (primary_ne_zero hc) he,
      mul_comm (3:Eisenstein) k,cubicThetaSymbolFourier_mul hc (primary_coprime_three hc),hs]
  rw [cubicThetaInvertedGaussCoefficient_factor hc,cubicThetaSymbol_three hc,hG]
  ring

lemma cubicThetaShiftedGauss_congruence_iff {c : Eisenstein} (hc : primary c)
    (b : ℤ) (h : Eisenstein) :
    (3:Eisenstein) ∣ h-c*lambdaE*(b:Eisenstein) ↔
      (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) := by
  have hd : (3:Eisenstein) ∣ (c-1)*lambdaE*(b:Eisenstein) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
  constructor
  · intro hh
    convert dvd_add hh hd using 1
    ring
  · intro hh
    convert dvd_sub hh hd using 1
    ring

theorem cubicThetaShiftedGaussCoefficient_explicit {c : Eisenstein} (hc : primary c)
    (a b : ℤ) (h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c h=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicSymbol c lambdaE*cubicThetaSymbolFourier c (primary_ne_zero hc) h else 0 := by
  classical
  by_cases ht : (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein)
  · rw [ite_eq_left ht]
    obtain ⟨k,hk⟩ := (cubicThetaShiftedGauss_congruence_iff hc b h).mpr ht
    have he : h=3*k+c*lambdaE*(b:Eisenstein) := by linear_combination hk
    rw [he,cubicThetaShiftedGaussCoefficient_reduce hc]
    rw [cubicThetaInvertedGaussCoefficient_shift hc k (3*k+c*lambdaE*(b:Eisenstein))
      ⟨-lambdaE*(b:Eisenstein),by ring⟩]
    ring
  · rw [ite_eq_right ht]
    by_contra hn
    exact ht ((cubicThetaShiftedGauss_congruence_iff hc b h).mp
      (cubicThetaShiftedGaussCoefficient_congruence hc a b h hn))

def cubicThetaShiftedFrequencyDirichlet (b : Eisenstein) (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : CubicThetaPrimaryPart, cubicThetaShiftedGaussCoefficient b c.val h*(norm c.val:ℂ)^(-s)

theorem cubicThetaShiftedFrequencyDirichlet_eq (a b : ℤ) (h : Eisenstein) (s : ℂ) :
    cubicThetaShiftedFrequencyDirichlet ((a:Eisenstein)+b*omegaE) h s=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicThetaPrimaryFourierSeries 1 2 s h else 0 := by
  classical
  unfold cubicThetaShiftedFrequencyDirichlet
  have he (c : CubicThetaPrimaryPart) :
      cubicThetaShiftedGaussCoefficient ((a:Eisenstein)+b*omegaE) c.val h=
        if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
          9*cubicSymbol c.val lambdaE*cubicThetaSymbolFourier c.val (primary_ne_zero c.property) h else 0 :=
    cubicThetaShiftedGaussCoefficient_explicit c.property a b h
  simp_rw [he]
  split_ifs with ht
  · unfold cubicThetaPrimaryFourierSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro c
    unfold cubicThetaPrimaryFourierTerm
    have hu : cubicSymbol c.val 1=1 := by
      rw [cubic_reciprocity c.property primary_one,cubicSymbol_one_lower]
    have hcub := cubicSymbol_cube_of_isCoprime c.property lambdaE (primary_coprime_lambda c.property)
    rw [Units.val_one,hu,one_mul]
    have hp : ((cubicSymbol c.val lambdaE)^2)^2=cubicSymbol c.val lambdaE := by
      calc
        _ = (cubicSymbol c.val lambdaE)^3*cubicSymbol c.val lambdaE := by ring
        _ = _ := by rw [hcub,one_mul]
    rw [hp]
    ring
  · simp only [zero_mul,tsum_zero]

end CubicFirstMoment

end

end OAI
