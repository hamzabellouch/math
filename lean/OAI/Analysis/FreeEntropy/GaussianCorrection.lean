import OAI.Analysis.FreeEntropy.FreeEntropyFlow

namespace OAI

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace FiniteEntropySeparation
namespace Model
variable (p : ℕ) [NeZero p]
 theorem isotropic_gaussian_correction {a : ℝ} (ha : 0<a) :
    ((p+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+a))≤gaussianEntropy p a+1/(2*a) := by
  have hz : 0<2*Real.pi*Real.exp 1 := by positivity
  have hv := variance_nonneg p (Fin.last p)
  have hl : Real.log (1+a)-Real.log (a+variance p (Fin.last p))≤1/a := by
    have he : Real.log (1+a)-Real.log a≤1/a := by
      rw [← Real.log_div (by positivity) ha.ne']
      have hb := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<1+a) ha)
      have he : (1+a)/a-1=1/a := by field_simp; ring
      rwa [he] at hb
    have hm := Real.log_le_log ha (show a≤a+variance p (Fin.last p) by linarith)
    linarith
  rw [Real.log_mul hz.ne' (by positivity)]
  unfold gaussianEntropy
  rw [Fin.sum_univ_castSucc]
  simp only [variance_castSucc,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  have he : 1/(2*a)=(1/2:ℝ)*(1/a) := by ring
  rw [he,add_comm a 1]
  nlinarith
end Model
 theorem chosen_cumulantConstant : Model.cumulantConstant chosenP=(2:ℝ)^23 := by
  norm_num [Model.cumulantConstant,chosenP]
 theorem chosen_large_noise {h : ℝ} (hh : 0≤h) :
    2*(Model.cumulantConstant chosenP)^2≤h+chosenTime := by
  rw [chosen_cumulantConstant]
  norm_num [chosenTime] at *
  linarith
 theorem chosen_gaussian_correction {h : ℝ} (hh : 0<h) :
    ((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+h+chosenTime))≤
      Model.gaussianEntropy chosenP (h+chosenTime)+(1:ℝ)/2 := by
  have ht : 1≤h+chosenTime := by norm_num [chosenTime] at *; linarith
  have hb := Model.isotropic_gaussian_correction chosenP (show 0<h+chosenTime by linarith)
  have hc : 1/(2*(h+chosenTime))≤(1:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0<2*(h+chosenTime))).mpr
    linarith
  rw [← add_assoc] at hb
  linarith
 theorem chosen_terminal_gaussian {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hn : ∀k,(diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (chosenP+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)) :
    ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) chosenTime≤Model.gaussianEntropy chosenP (h+chosenTime)-1 := by
  filter_upwards [chosen_terminal_isotropic hD0 hD hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hn μ hμ] with k hk
  linarith [chosen_gaussian_correction hh0]
end FiniteEntropySeparation

end

end OAI
