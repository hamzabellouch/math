import OAI.NumberTheory.JointDickman.Counting.EnergyMeanComparison
import OAI.NumberTheory.JointDickman.Counting.CountingKernelBound

namespace OAI

/-! # Vanishing mean energy for the full singular-series counting model -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_model_energy_mean
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        (|(complexEnergy (countingArithmeticKernel singularSeries P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))).re|/(M B : ℝ))) < ε := by
  obtain ⟨K,hK,hbound⟩ := countingPrimeKernel_bounded hM hMP P m hm c hc D
  intro ε hε
  let δ := ε/128
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨q,hq,F,happrox⟩ := countingSiteModel_periodic_approximation hMP hV hK hη hδ
  let : NeZero q := hq
  let W := ∑ r : ZMod q, |F r|
  have hF (r : ZMod q) : |F r| ≤ W := single_le_sum (fun s _ => abs_nonneg (F s)) (mem_univ r)
  let t := ε/8
  have ht : 0 < t := by dsimp [t]; positivity
  have henergy := counting_periodic_energy hMR hMRT hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean
    P m hm c hc D hη F W hF A scale T H R M L τ C hA hscale hR hRT hvalid hMpos hV hroot
    (t^2) (sq_pos_of_pos ht)
  filter_upwards [henergy,hbound,hvalid,hMpos,hroot] with B henergy hbound hvalidB hMB hrootB
  filter_upwards [henergy,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro σ hσ z
  let X := A B*scale n
  let S := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let K₁ := fun u => countingArithmeticKernel singularSeries P m B L (T B) (H B) (M B) u τ C c D (σ u)
  let K₂ := fun u => countingArithmeticKernel (fun j => F (j : ZMod q)) P m B L (T B) (H B) (M B) u τ C c D (σ u)
  let zs := fun u (i : Fin (M B)) => z (u+(i.val+1))
  let f := fun u => complexEnergy (K₂ u) (zs u)/(M B : ℂ)
  have hcard : (S.card : ℝ) ≤ 2*X := by
    dsimp only [S]
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (by positivity))
  have hf : (1/X)*(∑ u ∈ S, ‖f u‖^2) ≤ t^2 := by
    simpa only [f,K₂,zs,norm_div,Complex.norm_natCast] using (hn σ hσ).le
  have hfmean := finite_norm_mean_of_square S f hX ht hcard hf
  have hcut (u : ℕ) : kernelCutNorm (fun i k => K₁ u i k-K₂ u i k) ≤ δ := by
    have hh := happrox P m B L (T B) (H B) (M B) τ C c D (σ u) hvalidB.1 hMB hrootB
      hvalidB.2.2 (fun j _ _ => hbound j (T B) (σ u) (by exact_mod_cast hvalidB.1)
        hvalidB.2.1 (hσ u))
      (fun i => ⟨coefficientPrimeSet B (u+(i.val+1)),by simp [coefficientPrimeSet]⟩)
    exact hh
  have hpoint (u : ℕ) : |(complexEnergy (K₁ u) (zs u)).re|/(M B : ℝ) ≤ ‖f u‖+16*δ := by
    apply (normalized_energy_comparison hMB (K₁ u) (K₂ u) (zs u)
      (fun i => norm_centered_binLabel_le_two _ ζ hζ μ hμ _)).trans
    apply add_le_add
    · simpa only [f,norm_div,Complex.norm_natCast] using
        div_le_div_of_nonneg_right (Complex.abs_re_le_norm (complexEnergy (K₂ u) (zs u))) (Nat.cast_nonneg (M B))
    · exact mul_le_mul_of_nonneg_left (hcut u) (by norm_num)
  change (1/X)*(∑ u ∈ S, |(complexEnergy (K₁ u) (zs u)).re|/(M B : ℝ)) < ε
  calc
    _ ≤ (1/X)*(∑ u ∈ S, (‖f u‖+16*δ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ => hpoint u)) (by positivity)
    _ = (1/X)*(∑ u ∈ S, ‖f u‖)+(S.card : ℝ)/X*(16*δ) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul]
      ring
    _ ≤ 2*t+(t^2)/(4*t)+2*(16*δ) := by
      apply add_le_add hfmean
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hX).mpr hcard) (by positivity)
    _ < ε := by
      have hdiv : t^2/(4*t) = t/4 := by field_simp
      rw [hdiv]
      dsimp [t,δ]
      linarith

end JointDickman

end OAI
