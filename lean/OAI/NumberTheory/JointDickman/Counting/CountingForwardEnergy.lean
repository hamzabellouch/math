import OAI.NumberTheory.JointDickman.Counting.CountingFeatureRows

namespace OAI

/-! # Mean-square cancellation of the actual periodic forward graph rows -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_forward_row_energy
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
    {η : ℝ} (hη : 0 < η) {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) → ∀ i : Fin (M B),
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖countingForwardRow (fun j => F (j : ZMod q)) P m B L (T B) (H B) (M B) u
          τ C c D (σ u) z i‖^2) < ε := by
  let I := CountingFeatureIndex P m
  let K : ℝ := ∑ e : I, V*(2/channelMesh (m e.1.val))
  have hK : 0 ≤ K := sum_nonneg (fun e _ => mul_nonneg hV (by
    exact div_nonneg (by norm_num) (channelMesh_pos (hm e.1.val)).le))
  intro ε hε
  let ν := ε/((Fintype.card I : ℝ)^2*K^2+1)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hsmall : (Fintype.card I : ℝ)^2*K^2*ν < ε := by
    dsimp [ν]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (Fintype.card I : ℝ)^2*K^2+1)).mpr
    nlinarith
  have hshort (e : I) := coarse_counting_row_energy hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean P e.1.val (hm e.1.val) (c e.1.val) (hc e.1.val)
    (D e.1.val) e.2.1 hη (q := q) F W hF A scale T H R M hA hscale hR hRT hvalid ν hν
  filter_upwards [eventually_all.mpr hshort,hroot,hvalid] with B hshort hrootB hvalidB
  filter_upwards [eventually_all.mpr hshort,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0]
    with n hn hX
  intro σ hσ i z
  let X := A B*scale n
  let S := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let α := fun u (e : I) => (independentRootMean B L τ C : ℂ)*
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
      (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1)))
  let β := fun u (e : I) => countingTermRow (fun j => F (j : ZMod q)) P e.1.val
    (m e.1.val) B (T B) (H B) (M B) u (c e.1.val) (D e.1.val) (σ u) z i e.2.1 e.2.2
  have hα (u : ℕ) (_ : u ∈ S) (e : I) (_ : e ∈ univ) : ‖α u e‖ ≤ K := by
    have hb := norm_centered_coarse_weight_le
      (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ hζ μ hμ
      (hm e.1.val) B e.2.2 (u+(i.val+1))
    change ‖z (u+(i.val+1))*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
        (u+(i.val+1)) : ℂ)‖ ≤ _ at hb
    rw [norm_mul] at hb
    have hn : ‖α u e‖ ≤ V*(2/channelMesh (m e.1.val)) := by
      dsimp only [α]
      rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (independentRootMean_nonneg B L τ C),norm_mul,norm_star,mul_comm _ ‖z _‖]
      exact mul_le_mul hrootB hb (by positivity) hV
    exact hn.trans (single_le_sum (fun f _ => mul_nonneg hV
      (div_nonneg (by norm_num) (channelMesh_pos (hm f.1.val)).le)) (mem_univ e))
  have hβ (e : I) (_ : e ∈ univ) : (1/X)*(∑ u ∈ S, ‖β u e‖^2) ≤ ν := by
    have hU : 0 < min (T B) (M B-i.val) ∧ min (T B) (M B-i.val) ≤ T B :=
      ⟨lt_min hvalidB.1 (by omega),min_le_left _ _⟩
    simpa only [X,S,β,countingTermRow,Nat.add_assoc] using
      (hn e e.2.1 e.2.2 σ (fun _ => min (T B) (M B-i.val)) hσ (fun _ => hU)
        (i.val+1) (by omega)).le
  have hh := finite_weighted_square_mean S (univ : Finset I) α β hX hα hβ
  simp only [card_univ] at hh
  have heq (u : ℕ) : countingForwardRow (fun j => F (j : ZMod q)) P m B L
      (T B) (H B) (M B) u τ C c D (σ u) z i = ∑ e : I, α u e*β u e :=
    countingForwardRow_features_flat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [heq]
  exact hh.trans_lt hsmall

end JointDickman

end OAI
