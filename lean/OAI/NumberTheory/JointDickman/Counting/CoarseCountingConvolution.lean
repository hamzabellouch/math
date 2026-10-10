import OAI.NumberTheory.JointDickman.Arithmetic.CountingLagSmoothing
import OAI.NumberTheory.JointDickman.Amplification.CoarseCenteredWeight
import OAI.NumberTheory.JointDickman.Arithmetic.FiniteSmoothedMean

namespace OAI

/-! # Cancellation of the actual counting coefficient against a centered coarse feature -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem coarse_counting_convolution_energy
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (D : ℕ) (b₀ : Fin m) {η : ℝ} (hη : 0 < η)
    {q : ℕ} [NeZero q] (F : ZMod q → ℝ) (W : ℝ) (hF : ∀ r, |F r| ≤ W)
    (A scale : ℕ → ℝ) (T H R : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (a b : Fin m) (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let g := fun k =>
        (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b₀) k : ℂ)
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖∑ j ∈ range (T B+1),
          ((cutLagWeight (H B) (T B) (fun k =>
            countingTermCoefficient P d m B k c D (T B) (σ u) a b/(k : ℝ)) j : ℝ) : ℂ)*
              (F (j : ZMod q) : ℂ)*g (u+j)‖^2) < ε := by
  obtain ⟨C,hC,hsmooth⟩ := counting_lag_smoothing hM hMP P d hm c hc D hη
  obtain ⟨V,hV,hweight⟩ := counting_lag_weight_bound hM hMP P d hm c hc D hη
  let G : ℝ := 2/channelMesh m
  have hG : 0 < G := div_pos (by norm_num) (channelMesh_pos hm)
  have hW : 0 ≤ W := (abs_nonneg (F 0)).trans (hF 0)
  let err := fun B => (W*G*C*(q : ℝ))*((R B : ℝ)/(T B : ℝ))
  have herr : Tendsto err atTop (𝓝 0) := by simpa only [mul_zero] using hRT.const_mul (W*G*C*(q : ℝ))
  have herrsq : Tendsto (fun B => 4*(err B)^2) atTop (𝓝 0) := by
    simpa using (herr.pow 2).const_mul 4
  intro ε hε
  let ν := ε/(16*(V*W)^2+1)
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνsmall : 8*(V*W)^2*ν < ε/2 := by
    dsimp [ν]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 16*(V*W)^2+1)).mpr
    nlinarith
  have hshort := coarse_residue_smoothing_energy hMR hMRT hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b₀ (q := q) A scale R T hA hscale hR ν hν
  filter_upwards [hsmooth,hweight,hshort,hvalid,hR.eventually_gt_atTop 0,
    herrsq.eventually (eventually_lt_nhds (half_pos hε))]
    with B hsm hwt hshort hv hRB herrB
  filter_upwards [hshort,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro a b σ hσ g
  let X := A B*scale n
  let I := Ico ⌈X⌉₊ ⌊2*X⌋₊
  let S := range (T B+1)
  let K := fun u => cutLagWeight (H B) (T B) (fun k =>
    countingTermCoefficient P d m B k c D (T B) (σ u) a b/(k : ℝ))
  let α := fun u j => (K u j : ℂ)*(F (j : ZMod q) : ℂ)
  let β := fun u j => residueSmoothed g q (R B) (u+j)
  let f := fun u => ∑ j ∈ S, α u j*g (u+j)
  have hg : ∀ k, ‖g k‖ ≤ G := fun k => norm_centered_coarse_weight_le _ ζ hζ μ hμ hm B b₀ k
  have happrox (u : ℕ) (_ : u ∈ I) : ‖f u-∑ j ∈ S, α u j*β u j‖ ≤ err B := by
    have hh := hsm (T B) (H B) (σ u) hv.1 hv.2.1 hv.2.2 (hσ u) a b q (R B) u F g G W hRB hg hF
    change ‖f u-∑ j ∈ S, α u j*β u j‖ ≤ _ at hh
    exact hh.trans_eq (by dsimp [err]; push_cast; ring)
  have hα (u : ℕ) (_ : u ∈ I) (j : ℕ) (_ : j ∈ S) : ‖α u j‖ ≤ V*W/(T B : ℝ) := by
    dsimp only [α]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul (hwt (T B) (H B) (σ u) hv.1 hv.2.1 hv.2.2 (hσ u) a b j)
      (hF (j : ZMod q)) (abs_nonneg _) (by positivity : 0 ≤ V/(T B : ℝ))
    exact hh.trans_eq (by ring)
  have hβ (j : ℕ) (hj : j ∈ S) : (1/X)*(∑ u ∈ I, ‖β u j‖^2) ≤ ν :=
    (hn j (by have hh := mem_range.mp hj; omega)).le
  have hcard : (I.card : ℝ) ≤ 2*X := by
    dsimp only [I]
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (by positivity))
  have hh := finite_approximation_square_mean I S f α β hX hcard happrox hα hβ
  change (1/X)*(∑ u ∈ I, ‖f u‖^2) < ε
  apply hh.trans_lt
  have hfac : (S.card : ℝ)^2*(V*W/(T B : ℝ))^2 ≤ 4*(V*W)^2 := by
    simpa only [S,card_range,Nat.cast_add,Nat.cast_one] using succ_card_scaled_square hv.1 (V*W)
  have hmul := mul_le_mul_of_nonneg_right hfac hν.le
  have hbound : 4*(err B)^2+2*(S.card : ℝ)^2*(V*W/(T B : ℝ))^2*ν ≤
      4*(err B)^2+8*(V*W)^2*ν := by nlinarith
  exact hbound.trans_lt (by linarith)

end JointDickman

end OAI
