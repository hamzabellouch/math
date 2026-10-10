import OAI.NumberTheory.CubicMoment.Estimates.LogCellNearHeight
import OAI.NumberTheory.CubicMoment.Estimates.FarLogNormCells
import OAI.NumberTheory.CubicMoment.Estimates.LogCellCount
import OAI.NumberTheory.CubicMoment.Estimates.FarIntegratedBound

namespace OAI

/-! Summing the actual far cells after height integration by parts. The
only loss in their diagonal mass is the proved number of populated cells. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def logCellHeightSum (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) : ℂ :=
  ∑ a ∈ logNormCellSupport P J A e.1, ∑ b ∈ logNormCellSupport S J B e.2,
    (α a*β b*gauss (a*b))*heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)

theorem far_logCell_integrated_bound
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      65536 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
        K*(J/T)^2*M*J*(Real.sqrt (A/J)+
          Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))*
            Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨d,K,hK,hcell⟩ := logCell_bilinear_height_square hMV hC hHuxley
  let F := ∫ u : ℝ, ‖𝓕 farInverseSquare u‖
  have hF : 0 ≤ F := integral_nonneg (fun _ => _root_.norm_nonneg _)
  refine ⟨d,4*Real.sqrt K*(F+1),by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M hZ hA hX hT hM hP hS h hi hd hi' hd' hi'' hsecond hs
  have hZp : 0 < Z := by linarith
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hJp : 0 < J := by linarith
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  let E := farLogNormCells P S J A (Z/2) X₀
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  let b := fun j => Real.sqrt (∑ n ∈ logNormCellSupport S J (Z/2) j, ‖β n‖^2)
  let H := 2*Real.sqrt K*(Real.sqrt (A/J)+
    Real.sqrt (J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)))
  let L := (J/T)^2*M*H*(F+1)
  have hL : 0 ≤ L := by dsimp [L,H]; positivity
  have hbound (e : ℤ × ℤ) (he : e ∈ E) :
      ‖(T:ℂ)⁻¹*logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤ L*a e.1*b e.2 := by
    let Pi := logNormCellSupport P J A e.1
    let Sj := logNormCellSupport S J (Z/2) e.2
    let c := fun q : Eisenstein × Eisenstein => α q.1*β q.2*gauss (q.1*q.2)
    let n := fun q : Eisenstein × Eisenstein => q.1*q.2
    have hei : e.1 ∈ P.image (logNormCell J A) :=
      (Finset.mem_product.mp (farLogNormCells_subset P S J A (Z/2) X₀ he)).1
    have hm (v : ℝ) : dyadicHeightMean
        (fun t => ‖∑ q ∈ Pi.product Sj, c q*normTwist (t+v) (n q)‖) T ≤ H*a e.1*b e.2 := by
      have hsq := hcell J hJ P S α β Z A (Z/2) T v hZ hA hT hP hS e.1 hei e.2
      have hf : Continuous (fun t => logCellPolynomial P S α β J A (Z/2) e (v+t)) :=
        (logCellPolynomial_continuous P S α β J A (Z/2) e).comp (continuous_const.add continuous_id)
      have hn := height_cell_square_root hf hTp hK.le (by positivity) (by positivity)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsq
      have heq : (fun t => ‖∑ q ∈ Pi.product Sj, c q*normTwist (t+v) (n q)‖) =
          fun t => ‖logCellPolynomial P S α β J A (Z/2) e (v+t)‖ := by
        funext t
        congr 1
        rw [add_comm t v]
        exact Finset.sum_product Pi Sj _
      rw [heq]
      exact hn
    have hb := far_integrated_norm_bound (Pi.product Sj) c n h hi hd hi' hd' hi'' hJp hTp hM
      (Real.log X₀) (fun q hq =>
        (farLogNormCells_frequency P S (fun a ha => (hP a ha).1)
          (fun b hb => (hS b hb).1) J A (Z/2) hX he
          (Finset.mem_product.mp hq).1 (Finset.mem_product.mp hq).2).le) hsecond hs hm
    have heq : (∑ q ∈ Pi.product Sj, c q*heightFourierIntegral h
        (Real.log (norm (n q))-Real.log X₀)) = logCellHeightSum P S α β J A (Z/2) X₀ e h :=
      Finset.sum_product Pi Sj _
    rw [heq] at hb
    have hsmall : (J/T)^2*M*(H*a e.1*b e.2)*F ≤ L*a e.1*b e.2 := by
      have hh := mul_le_mul_of_nonneg_left (show F ≤ F+1 by linarith)
        (show 0 ≤ (J/T)^2*M*(H*a e.1*b e.2) by dsimp [H,a,b]; positivity)
      dsimp [L]
      nlinarith only [hh]
    exact hb.trans hsmall
  rw [Finset.mul_sum]
  apply (norm_sum_le E _).trans
  apply (Finset.sum_le_sum hbound).trans
  have hm := dyadic_logCell_pair_mass P S (by linarith : 1 ≤ J)
    (fun a ha => (hP a ha).2)
    (fun b hb => by
      constructor
      · exact (le_div_iff₀ (by positivity : 0 < Z/2)).mpr (by linarith [(hS b hb).2.2.1])
      · exact (div_le_iff₀ (by positivity : 0 < Z/2)).mpr (by linarith [(hS b hb).2.2.2]))
    E (farLogNormCells_subset P S J A (Z/2) X₀) α β
  calc
    (∑ e ∈ E, L*a e.1*b e.2) = L*(∑ e ∈ E, a e.1*b e.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ L*(2*J*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)) :=
      mul_le_mul_of_nonneg_left hm hL
    _ = _ := by dsimp [L,H]; ring

end CubicFirstMoment

end

end OAI
