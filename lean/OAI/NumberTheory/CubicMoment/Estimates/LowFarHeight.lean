import OAI.NumberTheory.CubicMoment.Estimates.LowNearHeight
import OAI.NumberTheory.CubicMoment.Estimates.FarLogCellHeight

namespace OAI

/-! The far cells gain two integrations by parts. The diagonal and the
logarithmic remainder retain their separate cell-count costs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

theorem low_far_logCell_integrated_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
      K*(J/T)^2*H*(J*Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*
        Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  obtain ⟨d,hfamily⟩ := low_logCell_bilinear_height_square hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hcell⟩ := hfamily q
  let F := ∫ u : ℝ, ‖𝓕 farInverseSquare u‖
  have hF : 0 ≤ F := integral_nonneg (fun _ => _root_.norm_nonneg _)
  refine ⟨8*Real.sqrt K*(F+1),Ct,by positivity,?_⟩
  intro J hJ P S α β Z A X₀ T M H hZ hA hX hT hM hH hP hS hβ h hi hd hi' hd' hi'' hsecond hs
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le
    (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hTp : 0 < T := (pow_pos hL _).trans_le hT
  have hJp : 0 < J := by linarith
  let E := farLogNormCells P S J A (Z/2) X₀
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  let b := fun j => Real.sqrt (∑ n ∈ logNormCellSupport S J (Z/2) j, ‖β n‖^2)
  let R := J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q
  let H₁ := 2*Real.sqrt K*Real.sqrt (A/J)
  let H₂ := 2*Real.sqrt K*Real.sqrt R
  let L := (J/T)^2*H*F
  have hLp : 0 ≤ L := by dsimp [L]; positivity
  have hbound (e : ℤ × ℤ) (he : e ∈ E) :
      ‖(T:ℂ)⁻¹*logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
        L*(H₁*a e.1*b e.2+H₂*a e.1) := by
    let Pi := logNormCellSupport P J A e.1
    let Sj := logNormCellSupport S J (Z/2) e.2
    let c := fun p : Eisenstein × Eisenstein => α p.1*β p.2*gauss (p.1*p.2)
    let n := fun p : Eisenstein × Eisenstein => p.1*p.2
    have hei : e.1 ∈ P.image (logNormCell J A) :=
      (Finset.mem_product.mp (farLogNormCells_subset P S J A (Z/2) X₀ he)).1
    have hm (v : ℝ) : dyadicHeightMean
        (fun t => ‖∑ p ∈ Pi.product Sj, c p*normTwist (t+v) (n p)‖) T ≤
        H₁*a e.1*b e.2+H₂*a e.1 := by
      have hsq := hcell J hJ P S α β Z A (Z/2) T M v hZ hA hT hM hP hS hβ e.1 hei e.2
      have hf : Continuous (fun t => logCellPolynomial P S α β J A (Z/2) e (v+t)) :=
        (logCellPolynomial_continuous P S α β J A (Z/2) e).comp (continuous_const.add continuous_id)
      have hn := height_mixed_square_root hf hTp hK.le (by positivity)
        (show 0 ≤ R by dsimp [R]; positivity)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsq
      have heq : (fun t => ‖∑ p ∈ Pi.product Sj, c p*normTwist (t+v) (n p)‖) =
          fun t => ‖logCellPolynomial P S α β J A (Z/2) e (v+t)‖ := by
        funext t
        congr 1
        rw [add_comm t v]
        exact Finset.sum_product Pi Sj _
      rw [heq]
      convert hn using 1
      dsimp [H₁,H₂,a,b]
      ring
    have hb := far_integrated_norm_bound (Pi.product Sj) c n h hi hd hi' hd' hi'' hJp hTp hH
      (Real.log X₀) (fun p hp =>
        (farLogNormCells_frequency P S (fun a ha => (hP a ha).1)
          (fun b hb => (hS b hb).1) J A (Z/2) hX he
          (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2).le) hsecond hs hm
    have heq : (∑ p ∈ Pi.product Sj, c p*heightFourierIntegral h
        (Real.log (norm (n p))-Real.log X₀)) = logCellHeightSum P S α β J A (Z/2) X₀ e h :=
      Finset.sum_product Pi Sj _
    rw [heq] at hb
    convert hb using 1
    dsimp [L]
    ring
  have hSratio : ∀ b ∈ S, 1 ≤ norm b/(Z/2) ∧ norm b/(Z/2) ≤ 2 := by
    intro b hb
    constructor
    · exact (le_div_iff₀ (by positivity : 0 < Z/2)).mpr (by linarith [(hS b hb).2.2.1])
    · exact (div_le_iff₀ (by positivity : 0 < Z/2)).mpr (by linarith [(hS b hb).2.2.2])
  have hab := dyadic_logCell_pair_mass P S (by linarith : 1 ≤ J)
    (fun a ha => (hP a ha).2) hSratio E (farLogNormCells_subset P S J A (Z/2) X₀) α β
  have ha := dyadic_logCell_left_mass P S (by linarith : 1 ≤ J)
    (fun a ha => (hP a ha).2) hSratio E (farLogNormCells_subset P S J A (Z/2) X₀) α
  rw [Finset.mul_sum]
  apply (norm_sum_le E _).trans ((Finset.sum_le_sum hbound).trans ?_)
  calc
    _ = L*(H₁*(∑ e ∈ E, a e.1*b e.2)+H₂*(∑ e ∈ E, a e.1)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_assoc]
    _ ≤ L*(H₁*(2*J*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2))+
        H₂*(4*J^2*Real.sqrt (∑ a ∈ P, ‖α a‖^2))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hab (by dsimp [H₁]; positivity))
        (mul_le_mul_of_nonneg_left ha (by dsimp [H₂]; positivity))) hLp
    _ ≤ _ := by
      have hdiag : 0 ≤ (J/T)^2*H*Real.sqrt K*J*Real.sqrt (A/J)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by positivity
      have hrem : 0 ≤ (J/T)^2*H*Real.sqrt K*J^2*Real.sqrt R*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2) := by positivity
      dsimp [L,H₁,H₂,R] at hdiag hrem ⊢
      nlinarith only [hdiag,hrem,mul_nonneg hF hdiag]

end CubicFirstMoment

end

end OAI
