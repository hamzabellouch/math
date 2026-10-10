import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortMoments
import OAI.NumberTheory.CubicMoment.Estimates.NeighborhoodGeometry
import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortNeighborhoods

namespace OAI

/-! The first exceptional moment for the actual product of smooth
short-inverse factors. Both the all-short and dominant cases are proved. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_smooth_product_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsm : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlow : ∀ i x, x < 1 → W i x = 0) (hWup : ∀ i x, 2 < x → W i x = 0)
    (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(37/100:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,_,ε,hε,T₀,hshort⟩ := all_short_smooth_cubic_neighborhood (ι := ι)
    (show (0:ℝ) < 1/10000 by norm_num) hD
  obtain ⟨M,hM,hred⟩ := dominant_smooth_cubic_moment_reduction (ι := ι) hD
    (show (0:ℝ) ≤ 1/10000 by norm_num) (show (0:ℝ) < 1/10000 by norm_num)
  choose K T hK hT hfull using fun i => dominant_first_full_factor_neighborhood hpub
    (W i) (hW i) (hpos i) (hsm i) (hWlow i) hGI hGQ D
  let B : ℝ := M^2*∑ i, K i
  have hKall : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hK i)
  obtain ⟨T₁,hpow⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 6/625 by norm_num)).eventually_ge_atTop B)
  obtain ⟨T₂,_,hrows⟩ := eventual_first_neighborhood_rows
  refine ⟨min κ (1/10000),by positivity,min_le_right _ _,min ε (1/300),lt_min hε (by norm_num),max (max 2 T₂) (max T₀ (max (∑ i, T i) T₁)),?_⟩
  intro F Y N X A q η t P hY hNlo hNhi hF hA hX hlo hhi hq hη hqY ht hP
  have hY2 : 2 ≤ Y := (le_max_left 2 T₂).trans ((le_max_left _ _).trans hY)
  have hYT₂ : T₂ ≤ Y := (le_max_right 2 T₂).trans ((le_max_left _ _).trans hY)
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT : (∑ i, T i) ≤ Y := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  by_cases hall : ∀ i, X i ≤ Y^(1-(1/10000:ℝ))
  · exact (hshort F Y N X A q η W t P hYT₀
      ((Real.rpow_le_rpow_of_exponent_le hY1
        (by have := min_le_left κ (1/10000); linarith)).trans hNlo)
      (hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY1
        (by have := min_le_left κ (1/10000); linarith))) hA hX hq hWnorm hWup hall hlo hhi hP).trans
      (Real.rpow_le_rpow_of_exponent_le hY1 (by have := min_le_left ε (1/300); linarith))
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    have hlong : Y^(1-(1/10000:ℝ)) ≤ X i := hi.le
    have hXi : X i ≤ D*Y := by
      apply le_trans _ hhi
      calc
        X i = ∏ j ∈ ({i} : Finset ι), X j := by simp
        _ ≤ ∏ j, X j := Finset.prod_le_prod_of_subset_of_one_le₀ (by simp)
          (fun j _ => zero_le_one.trans (hX j)) (fun j _ _ => hX j)
    have hTi : T i ≤ Y := (Finset.single_le_sum (fun j _ => by linarith [hT j]) (Finset.mem_univ i)).trans hYT
    have hfulli := hfull i P (q i) (η i) (A i) F Y (X i) (t i)
      hTi (hA i) hF (hq i) (hη i) (hqY i) (ht i)
      (by convert hlong using 1; norm_num) hXi (fun a ha => hrows Y _ N hYT₂ (min_le_right _ _) hNlo hNhi a (hP a ha))
    have hreduce := hred F Y X A q η W t P i hA hX hq hWnorm hWup hY1
      (fun a ha => (hP a ha).1) hhi hlong
    have hKi : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
    have hp : (Y^((1/10000:ℝ)+1/10000))^2*Y^(58/25:ℝ) = Y^(5801/2500:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le,← Real.rpow_add hY0]
      norm_num
    calc
      _ ≤ (M*Y^((1/10000:ℝ)+1/10000))^2*(K i*Y^(58/25:ℝ)) :=
        hreduce.trans (mul_le_mul_of_nonneg_left hfulli (sq_nonneg _))
      _ ≤ (M*Y^((1/10000:ℝ)+1/10000))^2*((∑ j, K j)*Y^(58/25:ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKi (Real.rpow_nonneg hY0.le _)) (sq_nonneg _)
      _ = B*Y^(5801/2500:ℝ) := by dsimp [B]; rw [mul_pow]; rw [← hp]; ring
      _ ≤ Y^(6/625:ℝ)*Y^(5801/2500:ℝ) :=
        mul_le_mul_of_nonneg_right (hpow Y hYT₁) (Real.rpow_nonneg hY0.le _)
      _ = Y^(233/100:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ Y^(7/3-min ε (1/300)) := Real.rpow_le_rpow_of_exponent_le hY1
        (by have := min_le_right ε (1/300); linarith)

end CubicFirstMoment

end

end OAI
