import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.Dyadic

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseReflectedPhasePowerfulBudget
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem powerful_half_norm_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ),1≤X →
      (∀ I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∑ I∈S,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ C*X^ε := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hcount⟩ := powerful_ideal_count δ hδ
  let C := D*(2:ℝ)^(1/2+δ)*(2+1/(δ*Real.log 2))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro S X hX hS
  have hx : 0<X := zero_lt_one.trans_le hX
  have hnorm (I : Ideal O) (hI : I∈S) :
      1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤X :=
    ⟨QuadraticMainBoundary.norm_one_le (hS I hI).1.1,(hS I hI).2⟩
  have hbin (j : Fin (columnDyadicLength X+1)) :
      ∑ I∈divisorDyadicBin S X j,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤
        D*(2:ℝ)^(1/2+δ)*X^δ := by
    let R := divisorDyadicScale j.val
    have hR : 1≤R := divisorDyadicScale_ge_one _
    have hr : 0<R := zero_lt_one.trans_le hR
    by_cases he : (divisorDyadicBin S X j).Nonempty
    · have hRX : R≤X := divisorDyadicBin_scale_le S X hnorm j he
      have hc : ((divisorDyadicBin S X j).card:ℝ) ≤ D*(2*R)^(1/2+δ) := by
        apply hcount _ _ (by linarith)
        intro I hI
        exact ⟨(hS I (Finset.mem_filter.mp hI).1).1,
          (divisorDyadicBin_bounds S X hnorm j I hI).2⟩
      have hw (I : Ideal O) (hI : I∈divisorDyadicBin S X j) :
          (Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ R^(-1/2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr (divisorDyadicBin_bounds S X hnorm j I hI).1
          (by norm_num)
      calc
        _ ≤ ((divisorDyadicBin S X j).card:ℝ)*R^(-1/2:ℝ) := by
          apply (Finset.sum_le_sum hw).trans_eq
          simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ (D*(2*R)^(1/2+δ))*R^(-1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _)
        _ = (D*(2:ℝ)^(1/2+δ))*(R^(1/2+δ)*R^(-1/2:ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le]
          ring
        _ = D*(2:ℝ)^(1/2+δ)*R^δ := by
          rw [←Real.rpow_add hr]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hRX hδ.le) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [sum_divisorDyadicBins S X]
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength X+1),D*(2:ℝ)^(1/2+δ)*X^δ :=
      Finset.sum_le_sum (fun j _=>hbin j)
    _ = (columnDyadicLength X+1:ℝ)*(D*(2:ℝ)^(1/2+δ)*X^δ) := by simp
    _ ≤ ((2+1/(δ*Real.log 2))*X^δ)*(D*(2:ℝ)^(1/2+δ)*X^δ) :=
      mul_le_mul_of_nonneg_right (columnDyadicLength_small_power δ hδ X hX) (by positivity)
    _ = C*X^ε := by
      calc
        _ = C*(X^δ*X^δ) := by dsimp [C];ring
        _ = _ := by rw [←Real.rpow_add hx,show δ+δ=ε by dsimp [δ];ring]

lemma rowPowerful_norm_le (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowPowerfulPart I):ℝ) ≤ Ideal.absNorm I := by
  apply QuadraticMainBoundary.norm_le_of_dvd hI
  exact ⟨rowSimplePart I,(row_powerful_simple_product I hI).symm⟩

theorem row_mask_powerful_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (S : Finset (Ideal O)) (Q : Ideal O),
      (∀ I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ((S.image (fun I=>rowMaskPart I Q)).card:ℝ)*
        (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ C*Z^ε := by
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cp,hCp,hpower⟩ := powerful_half_norm_sum δ hδ
  obtain ⟨Cd,hCd,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨Cd*Cp,mul_pos hCd hCp,?_⟩
  intro Z hZ S Q hS hQ hQN
  have hz : 0<Z := by linarith
  have hX : 1≤Z^L := Real.one_le_rpow (by linarith) hL
  have hp : (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ Cp*(Z^L)^δ := by
    apply hpower _ _ hX
    intro A hA
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨rowPowerfulPart_powerful I,(rowPowerful_norm_le I (hS I hI).1).trans (hS I hI).2⟩
  have hm : ((S.image (fun I=>rowMaskPart I Q)).card:ℝ) ≤ Cd*(Z^L)^δ :=
    ((Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)).trans (hdiv Q hQ)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hQN hδ.le) hCd.le)
  have he : L*(δ+δ) ≤ ε := by
    have heq : δ*(2*(L+1))=ε := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ (Cd*(Z^L)^δ)*(Cp*(Z^L)^δ) :=
      mul_le_mul hm hp (Finset.sum_nonneg (fun A _=>Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = (Cd*Cp)*((Z^L)^δ*(Z^L)^δ) := by ring
    _ = (Cd*Cp)*Z^(L*(δ+δ)) := by
      rw [←Real.rpow_add (Real.rpow_pos_of_pos hz L),←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (mul_pos hCd hCp).le

end SevenEighths.InverseReflectedPhasePowerfulBudget

end

end OAI
