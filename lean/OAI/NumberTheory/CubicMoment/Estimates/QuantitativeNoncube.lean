import OAI.NumberTheory.CubicMoment.Estimates.NoncubeSieveAssembly
import OAI.NumberTheory.CubicMoment.Estimates.NoncubePowerBounds

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

private lemma sieve_epsilon_loss {B p q ε : ℝ} (hB : 1 ≤ B)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsize : p+2*q ≤ 1) (hε : 0 ≤ ε) :
    (B^p*B)^ε ≤ B^(2*ε) ∧ (B^q*B)^ε ≤ B^(2*ε) ∧
      (B^p*B^q)^ε ≤ B^(2*ε) := by
  have hB0 : 0 < B := by linarith
  have hh (a : ℝ) (ha : a ≤ 1) : (B^a*B)^ε ≤ B^(2*ε) := by
    have he : B^a*B = B^(a+1) := by rw [Real.rpow_add hB0,Real.rpow_one]
    rw [he,← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB (mul_le_mul_of_nonneg_right (by linarith) hε)
  refine ⟨hh p (by linarith),hh q (by linarith),?_⟩
  rw [← Real.rpow_add hB0,← Real.rpow_mul hB0.le]
  exact Real.rpow_le_rpow_of_exponent_le hB (mul_le_mul_of_nonneg_right (by linarith) hε)

private lemma pSieveRatio_cancel {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*pSieveRatio B P Q = Q*(P+B+(P*B)^(2/3:ℝ)) := by
  unfold pSieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma qSieveRatio_cancel {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*qSieveRatio B P Q = P*(Q+B+(Q*B)^(2/3:ℝ)) := by
  unfold qSieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma ordinarySieveRatio_cancel {B P Q : ℝ} (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q) :
    (B*(P*Q^2)^(1/3:ℝ))*ordinarySieveRatio B P Q = B+(P*Q)^2 := by
  unfold ordinarySieveRatio
  have hD : B*(P*Q^2)^(1/3:ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ hD

private lemma scale_sieve_row {r j C T loss term E L W M D ratio : ℝ}
    (hr : 0 ≤ r) (hj : 0 ≤ j) (hE : 0 ≤ E) (hloss0 : 0 ≤ loss)
    (hterm : 0 ≤ term) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hCT : C*T ≤ L*W) (hloss : loss ≤ M) (hcancel : D*ratio = W*term) :
    r*j*C*(T*loss*term)*E ≤ (r*j*L*D*E)*M*ratio := by
  calc
    _ = r*j*(C*T)*loss*term*E := by ring
    _ ≤ r*j*(L*W)*M*term*E := by gcongr
    _ = (r*j*L*M*E)*(W*term) := by ring
    _ = (r*j*L*M*E)*(D*ratio) := by rw [hcancel]
    _ = _ := by ring

/-- Away from the two exceptional shapes, the actual quadratic character mass
saves a uniform power over `B*(P*Q²)^(1/3)` times coefficient energy. -/
theorem quantitative_noncube_mass (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (B p q : ℝ), 1 ≤ B → 0 ≤ p → 0 ≤ q → p+2*q ≤ 1 →
        κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      ∀ (A R S T J H : Finset Eisenstein),
        (∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ B) →
        (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ B^p) →
        (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ B^q) →
        H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
        C*(R.card:ℝ)*J.card*B*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-γ)*
          ∑ a ∈ A, ‖β a‖^2 := by
  obtain ⟨γ,hγ,hgap⟩ := uniform_noncube_ratio_saving hκ hδ
  let ε := γ/8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C₁,C₂,hC₁,hC₂,hraw⟩ := noncube_three_sieve_bounds hHuxley hε
  let L := 18*max C₁ C₂
  have hL : 0 < L := mul_pos (by norm_num) (lt_max_iff.mpr (Or.inl hC₁))
  refine ⟨3*L,γ/2,mul_pos (by norm_num) hL,by positivity,?_⟩
  intro B p q hB hp hq hsize hlarge hfirst hbalanced A R S T J H hA hS hT hH β
  let E := ∑ a ∈ A, ‖β a‖^2
  let D := B*(B^p*(B^q)^2)^(1/3:ℝ)
  let F := (R.card:ℝ)*J.card*L*D*E
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB0 : 0 < B := by linarith
  have hU : 1 ≤ B^p := Real.one_le_rpow hB hp
  have hV : 1 ≤ B^q := Real.one_le_rpow hB hq
  have hU0 : 0 < B^p := by positivity
  have hV0 : 0 < B^q := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hSc := primary_support_card_le S hU0.le (fun s hs => ⟨(hS s hs).1,(hS s hs).2.2⟩)
  have hTc := primary_support_card_le T hV0.le (fun t ht => ⟨(hT t ht).1,(hT t ht).2.2⟩)
  have hloss := sieve_epsilon_loss hB hp hq hsize hε.le
  have hCp : C₁*(T.card:ℝ) ≤ L*B^q := by
    calc
      _ ≤ max C₁ C₂*(18*B^q) := mul_le_mul (le_max_left _ _) hTc (by positivity) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hCq : C₁*(S.card:ℝ) ≤ L*B^p := by
    calc
      _ ≤ max C₁ C₂*(18*B^p) := mul_le_mul (le_max_left _ _) hSc (by positivity) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hCo : C₂ ≤ L := by
    apply (le_max_right C₁ C₂).trans
    dsimp [L]
    nlinarith [hC₁.le.trans (le_max_left C₁ C₂)]
  have hm := hraw A R S T J H B (B^p) (B^q) hB hU hV hA hS hT hH β
  have hcp : 0 ≤ (R.card:ℝ)*J.card*C₁ := by positivity
  have hmP : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₁*((T.card:ℝ)*(B^p*B)^ε*(B^p+B+(B^p*B)^(2/3:ℝ)))*E :=
    hm.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hcp)) hE)
  have hmQ : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₁*((S.card:ℝ)*(B^q*B)^ε*(B^q+B+(B^q*B)^(2/3:ℝ)))*E :=
    hm.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hcp)) hE)
  have hmO : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      (R.card:ℝ)*J.card*C₂*(B^p*B^q)^ε*((B^p*B^q)^2+B)*E :=
    hm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hE)
  have hP : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(2*ε)*pSieveRatio B (B^p) (B^q) := by
    exact hmP.trans (scale_sieve_row (by positivity) (by positivity) hE
      (by positivity) (by positivity) hL.le hV0.le hCp hloss.1
      (pSieveRatio_cancel hB0 hU0 hV0))
  have hQ : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(2*ε)*qSieveRatio B (B^p) (B^q) := by
    exact hmQ.trans (scale_sieve_row (by positivity) (by positivity) hE
      (by positivity) (by positivity) hL.le hU0.le hCq hloss.2.1
      (qSieveRatio_cancel hB0 hU0 hV0))
  have hO : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*B^(2*ε)*ordinarySieveRatio B (B^p) (B^q) := by
    have hh := scale_sieve_row (r := (R.card:ℝ)) (j := (J.card:ℝ))
      (C := C₂) (T := 1) (loss := (B^p*B^q)^ε) (term := B+(B^p*B^q)^2)
      (E := E) (L := L) (W := 1) (M := B^(2*ε)) (D := D)
      (ratio := ordinarySieveRatio B (B^p) (B^q))
      (by positivity) (by positivity) hE (by positivity) (by positivity) hL.le
      (by norm_num) (by simpa using hCo) hloss.2.2
      (by change (B*(B^p*(B^q)^2)^(1/3:ℝ))*ordinarySieveRatio B (B^p) (B^q) = _
          simpa only [one_mul] using ordinarySieveRatio_cancel hB0 hU0 hV0)
    apply hmO.trans
    convert hh using 1; ring
  have hmin : (∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2) ≤
      F*(B^(2*ε)*min (pSieveRatio B (B^p) (B^q))
        (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q)))) := by
    rw [← mul_assoc,mul_min_of_nonneg _ _ (mul_nonneg hF (by positivity)),
      mul_min_of_nonneg _ _ (mul_nonneg hF (by positivity))]
    exact le_min hP (le_min hQ hO)
  apply hmin.trans
  have hsave := hgap B p q (2*ε) hB hp hq hsize hlarge hfirst hbalanced
    (by dsimp [ε]; linarith)
  have hh := mul_le_mul_of_nonneg_left hsave hF
  convert hh using 1; dsimp [F,D,E]; ring_nf

end CubicFirstMoment

end

end OAI
