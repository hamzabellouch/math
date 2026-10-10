import OAI.NumberTheory.CubicMoment.Estimates.MixedTwistedEuler
import OAI.NumberTheory.CubicMoment.Estimates.MixedPrimitiveFamily
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveSmoothBound

namespace OAI

/-! The original primary mixed smooth sum has the cubic second moment.
Its primitive characters, conductors, and Euler corrections are constructed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryMixedSmoothSum (a b : Eisenstein) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    mixedCubic a b x*mellinPhase t (norm x)*W (norm x/Z) else 0

theorem primary_mixed_smooth_cubic_moment (hpub : PrimitiveResidueHeckeInput)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (N Y Z J t : ℝ),
      primary b → Squarefree b → 1 ≤ N → 1 ≤ Y → 9 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧
        IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      (∑ a ∈ P, ‖primaryMixedSmoothSum a b W Z t‖^2) ≤
        C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_primitive_cubic_bound hpub hε
    W hW hpos hsm hδ H R hGI hGQ
  let K := ramifiedIdealPrimes.powerset
  refine ⟨C*(K.card:ℝ)^2,D*(K.card:ℝ)^2,by positivity,by positivity,?_⟩
  intro P b N Y Z J t hb hsb hN hY hZ hJ hZH hJH hP hcut
  have hZ0 : 0 < Z := by linarith
  obtain ⟨d,ψ,hspec⟩ := actual_primitive_mixed_family P hb hsb
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2.1,(hP a ha).2.2.2.2⟩)
  let V (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    ∑' ν, residueIdealChar (d a) (ψ a) ν*mellinPhase t (idealExponentNorm ν)*
      W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T)))
  let F (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    (-1:ℂ)^T.card*residueIdealChar (d a) (ψ a) (primeSetExponent T)*
      mellinPhase t (idealExponentNorm (primeSetExponent T))*V a T
  let B := C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R)
  have hrow (T : Finset EisensteinIdealPrime) (hT : T ∈ K) :
      (∑ a ∈ P, ‖F a T‖^2) ≤ B := by
    let r := idealExponentNorm (primeSetExponent T)
    have hr : 1 ≤ r := idealExponentNorm_ge_one _
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hr9 : r ≤ 9 := ramifiedEulerNorm_le hT
    have hZr : 1 ≤ Z/r := (le_div_iff₀ hr0).mpr (by linarith)
    have hZrZ : Z/r ≤ Z := div_le_self hZ0.le hr
    have hlocal (a : Eisenstein) (ha : a ∈ P) :
        ((residueHeckeScale (d a))^2*(1+|t|)^2)/((Z/r)*J) ≤ Y^(-δ) := by
      have hb0 : 0 ≤ norm b := norm_nonneg b
      have hB0 : 0 ≤ 27*N*norm b/(2*Real.pi)^2 := by positivity
      have haN : (residueHeckeScale (d a))^2 ≤ 27*N*norm b/(2*Real.pi)^2 :=
        (hspec a ha).2.2.2.2.2.trans (by gcongr; exact (hP a ha).2.2.1)
      have hprod : r*(residueHeckeScale (d a))^2 ≤ 9*(27*N*norm b/(2*Real.pi)^2) :=
        mul_le_mul hr9 haN (sq_nonneg _) (by norm_num)
      calc
        _ = (r*(residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) := by
          field_simp
        _ ≤ (9*(27*N*norm b/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)) (by positivity)
        _ = ((243*N*norm b/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) := by ring
        _ ≤ _ := hcut
    have hv := hbound P b d ψ N Y (Z/r) J t hb hsb hN hY hZr hJ
      (hZrZ.trans hZH) hJH
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1,(hP a ha).2.2.2.1⟩)
      (fun a ha => (hspec a ha).1) (fun a ha => (hspec a ha).2.1)
      (fun a ha => (hspec a ha).2.2.1) (fun a ha => (hspec a ha).2.2.2.1)
      (fun a ha => (hspec a ha).2.2.2.2.1) hlocal
    calc
      _ ≤ ∑ a ∈ P, ‖V a T‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ‖(-1:ℂ)^T.card*residueIdealChar (d a) (ψ a) (primeSetExponent T)*
            mellinPhase t (idealExponentNorm (primeSetExponent T))‖ ≤ 1 := by
          simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
            mellinPhase_norm,mul_one] using
            residueIdealChar_norm_le_one (hspec a ha).1 (ψ a) (primeSetExponent T)
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        exact (norm_mul _ _).trans_le (mul_le_of_le_one_left (_root_.norm_nonneg _) hc)
      _ ≤ C*(Z/r)*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := hv
      _ ≤ B := by dsimp [B]; gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      primaryMixedSmoothSum a b W Z t = ∑ T ∈ K, F a T :=
    primary_mixed_twisted_euler (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2.1 (ψ a) (hspec a ha).2.2.2.1 (hspec a ha).2.2.2.2.1 W hW hZ0 t
  calc
    _ = ∑ a ∈ P, ‖∑ T ∈ K, F a T‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ (K.card:ℝ)*∑ T ∈ K, ∑ a ∈ P, ‖F a T‖^2 := complex_mass_sum_sq_le K P F
    _ ≤ (K.card:ℝ)*∑ _T ∈ K, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = _ := by simp [B]; ring

end CubicFirstMoment

end

end OAI
