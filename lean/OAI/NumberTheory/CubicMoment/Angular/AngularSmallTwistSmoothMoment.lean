import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedEuler
import OAI.NumberTheory.CubicMoment.Estimates.SmallEulerDivisors
import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedPrimitiveFamily
import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedSmoothBound

namespace OAI

/-! The original primary mixed smooth sum has the cubic second moment.
Its primitive characters, conductors, and Euler corrections are constructed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryAngularSmallTwistSmoothSum (ℓ : ℤ) (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)*W (norm x/Z) else 0

theorem primary_angular_smalltwist_smooth_cubic_moment (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧
        IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤
        C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^(3*ε) +
          D*P.card*Y^(-2*R)*norm (3*q)^(2*ε) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_angular_twisted_primitive_cubic_bound hpub ℓ hε
    W hW hpos hsm hδ H R hGI hGQ
  obtain ⟨E,hE,hEbound⟩ := euler_parts_card_small_power hε
  refine ⟨C*E^2,D*E^2,by positivity,by positivity,?_⟩
  intro P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ hZH hJH hP hcut
  let K := (idealExponentOf (3*q)).support.powerset
  have h3q : (3:Eisenstein)*q ≠ 0 := mul_ne_zero (by norm_num) hq
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  have hNq : 0 < norm q := norm_pos_of_ne_zero hq
  have hNpow : 0 ≤ norm (3*q)^ε := Real.rpow_nonneg (norm_nonneg _) _
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  obtain ⟨d,ψ,hspec⟩ := actual_primitive_angular_smalltwist_family P hb hsb hq η ℓ hη
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2.1,(hP a ha).2.2.2.2⟩) hsmall
  let V (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    ∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
      W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T)))
  let F (a : Eisenstein) (T : Finset EisensteinIdealPrime) : ℂ :=
    (-1:ℂ)^T.card*angularResidueIdealChar (d a) (ψ a) ℓ (primeSetExponent T)*
      mellinPhase t (idealExponentNorm (primeSetExponent T))*V a T
  let B := C*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^ε + D*P.card*Y^(-2*R)
  have hrow (T : Finset EisensteinIdealPrime) (hT : T ∈ K) :
      (∑ a ∈ P, ‖F a T‖^2) ≤ B := by
    let r := idealExponentNorm (primeSetExponent T)
    have hr : 1 ≤ r := idealExponentNorm_ge_one _
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have hr9 : r ≤ 9*norm q := by
      simpa only [norm_mul_eq,h3] using euler_part_norm_le h3q hT
    have hZr : 1 ≤ Z/r := (le_div_iff₀ hr0).mpr (by linarith)
    have hZrZ : Z/r ≤ Z := div_le_self hZ0.le hr
    have hlocal (a : Eisenstein) (ha : a ∈ P) :
        ((residueHeckeScale (d a))^2*(1+|t|)^2)/((Z/r)*J) ≤ Y^(-δ) := by
      have hb0 : 0 ≤ norm b := norm_nonneg b
      have hB0 : 0 ≤ 27*N*norm b*norm q/(2*Real.pi)^2 := by positivity
      have haN : (residueHeckeScale (d a))^2 ≤ 27*N*norm b*norm q/(2*Real.pi)^2 :=
        (hspec a ha).2.2.2.2.2.trans (by gcongr; exact (hP a ha).2.2.1)
      have hprod : r*(residueHeckeScale (d a))^2 ≤ (9*norm q)*(27*N*norm b*norm q/(2*Real.pi)^2) :=
        mul_le_mul hr9 haN (sq_nonneg _) (by positivity)
      calc
        _ = (r*(residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) := by
          field_simp
        _ ≤ ((9*norm q)*(27*N*norm b*norm q/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)) (by positivity)
        _ = ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) := by ring
        _ ≤ _ := hcut
    have hv := hbound P b d ψ q η N Y (Z/r) J t hb hsb hq hη hsmall hN hY hZr hJ
      (hZrZ.trans hZH) hJH
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1,(hP a ha).2.2.2.1⟩)
      (fun a ha => (hspec a ha).1) (fun a ha => (hspec a ha).2.1)
      (fun a ha => Or.inr (hspec a ha).2.2.1) (fun a ha => (hspec a ha).2.2.2.1)
      (fun a ha => (hspec a ha).2.2.2.2.1) hlocal
    calc
      _ ≤ ∑ a ∈ P, ‖V a T‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ‖(-1:ℂ)^T.card*angularResidueIdealChar (d a) (ψ a) ℓ (primeSetExponent T)*
            mellinPhase t (idealExponentNorm (primeSetExponent T))‖ ≤ 1 := by
          simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
            mellinPhase_norm,mul_one] using
            angularResidueIdealChar_norm_le_one (hspec a ha).1 (ψ a) ℓ (primeSetExponent T)
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        exact (norm_mul _ _).trans_le (mul_le_of_le_one_left (_root_.norm_nonneg _) hc)
      _ ≤ C*(Z/r)*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^ε + D*P.card*Y^(-2*R) := hv
      _ ≤ B := by dsimp [B]; gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t = ∑ T ∈ K, F a T :=
    primary_angular_smalltwist_euler (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2.1 hq (hsmall a ha) (ψ a) η ℓ (hspec a ha).2.2.2.1 hη
      (hspec a ha).2.2.2.2.1 W hW hZ0 t
  calc
    _ = ∑ a ∈ P, ‖∑ T ∈ K, F a T‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ (K.card:ℝ)*∑ T ∈ K, ∑ a ∈ P, ‖F a T‖^2 := complex_mass_sum_sq_le K P F
    _ ≤ (K.card:ℝ)*∑ _T ∈ K, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = (K.card:ℝ)^2*B := by simp; ring
    _ ≤ (E*norm (3*q)^ε)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (hEbound (3*q) h3q) 2) (by dsimp [B]; positivity)
    _ = _ := by
      have hNp : 0 < norm (3*q) := norm_pos_of_ne_zero h3q
      have h2 : (norm (3*q)^ε)^2 = norm (3*q)^(2*ε) := by
        rw [← Real.rpow_mul_natCast hNp.le]
        congr 1
        norm_num
        ring
      dsimp [B]
      rw [mul_pow,h2]
      rw [show 3*ε = ε+2*ε by ring,Real.rpow_add hNp]
      ring

end CubicFirstMoment

end

end OAI
