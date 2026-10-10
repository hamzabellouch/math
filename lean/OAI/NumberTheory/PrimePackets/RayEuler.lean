import Mathlib
import OAI.NumberTheory.PrimePackets.RayCharacter

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

 
def allCoefficient (I : Ideal (𝓞 K)) : ℂ :=
  if hI : I ≠ ⊥ then
    if IsCoprime I (rationalModulusIdeal (𝓞 K) N) then
      (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)
    else 0
  else 0

@[simp] lemma allCoefficient_bot : ψ.allCoefficient ⊥ = 0 := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_zero : ψ.allCoefficient 0 = 0 := ψ.allCoefficient_bot

@[simp] lemma allCoefficient_one : ψ.allCoefficient 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (rationalModulusIdeal (𝓞 K) N) :=
    by rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  have ht : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  simp only [Ideal.one_eq_top, allCoefficient, dite_eq_left ht, hc,
    ite_true, integralIdealFractionalUnit_top, map_one, Units.val_one]

lemma integralUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    integralIdealFractionalUnit (I*J) (mul_ne_zero hI hJ) =
      integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I J

lemma allCoefficient_mul (I J : Ideal (𝓞 K)) :
    ψ.allCoefficient (I*J) = ψ.allCoefficient I * ψ.allCoefficient J := by
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  change I ≠ ⊥ at hI
  change J ≠ ⊥ at hJ
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [allCoefficient, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ,
    IsCoprime.mul_left_iff]
  by_cases hcI : IsCoprime I (rationalModulusIdeal (𝓞 K) N)
  · by_cases hcJ : IsCoprime J (rationalModulusIdeal (𝓞 K) N)
    · simp only [hcI, hcJ, and_self, ite_true]
      have H := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (ψ.idealHom U : ℂ)) (integralUnit_mul I J hI hJ)
      simpa only [map_mul, Units.val_mul] using H
    · simp [hcI, hcJ]
  · simp [hcI]

 

def coefficientHom : Ideal (𝓞 K) →*₀ ℂ where
  toFun := ψ.allCoefficient
  map_zero' := ψ.allCoefficient_zero
  map_one' := ψ.allCoefficient_one
  map_mul' := ψ.allCoefficient_mul

lemma allCoefficient_norm_le_one (I : Ideal (𝓞 K)) :
    ‖ψ.allCoefficient I‖ ≤ 1 := by
  unfold allCoefficient
  split_ifs with hI hc
  · rw [ψ.idealHom_norm]
  · simp
  · simp

lemma allCoefficient_underlying (J : integralFractionalIdeals K) :
    ψ.allCoefficient (underlyingIdeal J) = ψ.coefficient J := by
  rw [allCoefficient, dite_eq_left (underlyingIdeal_ne_bot J)]
  simp only [underlyingIdeal_unit, coefficient]

lemma norm_underlying (J : integralFractionalIdeals K) :
    (Ideal.absNorm (underlyingIdeal J) : ℚ) = FractionalIdeal.absNorm J.val.val := by
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), underlyingIdeal_coe]

 
def idealTerm {s : ℂ} (hs : 1 < s.re) : Ideal (𝓞 K) →*₀ ℂ :=
  ψ.coefficientHom * (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)).comp
    Ideal.absNorm

lemma idealTerm_apply {s : ℂ} (hs : 1 < s.re) (I : Ideal (𝓞 K)) :
    ψ.idealTerm hs I = ψ.allCoefficient I * (Ideal.absNorm I : ℂ)^(-s) := rfl

lemma idealTerm_underlying {s : ℂ} (hs : 1 < s.re) (J : integralFractionalIdeals K) :
    ψ.idealTerm hs (underlyingIdeal J) =
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s) := by
  rw [idealTerm_apply, allCoefficient_underlying, ← norm_underlying]
  simp

lemma idealTerm_summable_nonzero {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => ψ.idealTerm hs I.val) := by
  have H := (ψ.dirichlet_summable hs).comp_injective (integralFractionalIdealsEquiv K).injective
  exact H.congr (fun I => by
    have he : underlyingIdeal ((integralFractionalIdealsEquiv K) I) = I.val :=
      congrArg Subtype.val ((integralFractionalIdealsEquiv K).symm_apply_apply I)
    change ψ.coefficient ((integralFractionalIdealsEquiv K) I) *
      ((FractionalIdeal.absNorm ((integralFractionalIdealsEquiv K) I).val.val : ℝ) : ℂ)^(-s) = _
    have HH := (ψ.idealTerm_underlying hs ((integralFractionalIdealsEquiv K) I)).symm
    erw [he] at HH
    exact HH)

lemma idealTerm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (ψ.idealTerm hs) := by
  apply (hasSum_subtype_iff_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ ⊥})
    (f := ψ.idealTerm hs) ?_).mp (ψ.idealTerm_summable_nonzero hs).hasSum |>.summable
  intro I hI hi
  apply hI
  subst I
  exact map_zero _

lemma dirichlet_eq_ideal_tsum {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑' I : Ideal (𝓞 K), ψ.idealTerm hs I := by
  have HE := (integralFractionalIdealsEquiv K).symm.tsum_eq
    (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => ψ.idealTerm hs I.val)
  change (∑' J : integralFractionalIdeals K, _ ) = _ at HE
  have he : ψ.dirichlet s =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, ψ.idealTerm hs I.val := by
    rw [← HE]
    exact tsum_congr (fun J => (ψ.idealTerm_underlying hs J).symm)
  rw [he]
  apply tsum_subtype_eq_of_support_subset
  intro I hI hi
  apply hI
  subst I
  exact map_zero _

 
def normTerm {s : ℂ} (hs : 1 < s.re) (m : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, ψ.idealTerm hs I.val

lemma normTerm_zero {s : ℂ} (hs : 1 < s.re) : ψ.normTerm hs 0 = 0 := by
  unfold normTerm
  have H : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = 0}, ψ.idealTerm hs I.val = 0 := by
    intro I
    rw [Ideal.absNorm_eq_zero_iff.mp I.property]
    exact map_zero _
  simp only [H, tsum_zero]

lemma normTerm_one {s : ℂ} (hs : 1 < s.re) : ψ.normTerm hs 1 = 1 := by
  let oneI : {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} := ⟨⊤, Ideal.absNorm_top⟩
  have h : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = 1}, I = oneI := by
    intro I
    exact Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property)
  rw [normTerm, tsum_eq_single oneI (fun I hI => (hI (h I)).elim)]
  change ψ.idealTerm hs (⊤ : Ideal (𝓞 K)) = 1
  rw [← Ideal.one_eq_top]
  exact map_one (ψ.idealTerm hs)

lemma normTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (ψ.normTerm hs) := by
  exact ((ψ.idealTerm_summable hs).hasSum.tsum_fiberwise Ideal.absNorm).summable

lemma normTerm_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, ψ.normTerm hs m) = ψ.dirichlet s := by
  rw [ψ.dirichlet_eq_ideal_tsum hs]
  exact ((ψ.idealTerm_summable hs).hasSum.tsum_fiberwise Ideal.absNorm).tsum_eq

lemma normTerm_mul {s : ℂ} (hs : 1 < s.re) {m n : ℕ} (hc : m.Coprime n) :
    ψ.normTerm hs (m*n) = ψ.normTerm hs m * ψ.normTerm hs n := by
  by_cases hm : m = 0
  · simp [hm, ψ.normTerm_zero hs]
  by_cases hn : n = 0
  · simp [hn, ψ.normTerm_zero hs]
  unfold normTerm
  rw [← (idealNormProductEquiv K m n hm hn hc).tsum_eq]
  change (∑' IJ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 K) // Ideal.absNorm J = n}, ψ.idealTerm hs (IJ.1.val * IJ.2.val)) = _
  simp only [map_mul]
  exact (tsum_mul_tsum_of_summable_norm
    ((ψ.idealTerm_summable hs).subtype _).norm
    ((ψ.idealTerm_summable hs).subtype _).norm).symm

lemma prime_idealTerm_norm_lt_one {s : ℂ} (hs : 1 < s.re) {p : ℕ}
    (P : idealsOverPrime K p) : ‖ψ.idealTerm hs P.val‖ < 1 := by
  have H := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  change ‖ψ.allCoefficient P.val *
    riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.val)‖ < 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one P.val)).trans_lt H

 

theorem primary_ideal_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    (∑' I : PrimaryIdeal K p, ψ.idealTerm hs I.val) =
      ∏ P : idealsOverPrime K p, (1 - ψ.idealTerm hs P.val)⁻¹ := by
  have HM (m : Multiset (idealsOverPrime K p)) :
      ψ.idealTerm hs (primaryIdealMultisetEquiv K p m).val =
        (m.map (fun P => ψ.idealTerm hs P.val)).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => exact map_one _
    | @cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
      exact congrArg (fun z => ψ.idealTerm hs P.val * z) ih
  have HT := (complex_tsum_multiset_prod (fun P : idealsOverPrime K p =>
    ψ.idealTerm hs P.val) (ψ.prime_idealTerm_norm_lt_one hs)).2
  rw [← (primaryIdealMultisetEquiv K p).tsum_eq]
  exact (tsum_congr HM).trans HT

theorem local_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, ψ.normTerm hs (p^e)) =
      ∏ P : idealsOverPrime K p, (1 - ψ.idealTerm hs P.val)⁻¹ := by
  have HS : Summable (fun I : PrimaryIdeal K p => ψ.idealTerm hs I.val) :=
    (ψ.idealTerm_summable hs).subtype _
  have HE := (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σ e : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
        ψ.idealTerm hs I.2.val := HE.tsum_sigma.symm
    _ = ∑' I : PrimaryIdeal K p, ψ.idealTerm hs I.val :=
      (primaryIdealNormEquiv K p hp).tsum_eq (fun I => ψ.idealTerm hs I.val)
    _ = _ := ψ.primary_ideal_euler hs

 
theorem dirichlet_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏ P : idealsOverPrime K (p:ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) (ψ.dirichlet s) := by
  have HE := EulerProduct.eulerProduct_hasProd (ψ.normTerm_one hs)
    (fun h => ψ.normTerm_mul hs h) (ψ.normTerm_summable hs).norm (ψ.normTerm_zero hs)
  rw [ψ.normTerm_tsum hs] at HE
  have he : (fun p : Nat.Primes => ∑' e : ℕ, ψ.normTerm hs ((p:ℕ)^e)) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime K (p:ℕ),
        (1 - ψ.idealTerm hs P.val)⁻¹) := by
    funext p
    exact ψ.local_euler hs p.property
  rwa [he] at HE

 

theorem dirichlet_ne_zero {s : ℂ} (hs : 1 < s.re) : ψ.dirichlet s ≠ 0 := by
  have Hlocal (p : Nat.Primes) : (∑' k : ℕ, ψ.normTerm hs ((p:ℕ)^k)) ≠ 0 := by
    rw [ψ.local_euler hs p.property]
    apply Finset.prod_ne_zero_iff.mpr
    intro P _
    apply inv_ne_zero
    intro h
    have HH := ψ.prime_idealTerm_norm_lt_one hs P
    rw [← sub_eq_zero.mp h, norm_one] at HH
    exact (lt_irrefl _ HH)
  have H := complex_multiplicative_tsum_ne_zero (ψ.normTerm hs) (ψ.normTerm_zero hs)
    (ψ.normTerm_one hs) (fun h => ψ.normTerm_mul hs h) (ψ.normTerm_summable hs).norm Hlocal
  rwa [ψ.normTerm_tsum hs] at H

 

theorem continued_ne_zero_of_one_lt_re {d : ℕ} [NumberField.IsTotallyReal K]
    [NeZero N] (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue ≠ 1) {s : ℂ} (hs : 1 < s.re) : ψ.continued σ s ≠ 0 := by
  rw [ψ.continued_eq_dirichlet σ hn hψ hs]
  exact ψ.dirichlet_ne_zero hs

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
