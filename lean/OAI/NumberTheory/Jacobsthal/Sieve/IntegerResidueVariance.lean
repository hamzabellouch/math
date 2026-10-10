import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.ReducedFractions
import OAI.NumberTheory.Jacobsthal.Harmonic.FourierDerivative
import OAI.NumberTheory.Jacobsthal.Harmonic.HyperbolaFourier

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

noncomputable def exponential (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

theorem monomial_eq_exponential (n : ℤ) (x : ℝ) :
    monomial n x = exponential ((n : ℝ) * x) := by
  rw [monomial, fourier_coe_apply]
  simp only [exponential, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

theorem monomial_add (m n : ℤ) (x : ℝ) :
    monomial (m + n) x = monomial m x * monomial n x := fourier_add

theorem monomial_norm (n : ℤ) (x : ℝ) : ‖monomial n x‖ = 1 := by
  exact Circle.norm_coe _

theorem shifted_sum_norm (J : ℕ) (M : ℤ) (b : ℕ → ℂ) (x : ℝ) :
    ‖∑ j ∈ Finset.range J, b j * exponential (((M + (j : ℤ) : ℤ) : ℝ) * x)‖ =
      ‖∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x‖ := by
  simp_rw [← monomial_eq_exponential]
  have h : (∑ j ∈ Finset.range J, b j * monomial (M + (j : ℤ)) x) =
      monomial M x * ∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [monomial_add]
    ring
  rw [h, norm_mul, monomial_norm, one_mul]

theorem separated_consecutive_bound {ι : Type*} (samples : Finset ι) (t : ι → ℝ)
    (J : ℕ) (M : ℤ) (b : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpoints : ∀ i ∈ samples, t i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i ∈ samples, ∀ j ∈ samples, i ≠ j → δ ≤ |t i - t j|) :
    (∑ i ∈ samples, ‖∑ j ∈ Finset.range J,
      b j * exponential (((M + (j : ℤ) : ℤ) : ℝ) * t i)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * ((J : ℝ) + δ⁻¹) * ∑ j ∈ Finset.range J, ‖b j‖ ^ 2 := by
  by_cases hJ : J = 0
  · simp [hJ]
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  let s : Finset ℤ := (Finset.range J).image (fun j : ℕ => (j : ℤ))
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := Int.ofNat_injective
  have hf (n : ℤ) (hn : n ∈ s) : |(n : ℝ)| ≤ (J : ℝ) := by
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    have hj' := Finset.mem_range.mp hj
    norm_cast
    omega
  have h := separated_polynomial_bound samples t s (fun n => b n.toNat)
    hJpos hδ hδ1 hpoints hsep hf
  have hp (x : ℝ) : polynomial s (fun n => b n.toNat) x =
      ∑ j ∈ Finset.range J, b j * monomial (j : ℤ) x := by
    rw [polynomial, Finset.sum_image hinj.injOn]
    simp
  have he : (∑ n ∈ s, ‖b n.toNat‖ ^ 2) = ∑ j ∈ Finset.range J, ‖b j‖ ^ 2 := by
    rw [Finset.sum_image hinj.injOn]
    simp
  simp_rw [hp] at h
  rw [he] at h
  simpa only [shifted_sum_norm] using h

theorem additive_large_sieve (Q J : ℕ) (M : ℤ) (b : ℤ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      ‖∑ j ∈ Finset.range J, b (M + (j : ℤ)) *
        exponential ((((M + (j : ℤ) : ℤ) : ℝ) * a) / q)‖ ^ 2) ≤
      (4 + 8 * Real.pi ^ 2) * ((J : ℝ) + (Q : ℝ) ^ 2) *
        ∑ j ∈ Finset.range J, ‖b (M + (j : ℤ))‖ ^ 2 := by
  by_cases hQ : Q = 0
  · simp only [hQ, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    positivity
  have hQpos : 0 < Q := by omega
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
  have hdelta : 0 < ((Q : ℝ) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hQreal)
  have hdelta1 : ((Q : ℝ) ^ 2)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (sq_pos_of_pos hQreal)).2
    nlinarith
  have h := separated_consecutive_bound (reducedFractions Q) fractionValue J M
    (fun j => b (M + (j : ℤ))) hdelta hdelta1
    (fun _ hz => ⟨(fractionValue_mem hz).1, (fractionValue_mem hz).2.le⟩)
    (fun _ hx _ hy hne => reduced_fraction_separation hQpos hx hy hne)
  rw [sum_reducedFractions] at h
  simpa only [fractionValue, inv_inv, mul_div_assoc] using h

end AdditiveLargeSieve

end

section

open scoped ComplexConjugate
namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

noncomputable def residueCount (N : ℕ) (S : Finset ℤ) (e : ZMod N) : ℕ :=
  (integerFibre N S e).card

noncomputable def spectrum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) : ℂ :=
  integerWeight N S (-a)

theorem spectrum_eq_sum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    spectrum N S a = ∑ x ∈ S,ZMod.stdAddChar (a*(x : ZMod N)) := by
  simp only [spectrum,integerWeight,neg_neg]

theorem spectrum_zero (N : ℕ) [NeZero N] (S : Finset ℤ) : spectrum N S 0 = (S.card : ℂ) := by
  simp [spectrum,integerWeight]

theorem spectrum_orthogonality (N : ℕ) [NeZero N] (S : Finset ℤ) (e : ZMod N) :
    (∑ a : ZMod N,spectrum N S a*ZMod.stdAddChar (-a*e)) = (N : ℂ)*(residueCount N S e : ℂ) := by
  have he : (∑ a : ZMod N,integerWeight N S (-a)*ZMod.stdAddChar ((-a)*e)) =
      ∑ a : ZMod N,integerWeight N S a*ZMod.stdAddChar (a*e) :=
    Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)
  exact he.trans (integerWeight_orthogonality N S e)

theorem conjugate_spectrum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    conj (spectrum N S a) = ∑ x ∈ S,ZMod.stdAddChar (-a*(x : ZMod N)) := by
  rw [spectrum_eq_sum,map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  ring

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

theorem residue_weighted_sum {R : Type*} [CommSemiring R] (N : ℕ) [NeZero N]
    (S : Finset ℤ) (f : ZMod N → R) :
    (∑ e : ZMod N,f e*(residueCount N S e : R)) = ∑ x ∈ S,f (x : ZMod N) := by
  calc
    _ = ∑ e : ZMod N,∑ _x ∈ integerFibre N S e,f e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [residueCount,mul_comm]
    _ = ∑ e : ZMod N,∑ x ∈ S,if (x : ZMod N) = e then f e else 0 := by
      simp only [integerFibre,Finset.sum_filter]
    _ = ∑ x ∈ S,∑ e : ZMod N,if (x : ZMod N) = e then f e else 0 := Finset.sum_comm
    _ = _ := by simp

theorem residue_count_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ e : ZMod N,residueCount N S e) = S.card := by
  have hh := residue_weighted_sum (R := ℕ) N S (fun _ => 1)
  simpa only [Nat.cast_id,one_mul,Finset.sum_const,nsmul_eq_mul,mul_one] using hh

theorem residue_square_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ x ∈ S,residueCount N S (x : ZMod N)) = ∑ e : ZMod N,(residueCount N S e)^2 := by
  simpa only [Nat.cast_id,pow_two] using (residue_weighted_sum (R := ℕ) N S (residueCount N S)).symm

end ErdosInverseSpectrum

end

section

open scoped ComplexConjugate
namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem spectrum_conjugate_sum (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ a : ZMod N,spectrum N S a*conj (spectrum N S a)) =
      (N : ℂ)*∑ e : ZMod N,(residueCount N S e : ℂ)^2 := by
  have hf : (∑ x ∈ S,(residueCount N S (x : ZMod N) : ℂ)) =
      ∑ e : ZMod N,(residueCount N S e : ℂ)^2 := by
    exact_mod_cast residue_square_sum N S
  calc
    _ = ∑ a : ZMod N,∑ x ∈ S,spectrum N S a*ZMod.stdAddChar (-a*(x : ZMod N)) := by
      simp_rw [conjugate_spectrum,Finset.mul_sum]
    _ = ∑ x ∈ S,∑ a : ZMod N,spectrum N S a*ZMod.stdAddChar (-a*(x : ZMod N)) := Finset.sum_comm
    _ = ∑ x ∈ S,(N : ℂ)*(residueCount N S (x : ZMod N) : ℂ) :=
      Finset.sum_congr rfl (fun x _ => spectrum_orthogonality N S (x : ZMod N))
    _ = (N : ℂ)*(∑ x ∈ S,(residueCount N S (x : ZMod N) : ℂ)) := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [hf]

theorem spectrum_parseval (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ a : ZMod N,‖spectrum N S a‖^2) = (N : ℝ)*∑ e : ZMod N,(residueCount N S e : ℝ)^2 := by
  have hh := spectrum_conjugate_sum N S
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at hh
  exact_mod_cast hh

theorem centered_residue_variance (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod N)),‖spectrum N S a‖^2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsum : (∑ e : ZMod N,(residueCount N S e : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast residue_count_sum N S
  have hcenter : (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      (N : ℝ)*(∑ e : ZMod N,(residueCount N S e : ℝ)^2)-(S.card : ℝ)^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hcross : (∑ e : ZMod N,2*(residueCount N S e : ℝ)*((S.card : ℝ)/(N : ℝ))) =
        2*(S.card : ℝ)*((S.card : ℝ)/(N : ℝ)) := by
      rw [← Finset.sum_mul,← Finset.mul_sum,hsum]
    rw [hcross]
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    field_simp
    ring
  have hzero : ‖spectrum N S (0 : ZMod N)‖^2 = (S.card : ℝ)^2 := by
    rw [spectrum_zero]
    norm_num
  have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun a => ‖spectrum N S a‖^2) (Finset.mem_univ (0 : ZMod N))
  rw [hzero,spectrum_parseval] at he
  rw [hcenter]
  linarith

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

noncomputable def exponentialSum (S : Finset ℤ) (a q : ℕ) : ℂ :=
  ∑ x ∈ S,AdditiveLargeSieve.exponential (((x : ℝ)*(a : ℝ))/(q : ℝ))

theorem spectrum_eq_exponentialSum (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ℕ) :
    spectrum N S (a : ZMod N) = exponentialSum S a N := by
  rw [spectrum_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have he : (a : ZMod N)*(x : ZMod N) = (((a : ℤ)*x : ℤ) : ZMod N) := by
    simp only [Int.cast_mul,Int.cast_natCast]
  rw [he,ZMod.stdAddChar_coe]
  unfold AdditiveLargeSieve.exponential
  congr 1
  push_cast
  ring

theorem spectrum_eq_exponentialSum_val (N : ℕ) [NeZero N] (S : Finset ℤ) (a : ZMod N) :
    spectrum N S a = exponentialSum S a.val N := by
  simpa only [ZMod.natCast_zmod_val] using spectrum_eq_exponentialSum N S a.val

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem residue_values_univ (N : ℕ) [NeZero N] :
    (Finset.univ : Finset (ZMod N)).image ZMod.val = Finset.range N := by
  ext a
  constructor
  · intro ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (ZMod.val_lt r)
  · intro ha
    exact Finset.mem_image.mpr ⟨(a : ZMod N),Finset.mem_univ _,ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)⟩

theorem sum_over_residues (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ e : ZMod N,f e.val) = ∑ e ∈ Finset.range N,f e := by
  rw [← residue_values_univ N,Finset.sum_image]
  intro a ha b hb hab
  exact ZMod.val_injective N hab

theorem residue_values_nonzero (N : ℕ) [NeZero N] :
    ((Finset.univ : Finset (ZMod N)).erase 0).image ZMod.val = (Finset.range N).erase 0 := by
  ext a
  constructor
  · intro ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hr0,hrU⟩ := Finset.mem_erase.mp hr
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_range.mpr (ZMod.val_lt r)⟩
    intro hz
    apply hr0
    apply ZMod.val_injective N
    simpa only [ZMod.val_zero] using hz
  · intro ha
    obtain ⟨ha0,haN⟩ := Finset.mem_erase.mp ha
    have haval := ZMod.val_natCast_of_lt (Finset.mem_range.mp haN)
    have har : (a : ZMod N) ≠ 0 := by
      intro hh
      have hval := congrArg ZMod.val hh
      rw [haval,ZMod.val_zero] at hval
      exact ha0 hval
    exact Finset.mem_image.mpr ⟨(a : ZMod N),Finset.mem_erase.mpr ⟨har,Finset.mem_univ _⟩,haval⟩

theorem sum_over_nonzero_residues (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ e ∈ (Finset.univ.erase (0 : ZMod N)),f e.val) = ∑ e ∈ (Finset.range N).erase 0,f e := by
  rw [← residue_values_nonzero N,Finset.sum_image]
  intro a ha b hb hab
  exact ZMod.val_injective N hab

theorem centered_variance_exponential (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*(∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) =
      ∑ a ∈ (Finset.range N).erase 0,‖exponentialSum S a N‖^2 := by
  rw [centered_residue_variance]
  simp_rw [spectrum_eq_exponentialSum_val]
  exact sum_over_nonzero_residues N (fun a => ‖exponentialSum S a N‖^2)

end ErdosInverseSpectrum

end

section

namespace ErdosInverseSpectrum
open ErdosHyperbolaIdentities
attribute [local instance] Classical.decEq

noncomputable def integerResidueCount (N : ℕ) (S : Finset ℤ) (e : ℕ) : ℕ :=
  (S.filter (fun x => x % (N : ℤ) = (e : ℤ))).card

noncomputable def integerResidueVariance (N : ℕ) (S : Finset ℤ) : ℝ :=
  ∑ e ∈ Finset.range N,((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2

theorem residueCount_at_val (N : ℕ) [NeZero N] (S : Finset ℤ) (e : ZMod N) :
    residueCount N S e = integerResidueCount N S e.val := by
  unfold residueCount integerResidueCount
  congr 1
  ext x
  simp only [integerFibre,Finset.mem_filter]
  apply and_congr_right
  intro _hx
  rw [← ZMod.val_intCast x]
  constructor
  · intro he
    rw [he]
  · intro he
    exact ZMod.val_injective N (Int.ofNat_inj.mp he)

theorem variance_eq_integerResidueVariance (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (∑ e : ZMod N,((residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2) = integerResidueVariance N S := by
  simp_rw [residueCount_at_val]
  exact sum_over_residues N (fun e => ((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2)

theorem integer_variance_fourier (N : ℕ) [NeZero N] (S : Finset ℤ) :
    (N : ℝ)*integerResidueVariance N S = ∑ a ∈ (Finset.range N).erase 0,‖exponentialSum S a N‖^2 := by
  rw [← variance_eq_integerResidueVariance]
  exact centered_variance_exponential N S

end ErdosInverseSpectrum

end

end Erdos970

end OAI
