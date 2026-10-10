import OAI.NumberTheory.DirichletL.Detector.RaySlots
import OAI.NumberTheory.DirichletL.Hecke.PrimeRow

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
local notation "Id" => Ideal HeckeFamily.O

lemma pool_sum_complex (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℂ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · intro P hP;exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he;exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP;rfl

theorem weighted_pool_eq_annular (C : Set Id) (S : Finset Id)
    (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (_hab : a≤b) (hD : 0<D)
    (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (g : Id→ℂ) :
    (∑P∈pool C S a b D,W ((P.val.absNorm:ℝ)/D)*g P.val)=
      ∑P∈(HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C),
        W ((P.absNorm:ℝ)/D)*g P := by
  rw [pool_sum_complex C S a b D (fun P=>W ((P.absNorm:ℝ)/D)*g P)]
  have hsub : annularPrimeIdeals C a b D\S⊆
      (HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C) := by
    intro P hP
    have hp := (mem_annularPrimeIdeals C a b D P).mp (Finset.mem_sdiff.mp hP).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,hp.2.1,hp.1⟩
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    refine ⟨Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1.ne_zero),?_⟩
    apply hp.2.2.2.trans
    apply Nat.floor_mono
    nlinarith [le_max_right (1:ℝ) b]
  apply Finset.sum_subset hsub
  intro P hP hnot
  have hw : W ((P.absNorm:ℝ)/D)=0 := by
    by_contra hn
    have hy := hW hn
    have hp := (Finset.mem_filter.mp hP).2
    apply hnot
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_annularPrimeIdeals C a b D P).mpr
      refine ⟨hp.2,hp.1,?_,?_⟩
      · apply (Nat.floor_lt (mul_nonneg hD.le ha.le)).mpr
        have := (lt_div_iff₀ hD).mp hy.1
        nlinarith
      · apply Nat.le_floor
        have := (div_lt_iff₀ hD).mp hy.2
        nlinarith
    · intro hs
      have := hS P hs
      have := (lt_div_iff₀ hD).mp hy.1
      linarith
  simp only [hw,zero_mul]

theorem central_phase_eq_amplitude (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    (∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val)))=
      -(D:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z := by
  have he := weighted_pool_eq_annular (RayQuotient.identityClass M H) S W a b D ha hab hD hW hS
    (fun P=>(P.absNorm:ℂ)^(z-1)*(-star (CanonicalRowCompletion.idealRowHom u P)))
  simp_rw [mul_assoc] at ⊢
  rw [he]
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [←mul_assoc,neg_mul,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  have hexp : (z-(1/2:ℂ)) + -(1/2:ℂ)=z-1 := by ring
  rw [hexp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hprime := (Finset.mem_filter.mp hP).2.1
  have hn : (0:ℝ)<P.absNorm := by exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprime.ne_zero)
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hn.le hD.le]
  have hd : (D:ℂ)^(z-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  field_simp
  simp only [starRingEnd_apply,Complex.ofReal_natCast]
  ring

theorem central_phase_norm (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    ‖∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val))‖=
      D^(z.re-1/2)*‖HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z‖ := by
  rw [central_phase_eq_amplitude M H S u W a b D ha hab hD hW hS z,
    norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hD]
  norm_num

theorem power_fixed_exclusions (S : Finset Id) (a ellMin : ℝ) (ha : 0<a) (hmin : 0<ellMin)
    {ι : Type*} (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in Filter.atTop,∀j,∀P∈S,(P.absNorm:ℝ)≤a*Z^(ell j) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop ha
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (∑P∈S,(P.absNorm:ℝ))),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hnorm hZ j P hP
  calc
    (P.absNorm:ℝ) ≤ ∑Q∈S,(Q.absNorm:ℝ) := Finset.single_le_sum (fun Q _=>Nat.cast_nonneg _) hP
    _ ≤ a*Z^ellMin := hnorm
    _ ≤ a*Z^(ell j) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) ha.le

end SevenEighths.ProbeRaySlots
end

end OAI
