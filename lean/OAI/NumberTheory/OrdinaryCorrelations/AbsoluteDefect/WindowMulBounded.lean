import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Product
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Euler
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CharBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WindowSmall

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinarySharpWindow Finset Filter MeasureTheory
open OrdinaryCorrelations.LocalExpansion OrdinaryCorrelations.ResidueCharacters
lemma window_mul_bounded {f g : ℕ→ℂ} (hf : OneBounded f) (hg : OneBounded g) :
    OneBounded (fun n=>f n*g n) := by
  intro n
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg n)
lemma window_mul_multiplicative {f g : ℕ→ℂ} (hf : Multiplicative f) (hg : Multiplicative g) :
    Multiplicative (fun n=>f n*g n) := by
  intro m n hm hn hmn
  change f (m*n)*g (m*n)=f m*g m*(f n*g n)
  rw [hf m n hm hn hmn,hg m n hm hn hmn]
  ring

lemma dilated_character_windowSmall {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (χ : DirichletCharacter ℂ q) :
    WindowSmall (fun n=>f n*dilation d (fun k=>χ (k:ZMod q)) n) := by
  let F : Finset ℕ→ℕ→ℂ := fun E n=>f n*dilationSummand d (fun k=>χ (k:ZMod q)) E n
  have hFb (E : Finset ℕ) : OneBounded (F E) :=
    window_mul_bounded hf (dilationSummand_bounded d _ (char_bounded χ) E)
  have hFm (E : Finset ℕ) : Multiplicative (F E) :=
    window_mul_multiplicative hm (dilationSummand_multiplicative d _ E)
  have hFnp (E : Finset ℕ) : UniformlyNonpretentious (F E) := by
    apply CharacterStability.finite_twist_nonpretentious hq χ f (F E) hf (hFb E)
      d.primeFactors _ hNP
    intro p hp hpd
    dsimp only [F]
    have he := dilationSummand_primePow d (fun k=>χ (k:ZMod q)) (by simp) E hp hpd 1
    simp only [pow_one] at he
    rw [he]
  have hsmall (E : Finset ℕ) : WindowSmall (fun n=>(-1:ℂ)^E.card*F E n) :=
    windowSmall_const_mul _ (windowSmall_of_nonpretentious (hFb E) (hFm E) (hFnp E))
  have hs := windowSmall_finsetSum d.primeFactors.powerset _ (fun E _=>hsmall E)
  apply windowSmall_congr_pos _ hs
  intro n hn
  rw [dilation_expansion d hd _ (char_multiplicative χ) (by simp) hn,mul_sum]
  apply sum_congr rfl
  intro E hE
  dsimp only [F]
  ring

theorem residue_windowSmall {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {l : ℕ} (hl : 0 < l) (b : ℕ) :
    WindowSmall (fun n=>f n*(if n ≡ b [MOD l] then (1:ℂ) else 0)) := by
  let d := b.gcd l
  let q := l/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hl
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_right b l)) hd
  let a (χ : DirichletCharacter ℂ q) : ℂ := (q.totient:ℂ)⁻¹*star (χ ((b/d):ZMod q))
  let F (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := f n*dilation d (fun k=>χ (k:ZMod q)) n
  have hsmall (χ : DirichletCharacter ℂ q) : WindowSmall (fun n=>a χ*F χ n) :=
    windowSmall_const_mul _ (dilated_character_windowSmall hf hm hNP hd hq χ)
  have hs := windowSmall_finsetSum univ _ (fun χ _=>hsmall χ)
  apply windowSmall_congr_pos _ hs
  intro n hn
  rw [gcd_indicator l b n hl,mul_sum,mul_sum]
  apply sum_congr rfl
  intro χ hχ
  dsimp only [a,F,d,q]
  ring

lemma finite_residue_expansion (f w : ℕ→ℂ) {l : ℕ} (hl : 0 < l) (n : ℕ) :
    f n*w (n%l)=∑b∈range l,w b*(f n*(if n ≡ b [MOD l] then (1:ℂ) else 0)) := by
  classical
  rw [sum_eq_single (n%l)]
  · have he : n ≡ n%l [MOD l] := by show n%l=(n%l)%l; rw [Nat.mod_mod]
    rw [ite_eq_left he,mul_one,mul_comm]
  · intro b hb hbn
    have he : ¬n ≡ b [MOD l] := by
      intro he
      have heb : n%l=b := by simpa only [Nat.mod_eq_of_lt (mem_range.mp hb)] using (show n%l=b%l from he)
      exact hbn heb.symm
    rw [ite_eq_right he,mul_zero,mul_zero]
  · intro hn
    exact False.elim (hn (mem_range.mpr (Nat.mod_lt n hl)))

theorem periodic_windowSmall {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {l : ℕ} (hl : 0 < l) (w : ℕ→ℂ) : WindowSmall (fun n=>f n*w (n%l)) := by
  have hs := windowSmall_finsetSum (range l)
    (fun b n=>w b*(f n*(if n ≡ b [MOD l] then (1:ℂ) else 0)))
    (fun b hb=>windowSmall_const_mul (w b) (residue_windowSmall hf hm hNP hl b))
  apply windowSmall_congr_pos _ hs
  intro n hn
  exact (finite_residue_expansion f w hl n).symm

end OrdinaryChainScales

end

end OAI
