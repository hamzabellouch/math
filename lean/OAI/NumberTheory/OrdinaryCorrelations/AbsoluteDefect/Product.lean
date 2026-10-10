import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TwistNormLe

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

namespace OrdinaryCorrelations.CharacterStability
open Classical

def product {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    DirichletCharacter ℂ (q*r) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_right q r) χ *
    DirichletCharacter.changeLevel (Nat.dvd_mul_left r q) ψ

lemma change_value {q r : ℕ} (χ : DirichletCharacter ℂ q) (hqr : q ∣ r)
    {n : ℕ} (hn : n.Coprime r) :
    (DirichletCharacter.changeLevel hqr χ) (n : ZMod r) = χ (n : ZMod q) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hqr (ZMod.unitOfCoprime n hn)
  simpa only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast hqr] using h

lemma product_apply {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    product χ ψ (n : ZMod (q*r)) = χ (n : ZMod q) * ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [product,MulChar.mul_apply,
      change_value χ _ hn,change_value ψ _ hn]
  · have hzero : product χ ψ (n : ZMod (q*r)) = 0 := by
      exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)
    rw [hzero]
    rw [Nat.coprime_mul_iff_right] at hn
    rcases not_and_or.mp hn with hq | hr
    · rw [MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using hq),zero_mul]
    · rw [MulChar.map_nonunit ψ (by simpa only [ZMod.isUnit_iff_coprime] using hr),mul_zero]

lemma twist_bounded {r : ℕ} (ψ : DirichletCharacter ℂ r)
    {f : ℕ → ℂ} (hf : OneBounded f) :
    OneBounded (fun n => f n * ψ (n : ZMod r)) := by
  intro n
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (ψ.norm_le_one _)

lemma twist_multiplicative {r : ℕ} (ψ : DirichletCharacter ℂ r)
    {f : ℕ → ℂ} (hf : Multiplicative f) :
    Multiplicative (fun n => f n * ψ (n : ZMod r)) := by
  intro m n hm hn hmn
  dsimp only
  rw [hf m n hm hn hmn,Nat.cast_mul,map_mul]
  ring

theorem twist_distanceSq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (f : ℕ → ℂ) (t X : ℝ) :
    distanceSq (fun n => f n * ψ (n : ZMod r)) χ t X =
      distanceSq f (product χ (star ψ)) t X := by
  unfold distanceSq
  apply Finset.sum_congr rfl
  intro p _
  rw [product_apply,MulChar.star_apply]
  congr 2
  simp only [star_mul,star_star]
  ring_nf

theorem twist_nonpretentious {r : ℕ} (hr : 0 < r) (ψ : DirichletCharacter ℂ r)
    {f : ℕ → ℂ} (hnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (fun n => f n * ψ (n : ZMod r)) := by
  intro q hq χ
  simpa only [distance,twist_distanceSq] using hnp (q*r) (Nat.mul_pos hq hr)
    (product χ (star ψ))

lemma exp_neg_conj (x : ℝ) :
    Complex.exp (-((x:ℂ) * Complex.I)) = star (Complex.exp ((x:ℂ) * Complex.I)) := by
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem conjugate_distanceSq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ → ℂ) (t X : ℝ) :
    distanceSq (fun n => star (f n)) χ t X =
      distanceSq f (star χ) (-t) X := by
  unfold distanceSq
  apply Finset.sum_congr rfl
  intro p _
  simp only [MulChar.star_apply,neg_mul,Complex.ofReal_neg]
  rw [exp_neg_conj]
  simp only [star_mul,star_star]
  congr 2
  calc
    _ = (star (f p * (χ (p : ZMod q) *
        Complex.exp ((t*Real.log (p:ℝ):ℝ)*Complex.I)))).re := by
      congr 1
      simp only [star_mul]
      ring
    _ = _ := by simp [mul_comm]; ring

theorem conjugate_nonpretentious {f : ℕ → ℂ} (hnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (fun n => star (f n)) := by
  intro q hq χ
  have he (N : ℕ) :
      (fun t : ℝ => distance (fun n => star (f n)) χ t (N:ℝ)) ''
        Set.Icc (-(N:ℝ)) (N:ℝ) =
      (fun t : ℝ => distance f (star χ) t (N:ℝ)) '' Set.Icc (-(N:ℝ)) (N:ℝ) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
      simp only [distance,conjugate_distanceSq]
    · rintro ⟨t,ht,rfl⟩
      refine ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
      simp only [distance,conjugate_distanceSq,neg_neg]
  simpa only [he] using hnp q hq (star χ)

theorem finite_twist_distanceSq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (f G : ℕ → ℂ) (hf : OneBounded f)
    (hG : OneBounded G) (S : Finset ℕ)
    (hag : ∀ p, p.Prime → p ∉ S → G p = f p * ψ (p:ZMod r)) (t X : ℝ) :
    |distanceSq G χ t X - distanceSq f (product χ (star ψ)) t X| ≤
      ∑ p ∈ S, 2/(p:ℝ) := by
  rw [← twist_distanceSq]
  apply PretentiousStability.distanceSq_change _ G (twist_bounded ψ hf) hG S
  intro p hp hn
  exact (hag p hp hn).symm

theorem finite_twist_nonpretentious {r : ℕ} (hr : 0 < r)
    (ψ : DirichletCharacter ℂ r) (f G : ℕ → ℂ) (hf : OneBounded f)
    (hG : OneBounded G) (S : Finset ℕ)
    (hag : ∀ p, p.Prime → p ∉ S → G p = f p * ψ (p:ZMod r))
    (hnp : UniformlyNonpretentious f) : UniformlyNonpretentious G := by
  apply PretentiousStability.uniformlyNonpretentious_change _ G (twist_bounded ψ hf)
    hG S _ (twist_nonpretentious hr ψ hnp)
  intro p hp hn
  exact (hag p hp hn).symm

end OrdinaryCorrelations.CharacterStability

end

end OAI
