import Mathlib
import OAI.Probability.SKGap.Matrix.NormalizedPrimaryRecipe
import OAI.Probability.SKGap.Localization.WeakResidual

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

def starSquared (P : Spin n→ℝ) (f : Observables n) : ℝ :=
  (∑ x,P x*(f x)^2)+varianceEnergy P f

def starNorm (P : Spin n→ℝ) (f : Observables n) : ℝ := Real.sqrt (starSquared P f)

lemma starSquared_nonneg (P : Spin n→ℝ) (hP : ∀x,0≤P x) (f : Observables n) :
    0≤ starSquared P f := add_nonneg (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))
      (varianceEnergy_nonneg P hP f)

lemma halfDiff_mul_flipped (i : Fin n) (θ G : Observables n) (x : Spin n) :
    halfDiff i (fun y=>θ y*G y) x=θ (flip x i)*halfDiff i G x+G x*halfDiff i θ x := by
  rw [halfDiff_mul]
  have h:=flip_sub i θ x
  rw [show θ (flip x i)=θ x-2*spin x i*halfDiff i θ x by linarith]
  ring

lemma multiplier_energy (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    varianceEnergy P (fun x=>θ x*G x)≤
      2*B^2*varianceEnergy P G+2*L^2*(∑x,P x*(G x)^2) := by
  have ht (x : Spin n) (i : Fin n) : (θ (flip x i))^2≤B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (hθ (flip x i))
  calc
    _ ≤ ∑x,P x*∑i,conditionalVariance P x i*
        (2*B^2*(halfDiff i G x)^2+2*(G x)^2*(halfDiff i θ x)^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply Finset.sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (conditionalVariance_nonneg P hP x i)
      rw [halfDiff_mul_flipped]
      have hh:=mul_le_mul_of_nonneg_right (ht x i) (sq_nonneg (halfDiff i G x))
      nlinarith only [hh,sq_nonneg (θ (flip x i)*halfDiff i G x-G x*halfDiff i θ x)]
    _ ≤ ∑x,P x*(2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2)+2*(G x)^2*L^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      simp only [mul_add,Finset.sum_add_distrib]
      have h1 : (∑i,conditionalVariance P x i*(2*B^2*(halfDiff i G x)^2))=
          2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h1]
      apply add_le_add_right
      calc
        _ ≤ ∑i,2*(G x)^2*(halfDiff i θ x)^2 := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_of_le_one_left (by positivity) (conditionalVariance_le_one P x i)
        _ = 2*(G x)^2*(∑i,(halfDiff i θ x)^2) := by rw [Finset.mul_sum]
        _ ≤ _ := by
          simpa only [mul_comm (2*(G x)^2)] using
            mul_le_mul (hd x) (le_refl (2*(G x)^2)) (by positivity) (pow_nonneg hL 2)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,varianceEnergy,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring_nf

lemma multiplier_starSquared (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    starSquared P (fun x=>θ x*G x)≤(3*B^2+2*L^2)*starSquared P G := by
  have hs : (∑x,P x*(θ x*G x)^2)≤B^2*(∑x,P x*(G x)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    have ht : (θ x)^2≤B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ x) 2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ht (sq_nonneg (G x))) (hP x)]
  have he:=multiplier_energy P hP θ G hB hL hθ hd
  have hn:=varianceEnergy_nonneg P hP G
  have hn' : 0≤∑x,P x*(G x)^2 := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  dsimp only [starSquared]
  nlinarith [mul_nonneg (sq_nonneg B) hn,mul_nonneg (sq_nonneg L) hn,
    mul_nonneg (sq_nonneg B) hn']

lemma star_multiplier (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (θ G : Observables n) {B L : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hθ : ∀x,|θ x|≤B)
    (hd : ∀x,∑i,(halfDiff i θ x)^2≤L^2) :
    starNorm P (fun x=>θ x*G x)≤Real.sqrt (3*B^2+2*L^2)*starNorm P G := by
  exact (Real.sqrt_le_sqrt (multiplier_starSquared P hP θ G hB hL hθ hd)).trans_eq
    (Real.sqrt_mul (by positivity) _)

lemma expected_abs_le_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (hPsum : ∑x,P x=1)
    (G : Observables n) : (∑x,P x*|G x|)≤ starNorm P G := by
  have hc:=weighted_cauchy_sq P (fun x=>|G x|) (fun _=>1) hP
  simp only [mul_one,one_pow,sq_abs,hPsum] at hc
  have hn : 0≤∑x,P x*|G x| := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (abs_nonneg _)
  apply (sq_le_sq₀ hn (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (starSquared_nonneg P hP G)]
  exact hc.trans (le_add_of_nonneg_right (varianceEnergy_nonneg P hP G))

lemma sqrt_energy_le_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (G : Observables n) :
    Real.sqrt (varianceEnergy P G)≤ starNorm P G := by
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))

theorem signed_base_star (P : Spin n→ℝ) (hP : ∀x,0≤P x) (hPsum : ∑x,P x=1)
    (G : Observables n) (U : VectorFields n) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀x,∑i,|halfDiff i (fun y=>U y i) x|≤A) (hU : ∀x,∑i,(U x i)^2≤B^2) :
    |∑x,P x*G x*∑i,(spin x i-conditionalMean P x i)*U x i|≤(2*B+5*A)*starNorm P G := by
  have H:=signed_weak_residual_base P hP hPsum G U hA hB hD hU
  have h1:=mul_le_mul_of_nonneg_left (expected_abs_le_star P hP hPsum G) hA
  have h2:=mul_le_mul_of_nonneg_left (sqrt_energy_le_star P hP G) (show 0≤2*B+4*A by positivity)
  linarith

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def UniformMultiplier (θ : ∀a,Observables (n a)) : Prop :=
  ∃B L : ℝ,0≤B ∧ 0≤L ∧ (∀a x,|θ a x|≤B) ∧
    (∀a x,∑i,(halfDiff i (θ a) x)^2≤L^2)

def UniformWeak (P F : ∀a,Observables (n a)) : Prop :=
  ∃C : ℝ,0≤C ∧ ∀a G,|∑x,P a x*G x*F a x|≤C*starNorm (P a) G

lemma UniformWeak.zero (P : ∀a,Observables (n a)) : UniformWeak P (fun _ _=>0) := by
  refine ⟨0,le_rfl,?_⟩
  simp

lemma UniformWeak.congr {P F F' : ∀a,Observables (n a)} (h : UniformWeak P F)
    (he : ∀a x,F a x=F' a x) : UniformWeak P F' := by
  have : F=F' := funext fun a=>funext (he a)
  rwa [←this]

lemma UniformWeak.add {P F H : ∀a,Observables (n a)} (hF : UniformWeak P F)
    (hH : UniformWeak P H) : UniformWeak P (fun a x=>F a x+H a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨D,hD,hH⟩:=hH
  refine ⟨C+D,add_nonneg hC hD,fun a G=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a G) (hH a G)).trans_eq (by ring))

lemma UniformWeak.neg {P F : ∀a,Observables (n a)} (hF : UniformWeak P F) :
    UniformWeak P (fun a x=>-F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  refine ⟨C,hC,fun a G=>?_⟩
  simpa using hF a G

lemma UniformWeak.sub {P F H : ∀a,Observables (n a)} (hF : UniformWeak P F)
    (hH : UniformWeak P H) : UniformWeak P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg

lemma UniformWeak.sum {τ : Type*} [Fintype τ] {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (h : ∀t,UniformWeak P (F t)) :
    UniformWeak P (fun a x=>∑t,F t a x) := by
  classical
  choose C hC hb using h
  refine ⟨∑t,C t,Finset.sum_nonneg (fun t _=>hC t),fun a G=>?_⟩
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun t _=>hb t a G).trans_eq (Finset.sum_mul ..).symm)

lemma UniformWeak.mul {P F θ : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformWeak P F) (hθ : UniformMultiplier θ) :
    UniformWeak P (fun a x=>θ a x*F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨B,L,hB,hL,hθ,hd⟩:=hθ
  refine ⟨C*Real.sqrt (3*B^2+2*L^2),by positivity,fun a G=>?_⟩
  have hf:=hF a (fun x=>θ a x*G x)
  have hm:=mul_le_mul_of_nonneg_left (star_multiplier (P a) (hP a) (θ a) G hB hL (hθ a) (hd a)) hC
  calc
    _ = |∑x,P a x*(θ a x*G x)*F a x| := by
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ C*(Real.sqrt (3*B^2+2*L^2)*starNorm (P a) G) := hf.trans hm
    _ = _ := by ring

lemma UniformMultiplier.const (c : ℝ) : UniformMultiplier (n:=n) (fun _ _=>c) := by
  refine ⟨|c|,0,abs_nonneg _,le_rfl,fun _ _=>le_rfl,?_⟩
  intro a x
  simp [halfDiff]

lemma UniformWeak.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformWeak P F) (c : ℝ) : UniformWeak P (fun a x=>c*F a x) :=
  hF.mul hP (UniformMultiplier.const c)

lemma UniformWeak.base (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hp : ∀a,∑x,P a x=1) (U : ∀a,VectorFields (n a))
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀a x,∑i,|halfDiff i (fun y=>U a y i) x|≤A)
    (hU : ∀a x,vectorNorm (U a x)≤B) :
    UniformWeak P (fun a x=>∑i,(spin x i-conditionalMean (P a) x i)*U a x i) := by
  refine ⟨2*B+5*A,by positivity,fun a G=>?_⟩
  apply signed_base_star (P a) (hP a) (hp a) G (U a) hA hB (hD a)
  intro x
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) (hU a x) 2

lemma UniformMultiplier.normedMean (hn : ∀a,0<n a) (U : ∀a,VectorFields (n a))
    {B : ℝ} (hB : 0≤B) (hU : ∀a x,SmallBound (U a) x B) :
    UniformMultiplier (fun a x=>Real.sqrt (n a:ℝ)*siteMean (U a) x) := by
  refine ⟨B,B,hB,hB,fun a x=>scaledMean_size (hn a) _ _ hB (hU a x).size,
    fun a x=>scaledMean_difference (hn a) _ _ hB (hU a x).derivative⟩

end SKGapCutoff.Static

end
end

end OAI
