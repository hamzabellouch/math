import Mathlib
import OAI.Probability.SKGap.Localization.PrimaryLocalInput

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_residual_rule (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
    (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
    (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
    ∀p≤pmax,RecipeResidualRule j J h P M Nmax p (b p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih=>
    intro hpmax
    cases p with
    | zero=>exact residual_rule_base C hP hp hm (b 0) (hA 0 hpmax)
    | succ k=>
      exact residual_rule_step C hP hn hJ b hmono k (hpmax.trans_lt hM)
        (hA k (by omega)) (h2 k (by omega)) (hstep k (by omega))
        (fun r hr=>ih r hr (by omega))

def residualCoefficientBudget (j K : ℝ) (t p : ℕ) : ℝ :=
  K*(1+4*steinCoefficientBudget |j|)^(t-p)
lemma residualCoefficientBudget_antitone (j : ℝ) {K : ℝ} (hK : 0≤K) (t : ℕ) :
    Antitone (residualCoefficientBudget j K t) := by
  intro p q hpq
  apply mul_le_mul_of_nonneg_left _ hK
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) (Nat.sub_le_sub_left hpq t)
lemma residualCoefficientBudget_ge (j : ℝ) {K : ℝ} (hK : 0≤K) (t p : ℕ) :
    K≤residualCoefficientBudget j K t p := by
  simpa only [mul_one,residualCoefficientBudget] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ (by linarith [steinCoefficientBudget_nonneg |j|]) :
      1≤(1+4*steinCoefficientBudget |j|)^(t-p)) hK
lemma residualCoefficientBudget_step (j K : ℝ) {t k : ℕ} (hk : k<t) :
    residualCoefficientBudget j K t (k+1)+4*steinCoefficientBudget |j| *residualCoefficientBudget j K t (k+1)=
      residualCoefficientBudget j K t k := by
  have he : t-k=(t-(k+1))+1 := by omega
  dsimp only [residualCoefficientBudget]
  rw [he,pow_succ]
  ring

theorem uniform_ordinary_weak_residual (p N : ℕ) {K : ℝ} (hK : 2≤K) (hM : p<M)
    (C : FiniteRecipeControl j J h M (N+2*p) (residualCoefficientBudget j K p 0))
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformWeak P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hK0 : 0≤K := by linarith
  have hb:=residualCoefficientBudget_antitone j hK0 p
  have HH:=uniform_residual_rule C hP hp hm hn hJ (residualCoefficientBudget j K p) hb p hM
    (fun r _=>hb (Nat.zero_le r)) (fun r _=>hK.trans (residualCoefficientBudget_ge j hK0 p r))
    (fun k hk=>le_of_eq (residualCoefficientBudget_step j K hk)) p le_rfl D N
  apply HH _ le_rfl
  simpa [residualCoefficientBudget] using H

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def UniformSquare (P F : ∀a,Observables (n a)) : Prop :=
  ∀B L:ℝ,0≤B→0≤L→∃C:ℝ,0≤C ∧ ∀a (f θ : Observables (n a)),
    (∀x,|θ x|≤B)→(∀x,∑i,(halfDiff i θ x)^2≤L^2)→
    |∑x,P a x*(f x)^2*θ x*F a x|≤C*starSquared (P a) f

lemma UniformSquare.zero (P : ∀a,Observables (n a)) : UniformSquare P (fun _ _=>0) := by
  intro B L hB hL
  exact ⟨0,le_rfl,by simp⟩
lemma UniformSquare.congr {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (he : ∀a x,F a x=H a x) : UniformSquare P H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma UniformSquare.add {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (hH : UniformSquare P H) : UniformSquare P (fun a x=>F a x+H a x) := by
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF B L hB hL
  obtain ⟨D,hD,hH⟩:=hH B L hB hL
  refine ⟨C+D,add_nonneg hC hD,fun a f θ ht hd=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a f θ ht hd) (hH a f θ ht hd)).trans_eq (by ring))
lemma UniformSquare.neg {P F : ∀a,Observables (n a)} (hF : UniformSquare P F) :
    UniformSquare P (fun a x=>-F a x) := by
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF B L hB hL
  refine ⟨C,hC,fun a f θ ht hd=>?_⟩
  simpa using hF a f θ ht hd
lemma UniformSquare.sub {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (hH : UniformSquare P H) : UniformSquare P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg
lemma UniformSquare.sum {τ : Type*} [Fintype τ] {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (h : ∀t,UniformSquare P (F t)) :
    UniformSquare P (fun a x=>∑t,F t a x) := by
  classical
  intro B L hB hL
  choose C hC hb using (fun t=>h t B L hB hL)
  refine ⟨∑t,C t,Finset.sum_nonneg (fun t _=>hC t),fun a f θ ht hd=>?_⟩
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun t _=>hb t a f θ ht hd).trans_eq (Finset.sum_mul ..).symm)

lemma scalar_product_bounds {n : ℕ} (θ η : Observables n) {B L D K : ℝ}
    (hB : 0≤B) (_ : 0≤L) (_ : 0≤D) (_ : 0≤K)
    (ht : ∀x,|θ x|≤B) (hdt : ∀x,∑i,(halfDiff i θ x)^2≤L^2)
    (he : ∀x,|η x|≤D) (hde : ∀x,∑i,(halfDiff i η x)^2≤K^2) :
    (∀x,|θ x*η x|≤B*D) ∧
    (∀x,∑i,(halfDiff i (fun y=>θ y*η y) x)^2≤(Real.sqrt (2*B^2*K^2+2*D^2*L^2))^2) := by
  constructor
  · intro x; rw [abs_mul]; exact mul_le_mul (ht x) (he x) (abs_nonneg _) hB
  · intro x
    rw [Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ∑i,(2*B^2*(halfDiff i η x)^2+2*D^2*(halfDiff i θ x)^2) := by
        apply Finset.sum_le_sum; intro i _
        rw [halfDiff_mul_flipped]
        have h1 : (θ (flip x i))^2≤B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ht (flip x i)) 2
        have h2 : (η x)^2≤D^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he x) 2
        have h1':=mul_le_mul_of_nonneg_right h1 (sq_nonneg (halfDiff i η x))
        have h2':=mul_le_mul_of_nonneg_right h2 (sq_nonneg (halfDiff i θ x))
        nlinarith only [h1',h2',sq_nonneg (θ (flip x i)*halfDiff i η x-η x*halfDiff i θ x)]
      _ = 2*B^2*(∑i,(halfDiff i η x)^2)+2*D^2*(∑i,(halfDiff i θ x)^2) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hde x) (by positivity))
        (mul_le_mul_of_nonneg_left (hdt x) (by positivity))

lemma UniformSquare.mul {P F η : ∀a,Observables (n a)} (_ : ∀a x,0≤P a x)
    (hF : UniformSquare P F) (hη : UniformMultiplier η) :
    UniformSquare P (fun a x=>η a x*F a x) := by
  obtain ⟨D,K,hD,hK,he,hde⟩:=hη
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF (B*D) (Real.sqrt (2*B^2*K^2+2*D^2*L^2))
    (mul_nonneg hB hD) (Real.sqrt_nonneg _)
  refine ⟨C,hC,fun a f θ ht hd=>?_⟩
  obtain ⟨h1,h2⟩:=scalar_product_bounds θ (η a) hB hL hD hK ht hd (he a) (hde a)
  convert hF a f (fun x=>θ x*η a x) h1 h2 using 1
  congr 1
  apply Finset.sum_congr rfl; intro x _; ring
lemma UniformSquare.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : UniformSquare P F) (c : ℝ) : UniformSquare P (fun a x=>c*F a x) :=
  hF.mul hP (UniformMultiplier.const c)

lemma UniformSquare.base (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (U : ∀a,VectorFields (n a)) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀a x,∑i,|halfDiff i (fun y=>U a y i) x|≤A)
    (hU : ∀a x,vectorNorm (U a x)≤B) :
    UniformSquare P (fun a x=>∑i,(spin x i-conditionalMean (P a) x i)*U a x i) := by
  intro H L hH hL
  refine ⟨13*(H*A+(2*B+4*A)*L)+6*(H*B),by positivity,fun a f θ ht hd=>?_⟩
  apply square_multiplier_weak_residual_base (P a) (hP a) f θ (U a) hA hB hH hL (hD a) _ ht hd
  intro x
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) (hU a x) 2

end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
lemma uniform_square_normalized_pair (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hn : ∀a,0<n a) (R U V : ∀a,VectorFields (n a))
    (hV : UniformSquare P (fun a x=>∑i,R a x i*(V a x i/Real.sqrt (n a:ℝ))))
    {C : ℝ} (hC : 0≤C) (hU : ∀a x,SmallBound (U a) x C) :
    UniformSquare P (fun a x=>siteMean (U a) x*(∑i,R a x i*V a x i)) := by
  exact (hV.mul hP (UniformMultiplier.normedMean hn U hC hU)).congr
    (fun a x=>normalized_pair_cancel (hn a) (R a) (V a) (siteMean (U a)) x)
lemma uniform_square_prev_zero (P : ∀a,Observables (n a)) (U : ∀a,VectorFields (n a)) :
    UniformSquare P (fun a x=>∑i,previousResidual j (J a) (h a) 0 x i*U a x i) := by
  convert UniformSquare.zero P using 1
  ext a x
  simp [previousResidual]
end SKGapCutoff.Recipe

end
end

end OAI
