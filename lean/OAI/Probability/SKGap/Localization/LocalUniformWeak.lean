import Mathlib
import OAI.Probability.SKGap.Localization.StartedResidualStep

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def LocalUniformMultiplier (E : ∀a,Set (Spin (n a))) (θ : ∀a,Observables (n a)) : Prop :=
  ∃B L : ℝ,0≤B ∧ 0≤L ∧ (∀a x,x∈flipNeighborhood (E a)→|θ a x|≤B) ∧
    (∀a x,x∈E a→∑i,(halfDiff i (θ a) x)^2≤L^2)

def LocalUniformWeak (E : ∀a,Set (Spin (n a))) (P F : ∀a,Observables (n a)) : Prop :=
  ∃C : ℝ,0≤C ∧ ∀a G,(∀x,x∉E a→G x=0)→|∑x,P a x*G x*F a x|≤C*starNorm (P a) G

lemma LocalUniformWeak.zero (E : ∀a,Set (Spin (n a))) (P : ∀a,Observables (n a)) : LocalUniformWeak E P (fun _ _=>0) := by
  refine ⟨0,le_rfl,?_⟩
  simp

variable {E : ∀a,Set (Spin (n a))}

lemma LocalUniformWeak.congr {P F F' : ∀a,Observables (n a)} (h : LocalUniformWeak E P F)
    (he : ∀a x,F a x=F' a x) : LocalUniformWeak E P F' := by
  have : F=F' := funext fun a=>funext (he a)
  rwa [←this]

lemma LocalUniformWeak.add {P F H : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F)
    (hH : LocalUniformWeak E P H) : LocalUniformWeak E P (fun a x=>F a x+H a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨D,hD,hH⟩:=hH
  refine ⟨C+D,add_nonneg hC hD,fun a G hG=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a G hG) (hH a G hG)).trans_eq (by ring))

lemma LocalUniformWeak.neg {P F : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F) :
    LocalUniformWeak E P (fun a x=>-F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  refine ⟨C,hC,fun a G hG=>?_⟩
  simpa using hF a G hG

lemma LocalUniformWeak.sub {P F H : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F)
    (hH : LocalUniformWeak E P H) : LocalUniformWeak E P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg

lemma LocalUniformWeak.sum {τ : Type*} [Fintype τ] {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (h : ∀t,LocalUniformWeak E P (F t)) :
    LocalUniformWeak E P (fun a x=>∑t,F t a x) := by
  classical
  choose C hC hb using h
  refine ⟨∑t,C t,Finset.sum_nonneg (fun t _=>hC t),fun a G hG=>?_⟩
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun t _=>hb t a G hG).trans_eq (Finset.sum_mul ..).symm)

lemma LocalUniformWeak.mul {P F θ : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : LocalUniformWeak E P F) (hθ : LocalUniformMultiplier E θ) :
    LocalUniformWeak E P (fun a x=>θ a x*F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨B,L,hB,hL,hθ,hd⟩:=hθ
  refine ⟨C*Real.sqrt (3*B^2+2*L^2),by positivity,fun a G hG=>?_⟩
  have hf:=hF a (fun x=>θ a x*G x) (by intro x hx; simp [hG x hx])
  have hm:=mul_le_mul_of_nonneg_left (local_star_multiplier (P a) (hP a) (E a) (θ a) G hG (hθ a) (hd a)) hC
  calc
    _ = |∑x,P a x*(θ a x*G x)*F a x| := by
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ C*(Real.sqrt (3*B^2+2*L^2)*starNorm (P a) G) := hf.trans hm
    _ = _ := by ring

lemma LocalUniformMultiplier.const (E : ∀a,Set (Spin (n a))) (c : ℝ) : LocalUniformMultiplier (n:=n) E (fun _ _=>c) := by
  refine ⟨|c|,0,abs_nonneg _,le_rfl,fun _ _ _=>le_rfl,?_⟩
  intro a x hx
  simp [halfDiff]

lemma LocalUniformWeak.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : LocalUniformWeak E P F) (c : ℝ) : LocalUniformWeak E P (fun a x=>c*F a x) :=
  hF.mul hP (LocalUniformMultiplier.const E c)

lemma LocalUniformWeak.base (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hp : ∀a,∑x,P a x=1) (U : ∀a,VectorFields (n a))
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hD : ∀a x,x∈flipNeighborhood (E a)→∑i,|halfDiff i (fun y=>U a y i) x|≤A)
    (hU : ∀a x,x∈flipNeighborhood (E a)→vectorNorm (U a x)≤B) :
    LocalUniformWeak E P (fun a x=>∑i,(spin x i-conditionalMean (P a) x i)*U a x i) := by
  refine ⟨2*B+5*A,by positivity,fun a G hG=>?_⟩
  apply local_signed_base_star (P a) (hP a) (hp a) (E a) G (U a) hA hB hG (hD a)
  intro x hx
  simpa only [vectorNorm_sq] using pow_le_pow_left₀ (vectorNorm_nonneg _) (hU a x hx) 2

lemma UniformWeak.localize {P F : ∀a,Observables (n a)}
    (h : UniformWeak P F) (E : ∀a,Set (Spin (n a))) : LocalUniformWeak E P F := by
  obtain ⟨C,hC,hh⟩:=h
  exact ⟨C,hC,fun a G _=>hh a G⟩

lemma UniformMultiplier.localize {θ : ∀a,Observables (n a)}
    (h : UniformMultiplier θ) (E : ∀a,Set (Spin (n a))) : LocalUniformMultiplier E θ := by
  obtain ⟨B,L,hB,hL,hθ,hd⟩:=h
  exact ⟨B,L,hB,hL,fun a x _=>hθ a x,fun a x _=>hd a x⟩

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ} {E : ∀a,Set (Spin (n a))}

lemma LocalUniformWeak.congr_on {P F F' : ∀a,Observables (n a)} (h : LocalUniformWeak E P F)
    (he : ∀a x,x∈E a→F a x=F' a x) : LocalUniformWeak E P F' := by
  obtain ⟨C,hC,hh⟩:=h
  refine ⟨C,hC,fun a G hG=>?_⟩
  convert hh a G hG using 2
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx:x∈E a
  · rw [he a x hx]
  · simp [hG x hx]

lemma LocalUniformMultiplier.normedMean (hn : ∀a,0<n a) (U : ∀a,VectorFields (n a))
    {B : ℝ} (hB : 0≤B) (hU : ∀a x,x∈flipNeighborhood (E a)→SmallBound (U a) x B) :
    LocalUniformMultiplier E (fun a x=>Real.sqrt (n a:ℝ)*siteMean (U a) x) := by
  exact ⟨B,B,hB,hB,fun a x hx=>scaledMean_size (hn a) _ _ hB (hU a x hx).size,
    fun a x hx=>scaledMean_difference (hn a) _ _ hB (hU a x (Or.inl hx)).derivative⟩

lemma local_uniform_normalized_pair (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hn : ∀a,0<n a) (R U V : ∀a,VectorFields (n a))
    (hV : LocalUniformWeak E P (fun a x=>∑i,R a x i*(V a x i/Real.sqrt (n a:ℝ))))
    {B : ℝ} (hB : 0≤B) (hU : ∀a x,x∈flipNeighborhood (E a)→SmallBound (U a) x B) :
    LocalUniformWeak E P (fun a x=>siteMean (U a) x*(∑i,R a x i*V a x i)) := by
  exact (hV.mul hP (LocalUniformMultiplier.normedMean hn U hB hU)).congr
    (fun a x=>normalized_pair_cancel (hn a) (R a) (V a) (siteMean (U a)) x)

end SKGapCutoff.Static

end
end

end OAI
