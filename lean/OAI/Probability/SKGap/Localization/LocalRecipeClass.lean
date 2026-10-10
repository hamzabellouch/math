import Mathlib
import OAI.Probability.SKGap.Gaussian.SteinRecipeRegularity
import OAI.Probability.SKGap.Localization.LocalUniformWeak
import OAI.Probability.SKGap.Localization.StartedPrimary
import OAI.Probability.SKGap.Localization.UniformRecipeClass

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {σ τ : Type} [Fintype σ] [Fintype τ]

structure LocalFamilyRecipe (E : ∀a,Set (Spin (n a))) (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (Θ : ∀a,κ→Observables (n a))
    (w y : ∀a,VectorFields (n a)) (D : ∀a,OrdinaryData (n a) (Fin M) κ σ) (N p : ℕ) (K : ℝ) : Prop where
  positive : 1≤N
  interaction : ∀a,(D a).J=J a
  coupling : ∀a,(D a).j=j
  primary : ∀a q,(D a).H q=fld j (J a) (h a) q.val
  predecessor : ∀a q,(D a).predecessor q=mag j (J a) (h a) q.val
  parameter : ∀a,(D a).θ=Θ a
  seed : ∃S : ℝ,0≤S ∧ ∀a,(∑s,vectorNorm ((D a).seed s))≤S
  coefficients : ∀a x,x∈flipNeighborhood (E a)→(D a).CoefficientClass N x K
  admissible : ∀a,(D a).Admissible N p
  initial : ∀a x,x∈E a→(D a).startedSource (w a) (y a) 1 x=w a x ∧
    (D a).startedAuxiliary (w a) (y a) 1 x=y a x

namespace LocalFamilyRecipe
variable {E : ∀a,Set (Spin (n a))} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}
variable {D : ∀a,OrdinaryData (n a) (Fin M) κ σ} {N p : ℕ} {K : ℝ}

lemma mono (H : LocalFamilyRecipe E j J h Θ w y D N p K) {r A : ℕ} {L : ℝ}
    (hr : r≤p) (hA : A≤N) (hpos : 1≤A) (hK : K≤L) : LocalFamilyRecipe E j J h Θ w y D A r L :=
  ⟨hpos,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x hx=>((H.coefficients a x hx).prefix hA).mono hK,
    fun a=>(H.admissible a).prefix hA |>.mono hr,H.initial⟩

lemma appendStein (H : LocalFamilyRecipe E j J h Θ w y D N p K) (l m : Fin M) (α : κ)
    (hl : p≤l.val) (hm : p ≤ m.val) {R : ℝ}
    (ht : ∀a x,|(D a).θ α x|≤R) :
    LocalFamilyRecipe E j J h Θ w y (fun a=>(D a).appendStein N l m α) (N+1) p
      (K+4*steinCoefficientBudget R*K) := by
  refine ⟨by omega,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,?_,?_,?_⟩
  · intro a x hx
    exact (H.coefficients a x hx).appendStein l m α R (ht a x) (fun k=>ht a (flip x k))
  · intro a;exact (D a).appendStein_Admissible N p l m α hl hm (H.admissible a)
  · intro a x hx
    have hp:=(D a).appendProduct_started_prefix (w a) (y a) N
      (phiCoefficient l m α) (phiDerivative l m α) 1 H.positive
    simpa only [OrdinaryData.appendStein,hp.1,hp.2] using H.initial a x hx

lemma appendAuxiliary (H : LocalFamilyRecipe E j J h Θ w y D N p K) :
    LocalFamilyRecipe E j J h Θ w y (fun a=>(D a).appendAuxiliary N) (N+1) p K := by
  refine ⟨by omega,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x hx=>(H.coefficients a x hx).appendAuxiliary,
    fun a=>(D a).appendAuxiliary_Admissible N p (H.admissible a),?_⟩
  intro a x hx
  have hp:=(D a).appendAuxiliary_started_prefix (w a) (y a) N 1 H.positive
  simpa only [hp.1,hp.2] using H.initial a x hx

lemma appendPrimary (H : LocalFamilyRecipe E j J h Θ w y D N p K) (hn : ∀a,0<n a)
    (hK : 2≤K) (q : Fin M) (hq : p≤q.val) :
    LocalFamilyRecipe E j J h Θ w y (fun a=>(D a).appendPrimary N q) (N+1) p K := by
  refine ⟨by omega,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,?_,
    fun a x hx=>(H.coefficients a x hx).appendPrimary hK q,
    fun a=>(D a).appendPrimary_Admissible N p q hq (H.admissible a),?_⟩
  · obtain ⟨S,hS,hs⟩:=H.seed
    exact ⟨S+1,by positivity,fun a=>by rw [(D a).appendPrimary_seed N q (hn a)];linarith [hs a]⟩
  · intro a x hx
    have hp:=(D a).appendPrimary_started_prefix (w a) (y a) N q 1 H.positive
    simpa only [hp.1,hp.2] using H.initial a x hx

lemma sameEnvironment (H : LocalFamilyRecipe E j J h Θ w y D N p K)
    {F : ∀a,OrdinaryData (n a) (Fin M) κ τ} {A r : ℕ} {L : ℝ}
    (H' : LocalFamilyRecipe E j J h Θ w y F A r L) (a : Ω) :
    (D a).J=(F a).J ∧ (D a).j=(F a).j ∧ (D a).H=(F a).H ∧
      (D a).predecessor=(F a).predecessor ∧ (D a).θ=(F a).θ := by
  exact ⟨(H.interaction a).trans (H'.interaction a).symm,
    (H.coupling a).trans (H'.coupling a).symm,
    funext fun q=>(H.primary a q).trans (H'.primary a q).symm,
    funext fun q=>(H.predecessor a q).trans (H'.predecessor a q).symm,
    (H.parameter a).trans (H'.parameter a).symm⟩

end LocalFamilyRecipe
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

structure FiniteLocalRecipeControl (E : ∀a,Set (Spin (n a))) (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (Θ : ∀a,κ→Observables (n a))
    (w y : ∀a,VectorFields (n a)) (M Nmax : ℕ) (A : ℝ) : Prop where
  small : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ)
    (N p : ℕ) (K : ℝ), LocalFamilyRecipe E j J h Θ w y D N p K → N≤Nmax → K≤A →
    ∃C : ℝ,0≤C ∧ ∀a x,x∈flipNeighborhood (E a)→SmallBound ((D a).startedSource (w a) (y a) N) x C ∧
      (∀q,SmallBound ((D a).startedPartial (w a) (y a) N q) x C) ∧
      (∑i,|derivativeMatrix ((D a).startedSource (w a) (y a) N) x i i|)≤C
  means : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ)
    (N p : ℕ) (K : ℝ), LocalFamilyRecipe E j J h Θ w y D N p K → N≤Nmax → K≤A →
    ∀b:Fin N,LocalUniformMultiplier E (fun a=>siteMean ((D a).auxCoefficient N b))
  parameter : ∀q:Fin M,LocalUniformMultiplier E
    (fun a x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))

end SKGapCutoff.Recipe
end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {E : ∀a,Set (Spin (n a))}
lemma LocalUniformMultiplier.congr {F H : ∀a,Observables (n a)} (hF : LocalUniformMultiplier E F)
    (he : ∀a x,F a x=H a x) : LocalUniformMultiplier E H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma LocalUniformMultiplier.add {F H : ∀a,Observables (n a)} (hF : LocalUniformMultiplier E F)
    (hH : LocalUniformMultiplier E H) : LocalUniformMultiplier E (fun a x=>F a x+H a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨C,K,hC,hK,hH,hdH⟩:=hH
  refine ⟨B+C,Real.sqrt (2*L^2+2*K^2),add_nonneg hB hC,Real.sqrt_nonneg _,
    fun a x hx=>(abs_add_le _ _).trans (add_le_add (hF a x hx) (hH a x hx)),fun a x hx=>?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have he (i : Fin (n a)) : halfDiff i (fun y=>F a y+H a y) x=halfDiff i (F a) x+halfDiff i (H a) x := by
    unfold halfDiff; ring
  simp only [he]
  calc
    _ ≤ ∑i,(2*(halfDiff i (F a) x)^2+2*(halfDiff i (H a) x)^2) := by
      apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (halfDiff i (F a) x-halfDiff i (H a) x)]
    _ = 2*(∑i,(halfDiff i (F a) x)^2)+2*(∑i,(halfDiff i (H a) x)^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by linarith [hdF a x hx,hdH a x hx]
lemma LocalUniformMultiplier.finset_sum {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,LocalUniformMultiplier E (F t)) : LocalUniformMultiplier E (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using (LocalUniformMultiplier.const (n:=n) E 0)
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
lemma LocalUniformMultiplier.sum {τ : Type*} [Fintype τ] {F : τ→∀a,Observables (n a)}
    (h : ∀t,LocalUniformMultiplier E (F t)) : LocalUniformMultiplier E (fun a x=>∑t,F t a x) :=
  LocalUniformMultiplier.finset_sum Finset.univ (fun t _=>h t)
end SKGapCutoff.Static

end
end

end OAI
