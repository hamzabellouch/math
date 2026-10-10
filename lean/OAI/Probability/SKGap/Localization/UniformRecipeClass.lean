import Mathlib
import OAI.Probability.SKGap.Gaussian.SteinRecipeRegularity
import OAI.Probability.SKGap.Localization.ResidualMultiplier

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

structure FamilyRecipe (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N p : ℕ) (K : ℝ) : Prop where
  interaction : ∀a,(D a).J=J a
  coupling : ∀a,(D a).j=j
  primary : ∀a q,(D a).H q=fld j (J a) (h a) q.val
  predecessor : ∀a q,(D a).predecessor q=mag j (J a) (h a) q.val
  parameter : ∀a q,(D a).θ q=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x)
  seed : ∃S : ℝ,0≤S ∧ ∀a,(∑s,vectorNorm ((D a).seed s))≤S
  coefficients : ∀a x,(D a).CoefficientClass N x K
  admissible : ∀a,(D a).Admissible N p

namespace OrdinaryData
lemma CoefficientClass.mono {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype σ] {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n}
    {K L : ℝ} (h : D.CoefficientClass N x K) (hKL : K≤L) : D.CoefficientClass N x L := by
  refine ⟨h.one_le.trans hKL,fun a ha s=>(h.seedRegular a ha s).mono hKL,
    fun a ha b=>(h.auxRegular a ha b).mono hKL,?_,?_⟩
  · intro a ha s i k t ht; exact (h.seedValue a ha s i k t ht).trans hKL
  · intro a ha b i k t ht; exact (h.auxValue a ha b i k t ht).trans hKL
end OrdinaryData

namespace FamilyRecipe
variable {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ} {N p : ℕ} {K : ℝ}
lemma mono (H : FamilyRecipe j J h D N p K) {r A : ℕ} {L : ℝ}
    (hr : r≤p) (hA : A≤N) (hK : K≤L) : FamilyRecipe j J h D A r L :=
  ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x=>((H.coefficients a x).prefix hA).mono hK,fun a=>(H.admissible a).prefix hA |>.mono hr⟩

lemma appendStein (H : FamilyRecipe j J h D N p K) (l m α : Fin M)
    (hl : p≤l.val) (hm : p ≤ m.val) {R : ℝ}
    (ht : ∀a x,|(D a).θ α x|≤R) :
    FamilyRecipe j J h (fun a=>(D a).appendStein N l m α) (N+1) p (K+4*steinCoefficientBudget R*K) := by
  refine ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,?_,?_⟩
  · intro a x
    exact (H.coefficients a x).appendStein l m α R (ht a x) (fun k=>ht a (flip x k))
  · intro a; exact (D a).appendStein_Admissible N p l m α hl hm (H.admissible a)

lemma appendAuxiliary (H : FamilyRecipe j J h D N p K) :
    FamilyRecipe j J h (fun a=>(D a).appendAuxiliary N) (N+1) p K :=
  ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,H.seed,
    fun a x=>(H.coefficients a x).appendAuxiliary,
    fun a=>(D a).appendAuxiliary_Admissible N p (H.admissible a)⟩

lemma normalizedPrimary (H : FamilyRecipe j J h D N p K) (hn : ∀a,0<n a)
    (q : Fin M) (r : ℕ) (hr : r≤q.val) :
    FamilyRecipe j J h (fun a=>(D a).normalizedPrimary q) 0 r 2 := by
  refine ⟨H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,
    ⟨1,by norm_num,fun a=>le_of_eq ((D a).normalizedPrimary_seed q (hn a))⟩,
    fun a x=>(D a).normalizedPrimary_coefficientClass q 0 x,
    fun a=>(D a).normalizedPrimary_Admissible q r hr 0⟩

lemma sameEnvironment (H : FamilyRecipe j J h D N p K)
    {E : ∀a,OrdinaryData (n a) (Fin M) (Fin M) τ} {A r : ℕ} {L : ℝ}
    (H' : FamilyRecipe j J h E A r L) (a : Ω) :
    (D a).J=(E a).J ∧ (D a).j=(E a).j ∧ (D a).H=(E a).H ∧
      (D a).predecessor=(E a).predecessor ∧ (D a).θ=(E a).θ := by
  exact ⟨(H.interaction a).trans (H'.interaction a).symm,
    (H.coupling a).trans (H'.coupling a).symm,
    funext fun q=>(H.primary a q).trans (H'.primary a q).symm,
    funext fun q=>(H.predecessor a q).trans (H'.predecessor a q).symm,
    funext fun q=>(H.parameter a q).trans (H'.parameter a q).symm⟩

end FamilyRecipe
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.congr {F H : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (he : ∀a x,F a x=H a x) : UniformMultiplier H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma UniformMultiplier.add {F H : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hH : UniformMultiplier H) : UniformMultiplier (fun a x=>F a x+H a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨C,K,hC,hK,hH,hdH⟩:=hH
  refine ⟨B+C,Real.sqrt (2*L^2+2*K^2),add_nonneg hB hC,Real.sqrt_nonneg _,
    fun a x=>(abs_add_le _ _).trans (add_le_add (hF a x) (hH a x)),fun a x=>?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have he (i : Fin (n a)) : halfDiff i (fun y=>F a y+H a y) x=halfDiff i (F a) x+halfDiff i (H a) x := by
    unfold halfDiff; ring
  simp only [he]
  calc
    _ ≤ ∑i,(2*(halfDiff i (F a) x)^2+2*(halfDiff i (H a) x)^2) := by
      apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (halfDiff i (F a) x-halfDiff i (H a) x)]
    _ = 2*(∑i,(halfDiff i (F a) x)^2)+2*(∑i,(halfDiff i (H a) x)^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by linarith [hdF a x,hdH a x]
lemma UniformMultiplier.finset_sum {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using (UniformMultiplier.const (n:=n) 0)
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
lemma UniformMultiplier.sum {τ : Type*} [Fintype τ] {F : τ→∀a,Observables (n a)}
    (h : ∀t,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∑t,F t a x) :=
  UniformMultiplier.finset_sum Finset.univ (fun t _=>h t)
end SKGapCutoff.Static
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma onsager_bounds (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤onsager j J h k x ∧ onsager j J h k x≤1 := by
  have hm (i : Fin n) : (mag j J h k x i)^2≤1 := by
    have H:=primaryState_mag_bounded j J h k x i
    have H':=sq_le_sq₀ (abs_nonneg (mag j J h k x i)) (by norm_num : (0:ℝ)≤1)
    simpa only [sq_abs,one_pow] using H'.mpr H
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hm i))) (Nat.cast_nonneg n)
  · by_cases hn : n=0
    · simp [onsager,siteMean,hn]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      calc
        (∑i:Fin n,(1-(mag j J h k x i)^2)) ≤ ∑i:Fin n,(1:ℝ) :=
          Finset.sum_le_sum fun i _=>sub_le_self _ (sq_nonneg _)
        _ = _ := by simp
lemma onsager_parameter_bound (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |j*(onsager j J h (k+1) x-onsager j J h k x)|≤|j| := by
  have H:=onsager_bounds j J h k x
  have H':=onsager_bounds j J h (k+1) x
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (show |onsager j J h (k+1) x-onsager j J h k x|≤1 from
    abs_le.mpr ⟨by linarith,by linarith⟩) (abs_nonneg j)
lemma onsager_telescope (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    (∑q∈Finset.range k,j*(onsager j J h (q+1) x-onsager j J h q x))=j*onsager j J h k x := by
  induction k with
  | zero=>simp [onsager_zero]
  | succ k ih=>rw [Finset.sum_range_succ,ih]; ring
end SKGapCutoff.Primary

end
end

end OAI
