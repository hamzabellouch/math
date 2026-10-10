import Mathlib
import OAI.Probability.SKGap.Localization.SelectionPartition

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformWeak.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformWeak P (F t)) :
    UniformWeak P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformWeak.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
lemma UniformSquare.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformSquare P (F t)) :
    UniformSquare P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformSquare.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

def constantRecipe (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M : ℕ) :
    OrdinaryData n (Fin M) (Fin M) Unit where
  J:=J
  j:=j
  H:=fun q=>fld j J h q.val
  predecessor:=fun q=>mag j J h q.val
  θ:=fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x)
  seed:=fun _=>e
  seedFunction:=fun _ _ _ _=>1
  seedDerivative:=fun _ _ _ _=>0
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

lemma constantRecipe_source (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M : ℕ) :
    (constantRecipe j J h e M).source 0=fun _=>e := by
  rw [OrdinaryData.source_eq]
  ext x i
  simp [OrdinaryData.sourceOf,constantRecipe,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,coefficient]

lemma constantRecipe_coefficients (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N : ℕ) (x : Spin n) :
    (constantRecipe j J h e M).CoefficientClass N x 1 := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩
  · intro a ha s; exact (segmentRegular_const _ _ x 1).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [SegmentValue,constantRecipe]
  · intros; norm_num [SegmentValue,constantRecipe]

lemma constantRecipe_admissible (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N p : ℕ) :
    (constantRecipe j J h e M).Admissible N p := by
  intro a ha q hq
  constructor <;> intro s <;> ext x i <;>
    simp [OrdinaryData.seedPartial,OrdinaryData.auxPartial,localPartial,constantRecipe,partialAt]

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma constantRecipe_family (he : ∀a,vectorNorm (e a)≤1) (M p : ℕ) :
    FamilyRecipe j J h (fun a=>constantRecipe j (J a) (h a) (e a) M) 0 p 2 := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
    ⟨1,zero_le_one,?_⟩,fun a x=>(constantRecipe_coefficients j (J a) (h a) (e a) M 0 x).mono (by norm_num),
    fun a=>constantRecipe_admissible j (J a) (h a) (e a) M 0 p⟩
  intro a; simpa [constantRecipe] using he a

lemma primary_residual_telescope (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (d : ℕ) (x : Spin n) (i : Fin n) :
    (∑k∈Finset.range d,residual j J h k x i)=spin x i-mag j J h d x i := by
  induction d with
  | zero=>simp [mag_zero]
  | succ d ih=>rw [Finset.sum_range_succ,ih];dsimp [Primary.residual];ring

theorem gibbs_constant_residuals (d : ℕ) (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a))
    (he : ∀a,vectorNorm (e a)≤1) (k : ℕ) (hk : k≤d) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) := by
  have H (l : ℕ) (hl : l<k):=
    gibbs_ordinary_residuals l 0 (by norm_num : (2:ℝ)≤2) (by omega : l<d+1)
      hR hB hW hC hn hJ hdiag
      (fun a=>(hevent a).mono (residualCoefficientBudget_depth_mono j (by omega)) (by omega))
      (fun a=>constantRecipe j (J a) (h a) (e a) (d+1)) (constantRecipe_family he (d+1) l)
  have H' (l : ℕ) (hl : l<k) :
      UniformWeak (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) ∧
      UniformSquare (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) := by
    simpa only [constantRecipe_source] using H l hl
  have hh (a : Ω) (x : Spin (N a)) :
      (∑l∈Finset.range k,∑i,residual j (J a) (h a) l x i*e a i)=
      ∑i,(spin x i-mag j (J a) (h a) k x i)*e a i := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,primary_residual_telescope]
  exact ⟨((UniformWeak.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).1))).congr hh,
    ((UniformSquare.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).2))).congr hh⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.neg {F : ∀a,Observables (n a)} (hF : UniformMultiplier F) :
    UniformMultiplier (fun a x=>-F a x) := by
  obtain ⟨B,L,hB,hL,hF,hd⟩:=hF
  refine ⟨B,L,hB,hL,fun a x=>by simpa using hF a x,fun a x=>?_⟩
  have he (i : Fin (n a)) : halfDiff i (fun y=>-F a y) x= -halfDiff i (F a) x := by unfold halfDiff;ring
  simpa only [he,neg_sq] using hd a x
lemma UniformMultiplier.mul {F G : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hG : UniformMultiplier G) : UniformMultiplier (fun a x=>F a x*G a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨D,K,hD,hK,hG,hdG⟩:=hG
  exact ⟨B*D,Real.sqrt (2*B^2*K^2+2*D^2*L^2),mul_nonneg hB hD,Real.sqrt_nonneg _,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).1,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).2⟩
lemma UniformMultiplier.finset_prod {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∏t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformMultiplier.const (n:=n) 1
  | @insert t s ht ih=>
    simpa only [Finset.prod_insert ht] using (h t (Finset.mem_insert_self ..)).mul
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualDerivativeBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  differentiationBound j R B k+differentiationBound j R B (k+1)

lemma residualDerivativeBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤residualDerivativeBudget j R B k :=
  add_nonneg (differentiationBound_nonneg hR hB k) (differentiationBound_nonneg hR hB (k+1))

lemma residual_derivative_bound (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤residualDerivativeBudget j R B k := by
  have hm (l : ℕ) (hl : l≤k+1) :
      SKGap.opNorm (derivativeMatrix (mag j J h l) x)≤differentiationBound j R B l :=
    (primary_differentiation J h x hn hR hB hJ l (fun t ht=>hformal x t (ht.trans hl))).2.2.1
  rw [show derivativeMatrix (residual j J h k) x=
    derivativeMatrix (mag j J h k) x-derivativeMatrix (mag j J h (k+1)) x from derivativeMatrix_sub _ _ x]
  simp only [opNorm_eq,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hm _ (by omega)) (hm _ le_rfl))

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B ρ : ℝ} {M : ℕ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

lemma residualCutoff_uniform (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B)
    (hn : ∀a,0<N a) (hop : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M→ShapeBound (formalField j (J a) (h a) x l) B)
    (k : ℕ) (hk : k+2<M) :
    UniformMultiplier (fun a=>residualCutoff ρ j (J a) (h a) k) := by
  obtain ⟨K,hK⟩:=residualScalarCutoff_lipschitz
  let A:=residualDerivativeBudget j R B k
  let D:=residualDerivativeBudget j R B (k+1)
  have hA : 0≤A:=residualDerivativeBudget_nonneg hR hB k
  have hD : 0≤D:=residualDerivativeBudget_nonneg hR hB (k+1)
  let L:=2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*D+2*D^2))
  have hL : 0≤L:=by dsimp [L];positivity
  refine ⟨1,L,zero_le_one,hL,fun a x=>?_,fun a x=>?_⟩
  · rw [abs_of_nonneg (residualCutoff_bounds ρ j (J a) (h a) k x).1]
    exact (residualCutoff_bounds ρ j (J a) (h a) k x).2
  · have H:=residualCutoff_gradient (hn a) hρ hK (J a) (h a) k x hA hD
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) k (fun x l hl=>hformal a x l (by omega)) x)
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) (k+1) (fun x l hl=>hformal a x l (by omega)) x)
    have hone : 1≤Real.sqrt (N a:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn a)
    have hd : ‖derivativeVector (residualCutoff ρ j (J a) (h a) k) x‖≤L :=
      H.trans (div_le_self hL hone)
    simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) hd 2

lemma cutoffWeight_uniform {C : ℕ→∀a,Observables (N a)} (k : ℕ)
    (hC : ∀l≤k,UniformMultiplier (C l)) :
    UniformMultiplier (fun a x=>cutoffWeight (fun l=>C l a x) k) := by
  exact (hC k le_rfl).mul (UniformMultiplier.finset_prod (Finset.range k)
    (fun l hl=>(UniformMultiplier.const 1).add (hC l (Finset.mem_range.mp hl).le).neg))

lemma residualWeight_uniform (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B)
    (hn : ∀a,0<N a) (hop : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M→ShapeBound (formalField j (J a) (h a) x l) B)
    (k : ℕ) (hk : k+2<M) :
    UniformMultiplier (fun a x=>cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k) := by
  apply cutoffWeight_uniform
  intro l hl
  exact residualCutoff_uniform hρ hR hB hn hop hformal l (by omega)

end SKGapCutoff.Recipe

end
end

end OAI
