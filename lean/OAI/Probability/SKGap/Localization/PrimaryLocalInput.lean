import Mathlib
import OAI.Probability.SKGap.Localization.FiniteRecipeControl

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing.Primary
variable {n : ℕ}

def averageBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  let C:=differentiationBound j R B k
  let T:=C+8*C^2
  2*T+4*T^2
lemma averageBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤averageBudget j R B k := by
  have hh:=differentiationBound_nonneg (j:=j) hR hB k
  unfold averageBudget
  positivity

def localPrimaryBudget (j R B : ℝ) (M : ℕ) : ℝ :=
  ∑q:Fin M,(differentiationBound j R B q.val+averageBudget j R B q.val)
lemma localPrimaryBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) :
    0≤localPrimaryBudget j R B M :=
  Finset.sum_nonneg (fun index _=>add_nonneg
    (differentiationBound_nonneg hR hB index.val) (averageBudget_nonneg hR hB index.val))
lemma localPrimaryBudget_bounds {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) (q : Fin M) :
    differentiationBound j R B q.val≤localPrimaryBudget j R B M ∧
    averageBudget j R B q.val≤localPrimaryBudget j R B M := by
  have hh:=Finset.single_le_sum (s:=Finset.univ)
    (fun r (_:r∈Finset.univ)=>add_nonneg (differentiationBound_nonneg (j:=j) hR hB r.val)
      (averageBudget_nonneg (j:=j) hR hB r.val)) (Finset.mem_univ q)
  have h1:=differentiationBound_nonneg (j:=j) hR hB q.val
  have h2:=averageBudget_nonneg (j:=j) hR hB q.val
  exact ⟨(le_add_of_nonneg_right h2).trans hh,(le_add_of_nonneg_left h1).trans hh⟩

lemma onsager_derivative_bound {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) {q : ℕ} (hq : q≤M) :
    ‖derivativeVector (onsager j J h q) x‖≤localPrimaryBudget j R B M := by
  cases q with
  | zero=>
    have he : onsager j J h 0=0:=funext (onsager_zero j J h)
    rw [he]
    have hz : derivativeVector (0 : Spin n→ℝ) x=0 := by
      ext i; simp [derivativeVector,halfDiff]
    rw [hz,norm_zero]
    exact localPrimaryBudget_nonneg (j:=j) hR hB M
  | succ k=>
    have hh:=primary_average_differentiation J h x hn hR hB hJ k (fun l hl=>hformal l (by omega))
    have hh':(n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j R B k)^2 := by
      simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using hh
    exact (derivative_norm_of_mean_square hn (averageBudget_nonneg hR hB k) hh').trans
      (localPrimaryBudget_bounds hR hB M ⟨k,by omega⟩).2

lemma derivativeVector_mul_sub (c : ℝ) (f g : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*(f y-g y)) x=c • (derivativeVector f x-derivativeVector g x) := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,PiLp.sub_apply]
  simp only [halfDiff]
  ring

theorem primary_local_input {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) :
    let C:=localPrimaryBudget j R B M
    LocalOrdinaryInput (emptyRecipe j J h M) (fun q=>primaryTree j J h x q.val) x 0
      ⟨1,1,C,R,C,(M:ℝ)*(|j| *(C+C)),0,le_rfl,zero_le_one,le_rfl,
        localPrimaryBudget_nonneg hR hB M,hR,localPrimaryBudget_nonneg hR hB M,
        by positivity [localPrimaryBudget_nonneg (j:=j) hR hB M],le_rfl⟩ := by
  dsimp only
  have hC:=localPrimaryBudget_nonneg (j:=j) hR hB M
  have hb:=localPrimaryBudget_bounds (j:=j) hR hB M
  have hd (q : Fin M):=primary_differentiation J h x hn hR hB hJ q.val
    (fun l hl=>hformal l (by omega))
  apply emptyRecipe_local j J h M _ x hC hR hC _ hn hJ
  · intro q; exact (hd q).2.2.2.mono (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).2]
    exact (hd q).1.trans (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).1]
    exact (hd q).2.1.trans (hb q).1
  · intro q; exact (hd q).2.2.1.trans (hb q).1
  · calc
      _ ≤ ∑q:Fin M,|j| *(localPrimaryBudget j R B M+localPrimaryBudget j R B M) := by
        apply Finset.sum_le_sum; intro q _
        rw [derivativeVector_mul_sub,norm_smul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (norm_sub_le _ _).trans (add_le_add
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega))
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega)))
      _ = _ := by simp

end SKGapCutoff.Primary

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

lemma FiniteRecipeControl.onsager_multiplier (H : FiniteRecipeControl j J h M Nmax A) (k : ℕ) (hk : k≤M) :
    UniformMultiplier (fun a x=>j*onsager j (J a) (h a) k x) := by
  have hh : UniformMultiplier (fun a x=>∑q∈Finset.range k,
      j*(onsager j (J a) (h a) (q+1) x-onsager j (J a) (h a) q x)) := by
    apply UniformMultiplier.finset_sum
    intro q hq
    exact H.parameter ⟨q,(Finset.mem_range.mp hq).trans_le hk⟩
  exact hh.congr (fun a x=>onsager_telescope j (J a) (h a) k x)

lemma uniform_normalized_pair (P : ∀a,Observables (n a)) (hP : ∀a x,0≤P a x)
    (hn : ∀a,0<n a) (R U V : ∀a,VectorFields (n a))
    (hV : UniformWeak P (fun a x=>∑i,R a x i*(V a x i/Real.sqrt (n a:ℝ))))
    {C : ℝ} (hC : 0≤C) (hU : ∀a x,SmallBound (U a) x C) :
    UniformWeak P (fun a x=>siteMean (U a) x*(∑i,R a x i*V a x i)) := by
  exact (hV.mul hP (UniformMultiplier.normedMean hn U hC hU)).congr
    (fun a x=>normalized_pair_cancel (hn a) (R a) (V a) (siteMean (U a)) x)

lemma uniform_prev_zero (P : ∀a,Observables (n a)) (U : ∀a,VectorFields (n a)) :
    UniformWeak P (fun a x=>∑i,previousResidual j (J a) (h a) 0 x i*U a x i) := by
  convert UniformWeak.zero P using 1
  ext a x
  simp [previousResidual]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

def RecipeResidualRule (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (P : ∀a,Observables (n a)) (M Nmax p : ℕ) (B : ℝ) : Prop :=
  ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N : ℕ),
    FamilyRecipe j J h D N p B → N+2*p≤Nmax →
    UniformWeak P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i)

lemma residual_rule_base (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (B : ℝ) (hB : B≤A) : RecipeResidualRule j J h P M Nmax 0 B := by
  intro σ inst D N H hN
  obtain ⟨K,hK,hbound⟩:=C.small D N 0 B H (by omega) hB
  have hh:=UniformWeak.base P hP hp (fun a=>(D a).source N) hK hK
    (fun a x=>(hbound a x).2.2) (fun a x=>(hbound a x).1.size)
  apply hh.congr
  intro a x
  simp only [Primary.residual,mag_zero,hm]

lemma residual_rule_step (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (k : ℕ) (hkM : k+1<M)
    (hkA : b k≤A) (hk2 : 2≤b k)
    (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
    (ih : ∀r<k+1,RecipeResidualRule j J h P M Nmax r (b r)) :
    RecipeResidualRule j J h P M Nmax (k+1) (b (k+1)) := by
  intro σ inst D N H hN
  let l : Fin M:=⟨k,by omega⟩
  let m : Fin M:=⟨k+1,hkM⟩
  have hlm : l≠m := by intro he; have hv:=congrArg Fin.val he; dsimp [l,m] at hv; omega
  let E:=fun a=>(D a).appendStein N l m l
  have HE : FamilyRecipe j J h E (N+1) k (b k) := by
    have HH:=(H.mono (show k≤k+1 by omega) le_rfl le_rfl).appendStein l m l le_rfl
      (show k ≤ m.val by dsimp [m]; omega)
      (R:=|j|) (fun a x=>by rw [H.parameter a l]; exact onsager_parameter_bound j (J a) (h a) k x)
    exact HH.mono le_rfl le_rfl hstep
  have hEN : N+1+2*k≤Nmax := by omega
  have source : UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).source (N+1) x i) :=
    ih k (by omega) E (N+1) HE hEN
  have aux : UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).auxiliary (N+1) x i) := by
    have HH:=ih k (by omega) (fun a=>(E a).appendAuxiliary (N+1)) (N+1+1)
      HE.appendAuxiliary (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.appendAuxiliary_source])
  have param := source.mul hP (C.parameter l)
  have prev : UniformWeak P (fun a x=>∑i,previousResidual j (J a) (h a) k x i*(E a).source (N+1) x i) := by
    cases k with
    | zero=>exact uniform_prev_zero P (fun a=>(E a).source (N+1))
    | succ r=>
      have HH:=ih r (by omega) E (N+1) (HE.mono (by omega) le_rfl (hmono (by omega))) (by omega)
      exact HH.congr (fun a x=>by simp only [previousResidual,Primary.residual,Nat.add_sub_cancel])
  have old:=prev.mul hP (C.onsager_multiplier k (by omega))
  have earlier : UniformWeak P (fun a x=>j*(∑t:Fin (N+1),siteMean ((E a).auxCoefficient (N+1) t) x*
      (∑i,residual j (J a) (h a) k x i*(E a).source t.val x i))) := by
    apply UniformWeak.smul hP _ j
    apply UniformWeak.sum
    intro t
    exact (ih k (by omega) E t.val (HE.mono le_rfl t.isLt.le le_rfl) (by omega)).mul hP
      (C.means E (N+1) k (b k) HE (by omega) hkA t)
  obtain ⟨V,hV,hbound⟩:=C.small E (N+1) k (b k) HE (by omega) hkA
  have primary (q : Fin M) (hr : k≤q.val) :
      UniformWeak P (fun a x=>∑i,residual j (J a) (h a) k x i*
        (mag j (J a) (h a) (q.val+1) x i/Real.sqrt (n a:ℝ))) := by
    have HQ:=(HE.normalizedPrimary hn q k hr).mono le_rfl le_rfl hk2
    have HH:=ih k (by omega) (fun a=>(E a).normalizedPrimary q) 0 HQ (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.normalizedPrimary_magnetization _ _ j (J a) (h a) q.val (HE.primary a q)])
  have future : UniformWeak P (fun a x=>j*(∑q:{q:Fin M//q≠l},siteMean ((E a).sourcePartial (N+1) q) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) q.val.val x i))) := by
    apply UniformWeak.smul hP _ j
    apply UniformWeak.sum
    intro q
    by_cases hq : q.val.val<k
    · apply (UniformWeak.zero P).congr
      intro a x
      rw [(HE.admissible a).sourcePartial (N+1) le_rfl q.val hq]
      simp [siteMean]
    · have hne : q.val.val≠k := by
        intro he
        exact q.property (Fin.ext he)
      have hq' : k<q.val.val := by omega
      let r : Fin M:=⟨q.val.val-1,by omega⟩
      have hr : r.val+1=q.val.val := by dsimp [r]; omega
      have HH:=uniform_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
        (fun a=>(E a).sourcePartial (N+1) q.val) (fun a=>mag j (J a) (h a) (r.val+1))
        (primary r (by dsimp [r]; omega)) hV (fun a x=>(hbound a x).2.1 q.val)
      simpa only [hr] using HH
  have last : UniformWeak P (fun a x=>j*(siteMean ((E a).sourcePartial (N+1) l) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) (k+1) x i))) := by
    apply UniformWeak.smul hP _ j
    exact uniform_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
      (fun a=>(E a).sourcePartial (N+1) l) (fun a=>mag j (J a) (h a) (k+1))
      (primary l le_rfl) hV (fun a x=>(hbound a x).2.1 l)
  apply ((((aux.add param).sub old).add earlier).add future).sub last |>.congr
  intro a x
  have hid:=(D a).residual_step N l m l hlm (hn a) j (J a) (hJ a) (h a) k Fin.val
    (H.coupling a) (H.interaction a) (H.predecessor a) rfl (H.primary a l) (H.primary a m)
    (H.parameter a l) ((H.admissible a).sourcePartial N le_rfl l (by dsimp [l]; omega)) x
  dsimp only at hid
  rw [hid]
  dsimp only [E,l]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
