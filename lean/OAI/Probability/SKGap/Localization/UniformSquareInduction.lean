import Mathlib
import OAI.Probability.SKGap.Localization.UniformResidual

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

def RecipeSquareResidualRule (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (P : ∀a,Observables (n a)) (M Nmax p : ℕ) (B : ℝ) : Prop :=
  ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N : ℕ),
    FamilyRecipe j J h D N p B → N+2*p≤Nmax →
    UniformSquare P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i)

lemma residual_square_rule_base (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (_ : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (B : ℝ) (hB : B≤A) : RecipeSquareResidualRule j J h P M Nmax 0 B := by
  intro σ inst D N H hN
  obtain ⟨K,hK,hbound⟩:=C.small D N 0 B H (by omega) hB
  have hh:=UniformSquare.base P hP (fun a=>(D a).source N) hK hK
    (fun a x=>(hbound a x).2.2) (fun a x=>(hbound a x).1.size)
  apply hh.congr
  intro a x
  simp only [Primary.residual,mag_zero,hm]

lemma residual_square_rule_step (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (k : ℕ) (hkM : k+1<M)
    (hkA : b k≤A) (hk2 : 2≤b k)
    (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
    (ih : ∀r<k+1,RecipeSquareResidualRule j J h P M Nmax r (b r)) :
    RecipeSquareResidualRule j J h P M Nmax (k+1) (b (k+1)) := by
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
  have source : UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).source (N+1) x i) :=
    ih k (by omega) E (N+1) HE hEN
  have aux : UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*(E a).auxiliary (N+1) x i) := by
    have HH:=ih k (by omega) (fun a=>(E a).appendAuxiliary (N+1)) (N+1+1)
      HE.appendAuxiliary (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.appendAuxiliary_source])
  have param := source.mul hP (C.parameter l)
  have prev : UniformSquare P (fun a x=>∑i,previousResidual j (J a) (h a) k x i*(E a).source (N+1) x i) := by
    cases k with
    | zero=>exact uniform_square_prev_zero P (fun a=>(E a).source (N+1))
    | succ r=>
      have HH:=ih r (by omega) E (N+1) (HE.mono (by omega) le_rfl (hmono (by omega))) (by omega)
      exact HH.congr (fun a x=>by simp only [previousResidual,Primary.residual,Nat.add_sub_cancel])
  have old:=prev.mul hP (C.onsager_multiplier k (by omega))
  have earlier : UniformSquare P (fun a x=>j*(∑t:Fin (N+1),siteMean ((E a).auxCoefficient (N+1) t) x*
      (∑i,residual j (J a) (h a) k x i*(E a).source t.val x i))) := by
    apply UniformSquare.smul hP _ j
    apply UniformSquare.sum
    intro t
    exact (ih k (by omega) E t.val (HE.mono le_rfl t.isLt.le le_rfl) (by omega)).mul hP
      (C.means E (N+1) k (b k) HE (by omega) hkA t)
  obtain ⟨V,hV,hbound⟩:=C.small E (N+1) k (b k) HE (by omega) hkA
  have primary (q : Fin M) (hr : k≤q.val) :
      UniformSquare P (fun a x=>∑i,residual j (J a) (h a) k x i*
        (mag j (J a) (h a) (q.val+1) x i/Real.sqrt (n a:ℝ))) := by
    have HQ:=(HE.normalizedPrimary hn q k hr).mono le_rfl le_rfl hk2
    have HH:=ih k (by omega) (fun a=>(E a).normalizedPrimary q) 0 HQ (by omega)
    exact HH.congr (fun a x=>by rw [OrdinaryData.normalizedPrimary_magnetization _ _ j (J a) (h a) q.val (HE.primary a q)])
  have future : UniformSquare P (fun a x=>j*(∑q:{q:Fin M//q≠l},siteMean ((E a).sourcePartial (N+1) q) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) q.val.val x i))) := by
    apply UniformSquare.smul hP _ j
    apply UniformSquare.sum
    intro q
    by_cases hq : q.val.val<k
    · apply (UniformSquare.zero P).congr
      intro a x
      rw [(HE.admissible a).sourcePartial (N+1) le_rfl q.val hq]
      simp [siteMean]
    · have hne : q.val.val≠k := by
        intro he
        exact q.property (Fin.ext he)
      have hq' : k<q.val.val := by omega
      let r : Fin M:=⟨q.val.val-1,by omega⟩
      have hr : r.val+1=q.val.val := by dsimp [r]; omega
      have HH:=uniform_square_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
        (fun a=>(E a).sourcePartial (N+1) q.val) (fun a=>mag j (J a) (h a) (r.val+1))
        (primary r (by dsimp [r]; omega)) hV (fun a x=>(hbound a x).2.1 q.val)
      simpa only [hr] using HH
  have last : UniformSquare P (fun a x=>j*(siteMean ((E a).sourcePartial (N+1) l) x*
      (∑i,residual j (J a) (h a) k x i*mag j (J a) (h a) (k+1) x i))) := by
    apply UniformSquare.smul hP _ j
    exact uniform_square_normalized_pair P hP hn (fun a=>residual j (J a) (h a) k)
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

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_residual_square_rule (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
    (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
    (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
    ∀p≤pmax,RecipeSquareResidualRule j J h P M Nmax p (b p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih=>
    intro hpmax
    cases p with
    | zero=>exact residual_square_rule_base C hP hp hm (b 0) (hA 0 hpmax)
    | succ k=>
      exact residual_square_rule_step C hP hn hJ b hmono k (hpmax.trans_lt hM)
        (hA k (by omega)) (h2 k (by omega)) (hstep k (by omega))
        (fun r hr=>ih r hr (by omega))

theorem uniform_ordinary_square_residual (p N : ℕ) {K : ℝ} (hK : 2≤K) (hM : p<M)
    (C : FiniteRecipeControl j J h M (N+2*p) (residualCoefficientBudget j K p 0))
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformSquare P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hK0 : 0≤K := by linarith
  have hb:=residualCoefficientBudget_antitone j hK0 p
  have HH:=uniform_residual_square_rule C hP hp hm hn hJ (residualCoefficientBudget j K p) hb p hM
    (fun r _=>hb (Nat.zero_le r)) (fun r _=>hK.trans (residualCoefficientBudget_ge j hK0 p r))
    (fun k hk=>le_of_eq (residualCoefficientBudget_step j K hk)) p le_rfl D N
  apply HH _ le_rfl
  simpa [residualCoefficientBudget] using H

end SKGapCutoff.Recipe

end
end

end OAI
