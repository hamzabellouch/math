import Mathlib
import OAI.Probability.LogConcave.Numerics.CompileDeclaredRootShift

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def BaseVariation (B : ℝ) (x y : X) : MeanTree X d → Prop
  | .node _ b _ _ _ C => ‖b x-b y‖ ≤ B ∧ ∀i,BaseVariation B x y (C i)

lemma compileTerms_variation (D : ℝ) (V : Point d → ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (B : Fin k → ℝ) (L H : ℝ) (hL : 0≤L) (x y : X)
    (hc : ∀i g,‖(C i).eval V x g-(C i).eval V y g‖ ≤ B i)
    (hm : ∀i u v g,‖(M i).program.run V (u,g)-(M i).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (he : ∀g,‖E.eval V x g-E.eval V y g‖ ≤ H) :
    ∀g,‖(compileTerms D k a C M E).eval V x g-(compileTerms D k a C M E).eval V y g‖ ≤
      (∑i,|a i| *(L*B i))+H := by
  induction k with
  | zero => simpa [compileTerms] using he
  | succ k ih =>
    intro g
    have ht := ih (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ)
      (fun i => B i.succ) (fun i => hc i.succ) (fun i => hm i.succ) (rightBlock g)
    have hhead := (hm 0 _ _ ((M 0).damping D (middleBlock g))).trans
      (mul_le_mul_of_nonneg_left (hc 0 (leftBlock g)) hL)
    change ‖a 0 • _+_-(a 0 • _+_)‖ ≤ _
    rw [show ∀u v w z : Point d,u+v-(w+z)=(u-w)+(v-z) by intros; abel]
    apply (norm_add_le _ _).trans
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,Fin.sum_univ_succ]
    have hh := mul_le_mul_of_nonneg_left hhead (abs_nonneg (a 0))
    linarith

theorem compileDeclared_variation {D A L B : ℝ} (hL : 0≤L) (hB : 0≤B)
    (hLA : L*A ≤ 1) (V : Point d → ℝ) (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P r τ → ∀u v g,‖(M r τ).program.run V (u,g)-(M r τ).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (E : MeanTree X d) (n : ℝ) (x y : X) (hE : BaseVariation B x y E)
    (hw : weight E ≤ A) (hcenters : centersBound A E) (hr : ShiftReady D A P E n) :
    ∀g,‖(compileDeclared D A M E n).eval V x g-(compileDeclared D A M E n).eval V y g‖ ≤
      ((depth E:ℝ)+1)*B := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hc (i : Fin k) (g) := ih i (r i/(2*D)) (hE.2 i) (hcenters i).1 (hcenters i).2 (hr i).2.2 g
    have hd (i : Fin k) : (depth (C i):ℝ)+1 ≤ (depth (node k b hb a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hct (i : Fin k) (g) : ‖(compileDeclared D A M (C i) (r i/(2*D))).eval V x g-
        (compileDeclared D A M (C i) (r i/(2*D))).eval V y g‖ ≤ (depth (node k b hb a r C):ℝ)*B :=
      (hc i g).trans (mul_le_mul_of_nonneg_right (hd i) hB)
    have hh := compileTerms_variation D V k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun _ => (depth (node k b hb a r C):ℝ)*B) L B hL x y hct
      (fun i => hm _ _ (hr i).2.1) (fun g => by simpa only [Expression.eval,add_sub_add_right_eq_sub] using hE.1)
    intro g
    apply (hh g).trans
    rw [←Finset.sum_mul]
    have hs : (∑i,|a i|)*L ≤ 1 := calc
      _ ≤ A*L := mul_le_mul_of_nonneg_right hw hL
      _ ≤ 1 := by simpa only [mul_comm] using hLA
    have hd0 : 0 ≤ (depth (node k b hb a r C):ℝ)*B := by positivity
    have hmult := mul_le_mul_of_nonneg_right hs hd0
    nlinarith

theorem compileDeclaredRoot_variation {D A Af L Li B Bf : ℝ} (hL : 0≤L) (hLi : 0≤Li)
    (hB : 0≤B) (hLA : Li*A ≤ 1) (V : Point d → ℝ)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖ ≤ Li*‖u-v‖)
    (E : MeanTree X d) (n : ℝ) (x y : X)
    (hE : BaseVariation B x y E) (hbase : ‖base E x-base E y‖ ≤ Bf)
    (hw : weight E ≤ Af) (hcenters : centersBound A E)
    (hr : RootShiftReady D A Af (P true) (P false) E n) :
    ∀g,‖(compileDeclaredRoot D A Af (M true) (M false) E n).eval V x g-
      (compileDeclaredRoot D A Af (M true) (M false) E n).eval V y g‖ ≤
      Af*L*(depth E:ℝ)*B+Bf := by
  cases E with | node k b hb a r C =>
    have hd (i : Fin k) : (depth (C i):ℝ)+1 ≤ (depth (node k b hb a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hc (i : Fin k) (g) := (compileDeclared_variation hLi hB hLA V (P false) (M false)
      hmi (C i) (r i/(2*D)) x y (hE.2 i) (hcenters i).1 (hcenters i).2 (hr i).2.2 g).trans
      (mul_le_mul_of_nonneg_right (hd i) hB)
    have hh := compileTerms_variation D V k a (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun _ => (depth (node k b hb a r C):ℝ)*B) L Bf hL x y hc
      (fun i => hm _ _ (hr i).2.1) (fun g => by simpa only [Expression.eval,add_sub_add_right_eq_sub,base] using hbase)
    intro g
    apply (hh g).trans
    rw [←Finset.sum_mul]
    change (∑ i, |a i|) ≤ Af at hw
    have hm := mul_le_mul_of_nonneg_right hw (show 0 ≤ L*((depth (node k b hb a r C):ℝ)*B) by positivity)
    nlinarith
end LogConcaveSampling.MeanTree

end

end

end OAI
