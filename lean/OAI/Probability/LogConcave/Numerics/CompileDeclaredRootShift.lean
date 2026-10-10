import Mathlib
import OAI.Probability.LogConcave.Numerics.Cost

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def compileDeclaredRootShift (D A Af : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d) :
    (E : MeanTree X d) → (n : ℝ) → DriftData E → Fin (compileDeclaredRoot D A Af Mf Mi E n).slots → ℝ
  | .node k b hb a r C,n,p =>
    compileTermsShift D k a (fun i => compileDeclared D A Mi (C i) (r i/(2*D)))
      (fun i => Mf (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun i => compileDeclaredShift D A Mi (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (Mf (r i) (declaredNoise n Af)))
      (fun _ => 0)

def RootShiftReady (D A Af : ℝ) (Pf Pi : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ _ r C,n => ∀i,r i≠0 ∧ Pf (r i) (declaredNoise n Af) ∧ ShiftReady D A Pi (C i) (r i/(2*D))

theorem compileDeclaredRoot_equivariant (D A Af : ℝ) (hD : 0<D)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ D^2)
    (hM : ∀s r τ,P s r τ → ∀Δ,(M s r τ).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (M s r τ).shift Δ) id)
    (f : Point d → X → X) (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hp : DriftValid f E p) (hr : RootShiftReady D A Af (P true) (P false) E n) :
    ∀Δ,(compileDeclaredRoot D A Af (M true) (M false) E n).compile.Equivariant
      (moveSeed (f Δ) (compileDeclaredRootShift D A Af (M true) (M false) E n p) Δ)
      (fun y => y+p.root E • Δ) := by
  cases E with | node k b hb a r C =>
    intro Δ
    apply compileTerms_equivariant
    · intro i
      exact compileDeclared_equivariant D A hD (P false) (M false) (hv false) (hM false)
        f (C i) (r i/(2*D)) (p.2 i) (hp.2 i) (hr i).2.2 Δ
    · intro i
      exact transformed_mean_equivariant (M true (r i) (declaredNoise n Af)).program
        (hr i).1 _ _ ((normalized_shift_bound hD _ (hv _ _ _ (hr i).2.1)).trans_lt (by norm_num))
        (hM _ _ _ (hr i).2.1) ((p.2 i).root (C i)) Δ
    · exact noise_equivariant b hb _ p.1 (f Δ) Δ (hp.1 Δ)

theorem compileDeclaredRoot_size (D A Af : ℝ)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (S Q : ℕ) (hM : ∀s r τ,P s r τ → (M s r τ).slots ≤ S ∧ (M s r τ).calls ≤ Q)
    (E : MeanTree X d) (n : ℝ) (hr : RootShiftReady D A Af (P true) (P false) E n) :
    (compileDeclaredRoot D A Af (M true) (M false) E n).slots ≤ 1+cost E*(S+1) ∧
      (compileDeclaredRoot D A Af (M true) (M false) E n).calls ≤ cost E*Q := by
  cases E with | node k b hb a r C =>
    have hc (i) := compileDeclared_size D A (P false) (M false) S Q (hM false) (C i) (r i/(2*D)) (hr i).2.2
    have hm (i) := hM true (r i) (declaredNoise n Af) (hr i).2.1
    constructor
    · simp only [compileDeclaredRoot,slots_compileTerms,Expression.slots,cost]
      apply Nat.add_le_add_left
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).1
      have h₂ := (hm i).1
      nlinarith
    · simp only [compileDeclaredRoot,calls_compileTerms,Expression.calls,zero_add,cost,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).2
      have h₂ := (hm i).2
      nlinarith

theorem compileDeclaredRootShift_energy_bound {D A Af R B : ℝ} (hD : 0<D) (hR : 0≤R) (hB : 0≤B)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ D^2)
    (hBv : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2) ≤ B)
    (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hr : RootShiftReady D A Af (P true) (P false) E n) (hg : DriftBound R E p) :
    (∑j,compileDeclaredRootShift D A Af (M true) (M false) E n p j^2) ≤ (cost E:ℝ)*(4*R^2*B) := by
  cases E with | node k b hb a r C =>
    change (∑j,compileTermsShift D k a (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun i => compileDeclaredShift D A (M false) (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)))
      (fun _ => 0) j^2) ≤ _
    rw [compileTermsShift_energy]
    simp only [zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,zero_add,cost,Nat.cast_sum,Nat.cast_add,Nat.cast_one,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hc := compileDeclaredShift_energy_bound hD hR hB (P false) (M false) (hv false) (hBv false)
      (C i) (r i/(2*D)) (p.2 i) (hr i).2.2 (hg i).2
    have hi := inverse_shift_energy (fun j => (M true (r i) (declaredNoise n Af)).shift j/(2*D))
      (M true (r i) (declaredNoise n Af)).shift (normalized_shift_bound hD _ (hv _ _ _ (hr i).2.1))
      (((p.2 i).root (C i))/(r i))
    have hs := hBv _ _ _ (hr i).2.1
    have hh : (((p.2 i).root (C i))/(r i))^2 ≤ R^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hg i).1 2
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4)) hB
    have hv' := mul_le_mul_of_nonneg_left hs (show 0≤4*(((p.2 i).root (C i))/(r i))^2 by positivity)
    change (∑j,compileDeclaredShift D A (M false) (C i) (r i/(2*D)) (p.2 i) j^2)+
      (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)) j^2) ≤ _
    change (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M true (r i) (declaredNoise n Af)) j^2) ≤ _ at hi
    nlinarith
end LogConcaveSampling.MeanTree

end

end

end OAI
