import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TerminalMean
import OAI.Probability.LogConcave.Sampling.TerminalMean

namespace OAI

section
section
noncomputable section
open MeasureTheory

namespace LogConcaveSampling.OracleCompiler

inductive Expression (X : Type*) [MeasurableSpace X] (d : ℕ) where
  | noise (base : X → Point d) (measurable_base : Measurable base) (noise : ℝ)
  | add (a : ℝ) (center : Expression X d) (k q : ℕ)
      (child : Program (Point d × (Fin k → Point d)) d q (Point d))
      (P : (Fin k → Point d) → (Fin k → Point d)) (measurable_P : Measurable P)
      (rest : Expression X d)

namespace Expression
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

@[reducible] def slots : Expression X d → ℕ
  | .noise .. => 1
  | .add _ C k _ _ _ _ T => C.slots + (k + T.slots)

@[reducible] def calls : Expression X d → ℕ
  | .noise .. => 0
  | .add _ C _ q _ _ _ T => C.calls + (q + T.calls)

def leftBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin c → Point d :=
  fun i => g (Fin.castAdd (k+t) i)
def middleBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin k → Point d :=
  fun i => g (Fin.natAdd c (Fin.castAdd t i))
def rightBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin t → Point d :=
  fun i => g (Fin.natAdd c (Fin.natAdd k i))

lemma measurable_leftBlock (c k t : ℕ) : Measurable (leftBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold leftBlock
  fun_prop
lemma measurable_middleBlock (c k t : ℕ) : Measurable (middleBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold middleBlock
  fun_prop
lemma measurable_rightBlock (c k t : ℕ) : Measurable (rightBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold rightBlock
  fun_prop

def compile : (C : Expression X d) →
    Program (X × (Fin C.slots → Point d)) d C.calls (Point d)
  | .noise b hb n => Program.pure (fun z => b z.1+n • z.2 0) (by fun_prop)
  | .add a C k q M P hP T => by
      let Ω := X × (Fin (C.slots+(k+T.slots)) → Point d)
      let A : Program Ω d C.calls (Point d) := C.compile.seedMap
        (fun z => (z.1,leftBlock z.2)) (by
          exact measurable_fst.prodMk ((measurable_leftBlock _ _ _).comp measurable_snd))
      let B : Program (Ω × Point d) d q (Point d) := M.seedMap
        (fun z => (z.2,P (middleBlock z.1.2))) (by
          exact measurable_snd.prodMk (hP.comp ((measurable_middleBlock _ _ _).comp
            (measurable_snd.comp measurable_fst))))
      let D : Program ((Ω × Point d) × Point d) d T.calls (Point d) :=
        (T.compile.seedMap (fun z => (z.1.1.1,rightBlock z.1.1.2)) (by
          exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_rightBlock _ _ _).comp (measurable_snd.comp
              (measurable_fst.comp measurable_fst))))).map
          (fun z => a • z.1.2+z.2) (by fun_prop)
      exact A.seq (B.seq D)

def eval (V : Point d → ℝ) : (C : Expression X d) → X → (Fin C.slots → Point d) → Point d
  | .noise b _ n, x, g => b x+n • g 0
  | .add a C _ _ M P _ T, x, g =>
      a • M.run V (C.eval V x (leftBlock g),P (middleBlock g))+
        T.eval V x (rightBlock g)

theorem compile_run (C : Expression X d) (V : Point d → ℝ)
    (x : X) (g : Fin C.slots → Point d) : C.compile.run V (x,g)=C.eval V x g := by
  induction C with
  | noise b hb n => rfl
  | add a C k q M P hP T hC hT =>
    simp only [compile,Program.seq_run,Program.seedMap_run,Program.map_run,eval]
    rw [hC,hT]

theorem measurable_eval (C : Expression X d) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) :
    Measurable (fun z : X × (Fin C.slots → Point d) => C.eval V z.1 z.2) := by
  have hr := C.compile.measurable_run V hV
  convert hr using 1
  funext z
  exact (compile_run C V z.1 z.2).symm

end Expression
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory

variable {Ω O R Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSpace R] [MeasurableSpace Ξ] {d q r : ℕ}

structure Equivariant (A : Program Ω d q O) (f : Ω → Ω) (τ : O → O) : Prop where
  query : ∀i ω h,A.query i (f ω,h)=A.query i (ω,h)
  output : ∀ω h,A.output (f ω,h)=τ (A.output (ω,h))

namespace Equivariant
variable {A : Program Ω d q O} {f : Ω → Ω} {τ : O → O}

theorem history (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    A.history V (f ω) n=A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Program.history,ih]
    split_ifs with hn
    · rw [hA.query]
    · rfl

theorem run (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) :
    A.run V (f ω)=τ (A.run V ω) := by
  unfold Program.run
  rw [hA.history,hA.output]

theorem executed_query (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω)
    (i : Fin q) :
    A.query i (f ω,A.history V (f ω) i.val)=A.query i (ω,A.history V ω i.val) := by
  rw [hA.history,hA.query]

theorem seq (hA : A.Equivariant f τ) {B : Program (Ω × O) d r R} {σ : R → R}
    (hB : B.Equivariant (fun z => (f z.1,τ z.2)) σ) : (A.seq B).Equivariant f σ := by
  constructor
  · intro i ω h
    refine Fin.addCases (fun _ => ?_) (fun j => ?_) i
    · simp only [Program.seq,Fin.addCases_left]
      exact hA.query _ _ _
    · simp only [Program.seq,Fin.addCases_right,hA.output]
      exact hB.query j (ω,A.output (ω,leftTrace h)) (rightTrace h)
  · intro ω h
    simp only [Program.seq,hA.output]
    exact hB.output (ω,A.output (ω,leftTrace h)) (rightTrace h)

theorem seedMap (hA : A.Equivariant f τ) (g : Ξ → Ω) (hg : Measurable g)
    (f' : Ξ → Ξ) (hf : ∀ξ,g (f' ξ)=f (g ξ)) : (A.seedMap g hg).Equivariant f' τ := by
  constructor
  · intro i ξ h
    simpa only [Program.seedMap,hf] using hA.query i (g ξ) h
  · intro ξ h
    simpa only [Program.seedMap,hf] using hA.output (g ξ) h

theorem map (hA : A.Equivariant f τ) (g : Ω × O → R) (hg : Measurable g)
    (σ : R → R) (he : ∀ω x,g (f ω,τ x)=σ (g (ω,x))) :
    (A.map g hg).Equivariant f σ := by
  constructor
  · exact hA.query
  · intro ω h
    simp only [Program.map,hA.output,he]

end Equivariant

lemma pure_equivariant (g : Ω → O) (hg : Measurable g) (f : Ω → Ω) (τ : O → O)
    (he : ∀ω,g (f ω)=τ (g ω)) : (Program.pure (d:=d) g hg).Equivariant f τ := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro ω h
    exact he ω

lemma oneQuery_equivariant (x : Ω → Point d) (hx : Measurable x)
    (g : Ω × Reply d → O) (hg : Measurable g) (f : Ω → Ω) (τ : O → O)
    (he : ∀ω,x (f ω)=x ω) (hout : ∀ω a,g (f ω,a)=τ (g (ω,a))) :
    (Program.oneQuery x hx g hg).Equivariant f τ := by
  constructor
  · intro i ω h
    exact he ω
  · intro ω h
    exact hout ω (h 0)

end LogConcaveSampling.OracleCompiler.Program

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def shiftSlots {n : ℕ} (v : Fin n → ℝ) (Δ : Point d) (g : Fin n → Point d) : Fin n → Point d :=
  fun i => g i+v i • Δ

def moveSeed {n : ℕ} (f : X → X) (v : Fin n → ℝ) (Δ : Point d)
    (z : X × (Fin n → Point d)) : X × (Fin n → Point d) := (f z.1,shiftSlots v Δ z.2)

lemma leftBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    leftBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots u Δ (leftBlock g) := by
  ext i
  simp [leftBlock,shiftSlots]
lemma middleBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    middleBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots v Δ (middleBlock g) := by
  ext i
  simp [middleBlock,shiftSlots]
lemma rightBlock_shift {c k t : ℕ} (u : Fin c → ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ)
    (Δ : Point d) (g : Fin (c+(k+t)) → Point d) :
    rightBlock (shiftSlots (Fin.append u (Fin.append v w)) Δ g)=shiftSlots w Δ (rightBlock g) := by
  ext i
  simp [rightBlock,shiftSlots]

lemma noise_equivariant (b : X → Point d) (hb : Measurable b) (n c : ℝ)
    (f : X → X) (Δ : Point d) (he : ∀x,b (f x)=b x+c • Δ) :
    (noise b hb n).compile.Equivariant (moveSeed f (fun _ => 0) Δ) (fun y => y+c • Δ) := by
  apply Program.pure_equivariant
  intro z
  simp [moveSeed,shiftSlots,he]
  abel

lemma add_equivariant (a : ℝ) (C T : Expression X d) {k q : ℕ}
    (M : Program (Point d × (Fin k → Point d)) d q (Point d))
    (P : (Fin k → Point d) → (Fin k → Point d)) (hP : Measurable P)
    (f : X → X) (Δ : Point d) (u : Fin C.slots → ℝ) (v : Fin k → ℝ)
    (w : Fin T.slots → ℝ) (c t : ℝ)
    (hC : C.compile.Equivariant (moveSeed f u Δ) (fun y => y+c • Δ))
    (hM : (M.seedMap (fun z : Point d × (Fin k → Point d) => (z.1,P z.2))
      (measurable_fst.prodMk (hP.comp measurable_snd))).Equivariant
        (moveSeed (fun y => y+c • Δ) v Δ) id)
    (hT : T.compile.Equivariant (moveSeed f w Δ) (fun y => y+t • Δ)) :
    (add a C k q M P hP T).compile.Equivariant
      (moveSeed f (Fin.append u (Fin.append v w)) Δ) (fun y => y+t • Δ) := by
  let Ω := X × (Fin (C.slots+(k+T.slots)) → Point d)
  let F : Ω → Ω := moveSeed f (Fin.append u (Fin.append v w)) Δ
  let A : Program Ω d C.calls (Point d) := C.compile.seedMap
    (fun z => (z.1,leftBlock z.2))
    (measurable_fst.prodMk ((measurable_leftBlock _ _ _).comp measurable_snd))
  have hA : A.Equivariant F (fun y => y+c • Δ) := by
    apply hC.seedMap
    intro z
    simp only [F,moveSeed,leftBlock_shift]
  let B : Program (Ω × Point d) d q (Point d) := M.seedMap
    (fun z => (z.2,P (middleBlock z.1.2)))
    (measurable_snd.prodMk (hP.comp ((measurable_middleBlock _ _ _).comp
      (measurable_snd.comp measurable_fst))))
  let G : (Ω × Point d) → (Ω × Point d) := fun z => (F z.1,z.2+c • Δ)
  have hB : B.Equivariant G id := by
    constructor
    · intro i z h
      have H := hM.query i (z.2,middleBlock z.1.2) h
      simpa only [B,Program.seedMap,G,F,moveSeed,middleBlock_shift] using H
    · intro z h
      have H := hM.output (z.2,middleBlock z.1.2) h
      simpa only [B,Program.seedMap,G,F,moveSeed,middleBlock_shift] using H
  let D : Program ((Ω × Point d) × Point d) d T.calls (Point d) :=
    (T.compile.seedMap (fun z => (z.1.1.1,rightBlock z.1.1.2))
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_rightBlock _ _ _).comp (measurable_snd.comp
          (measurable_fst.comp measurable_fst))))).map
      (fun z => a • z.1.2+z.2) (by fun_prop)
  have hD : D.Equivariant (fun z => (G z.1,id z.2)) (fun y => y+t • Δ) := by
    apply Program.Equivariant.map
    · apply hT.seedMap
      intro z
      simp only [G,F,moveSeed,rightBlock_shift]
    · intro z y
      dsimp
      abel
  exact hA.seq (hB.seq hD)

end LogConcaveSampling.OracleCompiler.Expression

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {d : ℕ}

def FixedSeedLip (C : Expression X d) (V : Point d → ℝ) (K : ℝ≥0) : Prop :=
  ∀g,LipschitzWith K (fun x => C.eval V x g)

lemma noise_fixedSeed_lip (b : X → Point d) (hb : Measurable b) (n : ℝ)
    (V : Point d → ℝ) {K : ℝ≥0} (h : LipschitzWith K b) :
    FixedSeedLip (noise b hb n) V K := by
  intro g
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [eval,dist_add_right] using h.dist_le_mul x y

lemma add_fixedSeed_lip (a : ℝ) (C T : Expression X d) {k q : ℕ}
    (M : Program (Point d × (Fin k → Point d)) d q (Point d))
    (P : (Fin k → Point d) → (Fin k → Point d)) (hP : Measurable P)
    (V : Point d → ℝ) {K L J : ℝ≥0}
    (hC : FixedSeedLip C V K) (hT : FixedSeedLip T V J)
    (hM : ∀g,LipschitzWith L (fun x => M.run V (x,g))) :
    FixedSeedLip (add a C k q M P hP T) V (‖a‖₊*(L*K)+J) := by
  intro g
  have hN := (hM (P (middleBlock g))).comp (hC (leftBlock g))
  have hS : LipschitzWith (‖a‖₊*(L*K)) (fun x =>
      a • M.run V (C.eval V x (leftBlock g),P (middleBlock g))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_smul₀]
    exact (mul_le_mul_of_nonneg_left (hN.dist_le_mul x y) (norm_nonneg a)).trans_eq
      (by simp only [NNReal.coe_mul,coe_nnnorm]; ring)
  exact hS.add (hT (rightBlock g))

lemma FixedSeedLip.compiled {C : Expression X d} {V : Point d → ℝ} {K : ℝ≥0}
    (h : FixedSeedLip C V K) (g : Fin C.slots → Point d) :
    LipschitzWith K (fun x => C.compile.run V (x,g)) := by
  simpa only [compile_run] using h g
end LogConcaveSampling.OracleCompiler.Expression

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open scoped NNReal

variable {d : ℕ} {V : Point d → ℝ} {K : ℝ≥0}

lemma terminalMean_fixedSeed_lip (hV : LipschitzWith K (gradient V))
    (r σ : ℝ) (g : Fin 2 → Point d) :
    LipschitzWith K (fun x => (terminalMean d r σ).run V (x,g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [terminalMean_run,dist_add_right]
  simpa only [dist_add_right] using hV.dist_le_mul (x+r • g 0) (y+r • g 0)

lemma terminalSample_fixedSeed_lip (hV : LipschitzWith K (gradient V))
    (r η : ℝ) (g : Fin 3 → Point d) :
    LipschitzWith (‖r‖₊*K) (fun x => (terminalSample d r η).run V (x,g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [terminalSample_run,dist_add_right,dist_sub_left,dist_smul₀,
    NNReal.coe_mul,coe_nnnorm]
  have hh := hV.dist_le_mul (x+r • g 0) (y+r • g 0)
  rw [dist_add_right] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg r)]

end LogConcaveSampling.SeedCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

lemma split_slots_preserving (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving
      (fun g : Fin (c+k) → E =>
        ((fun i : Fin c => g (Fin.castAdd k i)),fun i : Fin k => g (Fin.natAdd c i)))
      (Measure.pi fun _ => μ) ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ)) := by
  have H := (measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ Fin k => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (c+k) => μ) finSumFinEquiv).symm
  convert H using 1
  rfl

lemma three_blocks_preserving (μ : Measure E) [SigmaFinite μ] (c k t : ℕ) :
    MeasurePreserving
      (fun g : Fin (c+(k+t)) → E =>
        ((fun i : Fin c => g (Fin.castAdd (k+t) i)),
          ((fun i : Fin k => g (Fin.natAdd c (Fin.castAdd t i))),
            fun i : Fin t => g (Fin.natAdd c (Fin.natAdd k i)))))
      (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin c => μ).prod
        ((Measure.pi fun _ : Fin k => μ).prod (Measure.pi fun _ : Fin t => μ))) := by
  exact ((MeasurePreserving.id (Measure.pi fun _ : Fin c => μ)).prod
    (split_slots_preserving μ k t)).comp (split_slots_preserving μ c (k+t))

lemma three_blocks_with_anchor {A : Type*} [MeasurableSpace A] (ν : Measure A) [SFinite ν]
    (μ : Measure E) [SigmaFinite μ] (c k t : ℕ) :
    (ν.prod (Measure.pi fun _ : Fin (c+(k+t)) => μ)).map
      (fun z => (z.1,
        ((fun i : Fin c => z.2 (Fin.castAdd (k+t) i)),
          ((fun i : Fin k => z.2 (Fin.natAdd c (Fin.castAdd t i))),
            fun i : Fin t => z.2 (Fin.natAdd c (Fin.natAdd k i))))))=
      ν.prod ((Measure.pi fun _ : Fin c => μ).prod
        ((Measure.pi fun _ : Fin k => μ).prod (Measure.pi fun _ : Fin t => μ))) := by
  exact ((MeasurePreserving.id ν).prod (three_blocks_preserving μ c k t)).map_eq

end LogConcaveSampling.OracleCompiler.Expression

end

end

end

end OAI
