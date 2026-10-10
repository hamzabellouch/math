import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ForceExpressions

namespace OAI

noncomputable section
namespace VelocityDetection.Effective.RationalBox
open Set Filter Function
open scoped Topology BigOperators
variable {n : ℕ} (Q : RationalBox n)

theorem eventually_safe (e : Expr n) (he : ∀ x ∈ Q.carrier, e.Valid x) :
    ∀ᶠ k in atTop, ∀ j : Fin n → Fin (k+2), e.safe (Q.cell k j) k = true := by
  classical
  by_contra h
  have hh := frequently_atTop.mp (not_eventually.mp h)
  have hbad : ∀ k, ∃ m, k ≤ m ∧ ∃ j : Fin n → Fin (m+2), e.safe (Q.cell m j) m ≠ true := by
    intro k
    obtain ⟨m,hm,hh⟩ := hh k
    exact ⟨m,hm,not_forall.mp hh⟩
  choose κ hκle j hj using hbad
  have hκ : Tendsto κ atTop atTop := tendsto_atTop_mono hκle tendsto_id
  obtain ⟨x,hx,σ,hσ,hlim⟩ := Q.compact_carrier.tendsto_subseq (fun k => Q.center_mem (κ k) (j k))
  have hprec := hκ.comp hσ.tendsto_atTop
  have hc (i) : Ball.Converges (fun k => Q.cell (κ (σ k)) (j (σ k)) i) (x i) := by
    refine ⟨?_,Q.radius_tendsto hprec (fun k => j (σ k)) i⟩
    exact (continuous_apply i).continuousAt.tendsto.comp hlim
  have hs := (e.round_converges_precision hc (he x hx) hprec).2
  obtain ⟨k,hk⟩ := hs.exists
  exact hj (σ k) hk

def boundTrial (e : Expr n) (is : List (Fin n)) (k : ℕ) : Option ℚ :=
  if ∀ j : Fin n → Fin (k+2), (e.jet is).safe (Q.cell k j) k = true then
    some (∑ j : Fin n → Fin (k+2),
      (|((e.jet is).round (Q.cell k j) k).center| + |((e.jet is).round (Q.cell k j) k).radius|))
  else none

theorem boundTrial_correct (e : Expr n) (is : List (Fin n)) (k : ℕ) {C : ℚ}
    (h : Q.boundTrial e is k = some C) : 0 ≤ C ∧
      ∀ x ∈ Q.carrier, e.Valid x → |mixedD is (fun y => e.eval y) x| ≤ (C:ℝ) := by
  unfold boundTrial at h
  split_ifs at h with hs
  · cases Option.some.inj h
    refine ⟨Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)),?_⟩
    intro x hx he
    obtain ⟨j,hj⟩ := Q.covers k hx
    rw [e.mixedD_eval he is]
    have hbound := ((e.jet is).round_certifies hj k (hs j)).2
    have htri := abs_add_le ((e.jet is).eval x-(((e.jet is).round (Q.cell k j) k).center:ℝ))
      (((e.jet is).round (Q.cell k j) k).center:ℝ)
    simp only [sub_add_cancel] at htri
    have hsum := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n → Fin (k+2) =>
        |((e.jet is).round (Q.cell k j) k).center| + |((e.jet is).round (Q.cell k j) k).radius|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    have hsum' := Rat.cast_le (K := ℝ).mpr hsum
    simp only [Rat.cast_add,Rat.cast_abs] at hsum'
    linarith [le_abs_self (((e.jet is).round (Q.cell k j) k).radius:ℝ)]

theorem boundTrial_terminates (e : Expr n) (is : List (Fin n))
    (he : ∀ x ∈ Q.carrier, e.Valid x) : ∃ k C, Q.boundTrial e is k = some C := by
  obtain ⟨k,hk⟩ := (Q.eventually_safe (e.jet is) (fun x hx => e.valid_jet (he x hx) is)).exists
  refine ⟨k,∑ j : Fin n → Fin (k+2),
    (|((e.jet is).round (Q.cell k j) k).center| + |((e.jet is).round (Q.cell k j) k).radius|),?_⟩
  simp only [boundTrial,ite_eq_left hk]

end VelocityDetection.Effective.RationalBox
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Function Turing
variable {b N : ℕ} [NeZero b] [NeZero N]

def boxTimeCutoff (Q : RationalBox 5) : ℕ :=
  letI := neZeroFive
  ⌈Q.upper 1+1⌉₊

def boxSpaceCutoff (Q : RationalBox 5) : ℕ :=
  letI := neZeroFive
  ⌈|Q.lower 2|+|Q.upper 2|+|Q.lower 3|+|Q.upper 3|+2⌉₊

theorem box_good (d : Domain) (Q : RationalBox 5) (hQ : 0 < Q.lower 0)
    {x : Fin 5 → ℝ} (hx : x ∈ Q.carrier) :
    Good d (boxSpaceCutoff Q) (boxTimeCutoff Q) x := by
  have hν0 : (0:ℝ) < (Q.lower 0:ℝ) := by exact_mod_cast hQ
  have hν : 0 < x 0 := lt_of_lt_of_le hν0 (hx.1 0)
  have ht : (Q.upper 1:ℝ)+1 ≤ boxTimeCutoff Q := by
    exact_mod_cast (Nat.le_ceil (Q.upper 1+1))
  have hR : |(Q.lower 2:ℝ)|+|(Q.upper 2:ℝ)|+|(Q.lower 3:ℝ)|+|(Q.upper 3:ℝ)|+2 ≤
      boxSpaceCutoff Q := by
    exact_mod_cast (Nat.le_ceil (|Q.lower 2|+|Q.upper 2|+|Q.lower 3|+|Q.upper 3|+2))
  refine ⟨hν,by linarith [hx.2 1],fun _ => ?_⟩
  have hi (i) : |x i| ≤ |(Q.lower i:ℝ)|+|(Q.upper i:ℝ)| := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1 i,hx.2 i,neg_abs_le (Q.lower i:ℝ),le_abs_self (Q.upper i:ℝ),
      abs_nonneg (Q.lower i:ℝ),abs_nonneg (Q.upper i:ℝ)]
  have hn : ‖(![x 2,x 3] : Coord 2)‖ ≤
      |(Q.lower 2:ℝ)|+|(Q.upper 2:ℝ)|+|(Q.lower 3:ℝ)|+|(Q.upper 3:ℝ)| := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i; fin_cases i <;> simp only [Real.norm_eq_abs] <;> change |x _| ≤ _
    · linarith [hi 2,abs_nonneg (Q.lower 3:ℝ),abs_nonneg (Q.upper 3:ℝ)]
    · linarith [hi 3,abs_nonneg (Q.lower 2:ℝ),abs_nonneg (Q.upper 2:ℝ)]
  linarith

def runBoundTrial (d : Domain) (B : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5) (k : ℕ) : Option ℚ :=
  Q.boundTrial (force d B (boxSpaceCutoff Q) (boxTimeCutoff Q) M w i) is k

theorem runBoundTrial_correct (d : Domain) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5) (hQ : 0 < Q.lower 0)
    (k : ℕ) {C : ℚ} (h : runBoundTrial d SmoothBump.bound M w i is Q k = some C) :
    0 ≤ C ∧ ∀ x ∈ Q.carrier,
      |mixedD is (forceFunction (fun ν => analyticForce d ν M w) i) x| ≤ (C:ℝ) := by
  obtain ⟨hC,hbound⟩ := Q.boundTrial_correct _ is k h
  refine ⟨hC,fun x hx => ?_⟩
  have hg := box_good d Q hQ hx
  rw [← mixedD_congr (force_germ d _ _ M w hg i) is]
  exact hbound x hx (valid_force d _ _ M w hg.1 i)

theorem runBoundTrial_terminates (d : Domain) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5) (hQ : 0 < Q.lower 0) :
    ∃ k C, runBoundTrial d SmoothBump.bound M w i is Q k = some C :=
  Q.boundTrial_terminates _ is (fun _ hx => valid_force d _ _ M w (box_good d Q hQ hx).1 i)

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Turing

structure Program (b N : ℕ) [NeZero b] [NeZero N] where
  derivativeBound : ℕ
  table : TM0.Machine (Fin b) (Fin N)
  input : List (Fin b)

def compile {b N : ℕ} [NeZero b] [NeZero N] (B : ℕ) (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    Program b N := ⟨B,M,w⟩

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe.Program
open Turing
variable {b N : ℕ} [NeZero b] [NeZero N]

def valueTrial (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (q : Fin 5 → ℕ → ℚ) (ε : ℚ) (k : ℕ) : Option ℚ :=
  runTrial d P.derivativeBound P.table P.input i is q ε k

def boundTrial (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (Q : RationalBox 5) (k : ℕ) : Option ℚ :=
  runBoundTrial d P.derivativeBound P.table P.input i is Q k

noncomputable def evaluate (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (q : Fin 5 → ℕ → ℚ) (ε : ℚ) : Part ℚ := Nat.rfindOpt (P.valueTrial d i is q ε)

noncomputable def derivativeBounds (P : Program b N) (d : Domain) (i : Fin 3)
    (is : List (Fin 5)) (Q : RationalBox 5) : Part ℚ := Nat.rfindOpt (P.boundTrial d i is Q)

def Represents (P : Program b N) (d : Domain) (F : ℝ → VectorField 3) : Prop :=
  letI := neZeroFive
  (∀ (i : Fin 3) (is : List (Fin 5)) (q : Fin 5 → ℕ → ℚ) (x : Fin 5 → ℝ),
    Names q x → 0 < x 0 → ∀ ε : ℚ, 0 < ε →
      (P.evaluate d i is q ε).Dom ∧
      ∀ r ∈ P.evaluate d i is q ε,
        |mixedD is (forceFunction F i) x-(r:ℝ)| ≤ (ε:ℝ)) ∧
  (∀ (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5), 0 < Q.lower 0 →
    (P.derivativeBounds d i is Q).Dom ∧
    ∀ C ∈ P.derivativeBounds d i is Q, 0 ≤ C ∧
      ∀ x ∈ Q.carrier, |mixedD is (forceFunction F i) x| ≤ (C:ℝ))

theorem compile_represents (d : Domain) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) :
    (compile SmoothBump.bound M w).Represents d (fun ν => analyticForce d ν M w) := by
  constructor
  · intro i is q x hq hν ε hε
    constructor
    · apply Nat.rfindOpt_dom.mpr
      obtain ⟨k,r,hr⟩ := runTrial_terminates d M w i is hq hν hε
      exact ⟨k,r,hr⟩
    · intro r hr
      obtain ⟨k,hk⟩ := Nat.rfindOpt_spec hr
      exact runTrial_correct d M w i is hq hν ε k hk
  · intro i is Q hQ
    constructor
    · apply Nat.rfindOpt_dom.mpr
      obtain ⟨k,C,hC⟩ := runBoundTrial_terminates d M w i is Q hQ
      exact ⟨k,C,hC⟩
    · intro C hC
      obtain ⟨k,hk⟩ := Nat.rfindOpt_spec hC
      exact runBoundTrial_correct d M w i is Q hQ k hk

end VelocityDetection.Effective.MachineRecipe.Program
end

noncomputable section
namespace VelocityDetection.Effective
open Turing

def ComputableReal (x : ℝ) : Prop :=
  ∃ q : ℕ → ℚ, Computable q ∧ ∀ k, |x-(q k:ℝ)| ≤ (accuracy k:ℝ)

end VelocityDetection.Effective
end

end OAI
