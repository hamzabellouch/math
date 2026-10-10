import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkIteration

namespace OAI

/-! Exact rational coefficients for every stage of the global fork reduction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMARationalForkNetwork (c : ℕ) where
  graph : QMAForkNetwork c
  weight : graph.Edge → ℚ
  active : (Σ i, Fin (graph.degree i)) → ℚ
  constant : ℚ

namespace QMARationalForkNetwork
variable {c : ℕ}

def real (G : QMARationalForkNetwork c) : QMAWeightedForkNetwork c where
  graph := G.graph
  weight := fun e => G.weight e
  active := fun p => G.active p
  constant := G.constant

def pairWeight (G : QMARationalForkNetwork c) (b : Fin 2) (e : Fin G.graph.state.ports.pairCount) : ℚ :=
  G.active (qmaForkPairedPort G.graph.degree (G.graph.state.ports.pairEquiv.symm e,b))

def retainedWeight (G : QMARationalForkNetwork c) :
    G.graph.Edge ⊕ QMAForkRemainder G.graph.degree → ℚ :=
  Sum.elim G.weight (fun p => G.active (qmaForkRemainingPort G.graph.degree p))

def scale (G : QMARationalForkNetwork c) (N : ℚ) : ℚ :=
  let B := 3*(∑ a, |G.retainedWeight a|)+|G.constant|
  let A := 3*∑ e, (1+2*|G.pairWeight 0 e|+2*|G.pairWeight 1 e|)
  let D := B+12*∑ e, (1+|G.pairWeight 0 e|+|G.pairWeight 1 e|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

theorem scale_cast (G : QMARationalForkNetwork c) (N : ℚ) :
    (G.scale N : ℝ) = G.real.scale N := by
  dsimp only [real]
  simp only [scale,QMAWeightedForkNetwork.scale,retainedWeight,pairWeight,
    QMAForkState.retainedWeight,QMAForkState.pairWeight,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,qmaRoutingScale]
  push_cast
  rfl

def next (G : QMARationalForkNetwork c) (N : ℚ) : QMARationalForkNetwork c where
  graph := G.graph.next
  weight := fun e => match e with
    | .inl (.inl a) => G.weight a
    | .inl (.inr a) => 2*G.pairWeight 0 a*G.pairWeight 1 a
    | .inr (.inl _) => (G.scale N)^2
    | .inr (.inr (a,b)) => 2*G.scale N*G.pairWeight b a
  active := fun p => match G.graph.state.ports.nextPortEquiv p with
    | .inl _ => G.scale N
    | .inr p => G.active (qmaForkRemainingPort G.graph.degree p)
  constant := (G.constant+∑ e, (3/4+3*(G.pairWeight 0 e)^2+3*(G.pairWeight 1 e)^2))+
    3*(G.graph.state.ports.pairCount:ℚ)*(G.scale N)^2

theorem next_real (G : QMARationalForkNetwork c) (N : ℚ) :
    (G.next N).real = G.real.next N := by
  dsimp only [next,real,QMAWeightedForkNetwork.next]
  congr 1
  · funext e
    rcases e with (e | e) | (e | ⟨e,b⟩) <;>
      simp [QMAForkState.nextWeight,pairWeight,QMAForkState.pairWeight,scale_cast,real]
  · funext p
    dsimp only [QMAForkState.nextActive]
    split <;> simp_all only [scale_cast,real]
  · simp [QMAForkState.nextConstant,qmaForkOffset,pairWeight,QMAForkState.pairWeight,scale_cast,real]

def iterate (G : QMARationalForkNetwork c) (N : ℚ) : ℕ → QMARationalForkNetwork c
  | 0 => G
  | k+1 => (G.iterate N k).next N

theorem iterate_real (G : QMARationalForkNetwork c) (N : ℚ) (k : ℕ) :
    (G.iterate N k).real = G.real.iterate N k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate,next_real,ih]
    rfl

theorem iterate_energy_error (G : QMARationalForkNetwork c) {N : ℚ} (hN : 0 < N) (k : ℕ) :
    |(G.iterate N k).real.energy-G.real.energy| ≤ (k:ℝ)/(N:ℝ) := by
  rw [G.iterate_real]
  exact G.real.iterate_energy_error (by exact_mod_cast hN) k

end QMARationalForkNetwork
end ContinuumCoulomb

end

end OAI
