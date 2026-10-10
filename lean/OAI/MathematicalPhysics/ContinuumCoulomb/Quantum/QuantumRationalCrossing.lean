import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingProgram

namespace OAI

/-! A simultaneous crossing-removal layer as exact rational ordinary-spin data. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

structure QMARationalCrossingLayer (r : ℕ) where
  base : QMARationalExchangeGraph
  site : Fin r → Fin 4 → Fin base.n
  injective : ∀ i, Function.Injective (site i)
  J : Fin r → ℚ
  K : Fin r → ℚ

namespace QMARationalCrossingLayer
variable {r : ℕ}

def source (C : QMARationalCrossingLayer r) : QMARationalExchangeGraph where
  n := C.base.n
  Edge := C.base.Edge ⊕ (Fin r × Fin 2)
  left := Sum.elim C.base.left (fun p => C.site p.1 (if p.2 = 0 then 0 else 1))
  right := Sum.elim C.base.right (fun p => C.site p.1 (if p.2 = 0 then 2 else 3))
  distinct := by
    intro e
    rcases e with e | ⟨i,a⟩
    · exact C.base.distinct e
    · intro h
      have h' := C.injective i h
      fin_cases a <;> norm_num at h'
  weight := Sum.elim C.base.weight (fun p => if p.2 = 0 then C.J p.1 else C.K p.1)
  constant := C.base.constant

theorem source_matrix (C : QMARationalCrossingLayer r) :
    qmaExchangeMatrix C.source.left C.source.right (fun e => (C.source.weight e:ℝ)) C.source.constant =
      qmaExchangeMatrix C.base.left C.base.right (fun e => (C.base.weight e:ℝ)) C.base.constant +
        ∑ i, ((C.J i:ℂ) • sourceHeisenbergMatrix C.base.n (C.site i 0) (C.site i 2) +
          (C.K i:ℂ) • sourceHeisenbergMatrix C.base.n (C.site i 1) (C.site i 3)) := by
  let f : C.source.Edge → Matrix (SourceSpinBasis C.base.n) (SourceSpinBasis C.base.n) ℂ :=
    fun e => (C.source.weight e:ℂ) • sourceHeisenbergMatrix C.base.n (C.source.left e) (C.source.right e)
  let g : C.base.Edge ⊕ (Fin r × Fin 2) →
      Matrix (SourceSpinBasis C.base.n) (SourceSpinBasis C.base.n) ℂ := fun e =>
    ((Sum.elim C.base.weight (fun p => if p.2 = 0 then C.J p.1 else C.K p.1)) e:ℂ) •
      sourceHeisenbergMatrix C.base.n
        ((Sum.elim C.base.left (fun p => C.site p.1 (if p.2 = 0 then 0 else 1))) e)
        ((Sum.elim C.base.right (fun p => C.site p.1 (if p.2 = 0 then 2 else 3))) e)
  let E : C.source.Edge ≃ C.base.Edge ⊕ (Fin r × Fin 2) := Equiv.refl _
  have hs : (∑ e, f e) = ∑ e, g e := Fintype.sum_equiv E f g (by intro e; rfl)
  simp only [qmaExchangeMatrix]
  change (∑ e, f e)+(C.base.constant:ℂ) • 1 = _
  rw [hs]
  simp only [g,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
  simp
  ac_rfl

def scale (C : QMARationalCrossingLayer r) (N : ℚ) : ℚ :=
  let B := 3*(∑ e, |C.base.weight e|)+|C.base.constant|
  let A := 6*∑ i, (1+|C.J i|+|C.K i|)
  let D := B+12*∑ i, (1+|C.J i|+|C.K i|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

theorem scale_cast (C : QMARationalCrossingLayer r) (N : ℚ) :
    (C.scale N:ℝ) =
      qmaRoutingScale (6*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|))
        (3*(∑ e, |(C.base.weight e:ℝ)|)+|(C.base.constant:ℝ)|+
          12*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2) N := by
  simp only [scale,qmaRoutingScale]
  push_cast
  rfl

def output (C : QMARationalCrossingLayer r) (N : ℚ) : QMARationalExchangeGraph where
  n := C.base.n+r*2
  Edge := QMACrossingsGraphEdge C.base.Edge r
  left := qmaParallelGraphLeft (qmaCrossingsBaseLeft C.base.left C.site) C.site
  right := qmaParallelGraphRight (qmaCrossingsBaseRight C.base.right C.site) (fun _ => qmaCrossingMember)
  distinct := qmaParallelGraph_distinct _ _
    (qmaCrossingsBase_distinct _ _ C.base.distinct C.site C.injective) _ _
  weight := fun e => match e with
    | .inl (.inl e) => C.base.weight e
    | .inl (.inr (i,a)) => QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+5,by omega⟩
    | .inr (.inl _) => (C.scale N)^2
    | .inr (.inr (i,a)) => QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+1,by omega⟩
  constant := (C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+3*(r:ℚ)*(C.scale N)^2

theorem output_matrix (C : QMARationalCrossingLayer r) (N : ℚ) :
    qmaExchangeMatrix (C.output N).left (C.output N).right (fun e => ((C.output N).weight e:ℝ))
      (C.output N).constant =
      qmaCrossingsGraph C.base.left C.base.right (fun e => (C.base.weight e:ℝ)) C.base.constant
        (C.scale N) C.site (fun i => (C.J i:ℝ)) (fun i => (C.K i:ℝ)) := by
  dsimp only [output,qmaCrossingsGraph]
  congr 1
  · funext e
    rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
    · rfl
    · exact QuantumRoutingCode.coefficients_perimeter (C.scale N,C.J i,C.K i) a
    · simp [qmaParallelGraphWeight]
    · exact QuantumRoutingCode.coefficients_spoke (C.scale N,C.J i,C.K i) a
  · simp [qmaCrossingOffset]

theorem output_energy_error (C : QMARationalCrossingLayer r) {N : ℚ} (hN : 0 < N) :
    |(C.output N).energy-C.source.energy| ≤ 1/(N:ℝ) := by
  unfold QMARationalExchangeGraph.energy
  rw [C.output_matrix,C.source_matrix,C.scale_cast]
  exact qmaCrossingsGraph_accuracy C.base.left C.base.right C.base.distinct
    (fun e => (C.base.weight e:ℝ)) C.base.constant C.site C.injective
    (fun i => (C.J i:ℝ)) (fun i => (C.K i:ℝ)) (by exact_mod_cast hN)

theorem output_edge_count (C : QMARationalCrossingLayer r) (N : ℚ) :
    Fintype.card (C.output N).Edge = Fintype.card C.base.Edge+9*r :=
  qmaCrossingsGraphEdge_card C.base.Edge r

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
