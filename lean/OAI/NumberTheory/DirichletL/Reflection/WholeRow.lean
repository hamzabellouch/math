import OAI.NumberTheory.DirichletL.Reflection.ShellRows
import OAI.NumberTheory.DirichletL.Reflection.TruncatedSource

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0<X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryGenerator K))
            (fun P => aw P*shapeArgument (primaryGenerator P)) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryGenerator K))*(aw P.val.val*shapeArgument (primaryGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
