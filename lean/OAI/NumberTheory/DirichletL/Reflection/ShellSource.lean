import OAI.NumberTheory.DirichletL.Reflection.FullDyadic
import OAI.NumberTheory.DirichletL.Reflection.PhysicalIntegral

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma shell_windows_one (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (K P : Ideal Eis) (hK : K≠0) (hP : P≠0)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (j k : ℕ) (n : dualIdealDyad k) (b : dualIdealDyad j) :
    (∏ i : Fin 4, completedShellWindow (kernelLogCoordinates QK QP ((2:ℝ)^k) ((2:ℝ)^j)
      (Ideal.absNorm K:ℝ) (Ideal.absNorm P:ℝ) (Ideal.absNorm n.val:ℝ) (Ideal.absNorm b.val:ℝ) i))=1 := by
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hn := dualIdealDyad_bounds k n.val n.property
  have hb := dualIdealDyad_bounds j b.val b.property
  apply Finset.prod_eq_one
  intro i hi
  fin_cases i <;> dsimp only [kernelLogCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact completedShellWindow_log _ _ (hnorm K hK) hQK hKr.1 hKr.2
  · exact completedShellWindow_log _ _ (hnorm P hP) hQP hPr.1 hPr.2
  · exact completedShellWindow_log _ _ (hnorm n.val hn.1) (by positivity) hn.2.1 hn.2.2
  · exact completedShellWindow_log _ _ (hnorm b.val hb.1) (by positivity) hb.2.1 hb.2.2

theorem literalRawSeries_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalRawSeries (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
      actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [ite_eq_left hp]
    unfold literalRawSeries rawDualKernelTerm literalRawCoefficient actualKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [ite_eq_left hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [ite_eq_right hp,literalRawSeries,rawDualKernelTerm,literalRawCoefficient,ite_eq_right hp',zero_mul]

theorem literalDyadicBlock_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
          actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact literalRawSeries_eq_shell_source F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X
end
end SevenEighths.InverseReflectedPhase

end OAI
