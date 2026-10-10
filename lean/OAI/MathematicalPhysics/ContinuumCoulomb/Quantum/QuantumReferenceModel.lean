import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceTerms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalModel

namespace OAI

/-! A real six-local history model with separate references and a linear term count. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev qmaFirstUseTime (c : QMACircuit) (i : Fin (c.work+1)) : Fin (c.gates.length+1) :=
  ⟨qmaFirstUse c i,Nat.lt_succ_of_le (qmaFirstUse_le c i)⟩

def qmaReferenceHistorySites (c : QMACircuit) (i : Fin (qmaHistoryReferenceWork c+1)) :
    Finset (QMACircuitQubit c) :=
  qmaDistributedTermSites c (qmaFirstUseTime c) ((qmaHistoryTermIndex c).symm i)

def qmaReferenceHistoryModel (c : QMACircuit) : QMARealLocalModel 6 where
  Q := Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c
  Term := QMAReferenceTerm (qmaHistoryReferenceWork c)
  qFinite := inferInstance
  qDecidable := inferInstance
  termFinite := inferInstance
  matrix := qmaReferenceTermMatrix (qmaHistoryReferenceWork c)
    (qmaHistoryReferenceTerms c (qmaFirstUseTime c))
  sites := qmaReferenceTermSites (qmaHistoryReferenceWork c) (qmaReferenceHistorySites c)
  localOn := qmaReferenceTerm_local _ _ _ (fun _ => qmaDistributedTerm_local c _ _)
  card := qmaReferenceTerm_card _ _ (fun _ => qmaDistributedTerm_support_card c _ _)
  hermitian := qmaReferenceTerm_hermitian _ _ (fun _ => qmaDistributedTerm_hermitian c _ _)
  real := qmaReferenceTerm_real _ _

theorem qmaReferenceHistoryModel_sum (c : QMACircuit) :
    (∑ t, (qmaReferenceHistoryModel c).matrix t) =
      qmaReferenceOnQubits (qmaHistoryReferenceWork c)
        (qmaHistoryReferenceTerms c (qmaFirstUseTime c)) :=
  qmaReferenceTerm_sum _ _

theorem qmaReferenceHistoryModel_size (c : QMACircuit) :
    (qmaReferenceHistoryModel c).qubits = 3*c.gates.length+2*c.work+8 ∧
    (qmaReferenceHistoryModel c).terms = 4*c.gates.length+2*c.work+9 := by
  constructor
  · change Fintype.card (Fin (2*c.gates.length+c.work+4+1) ⊕
      (Fin (c.gates.length+2) ⊕ Fin (c.work+1))) = _
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  · change Fintype.card (Fin (2*c.gates.length+c.work+4+1) ⊕
      Fin (2*c.gates.length+c.work+4)) = _
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega

theorem qmaReferenceHistoryModel_yes (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    (qmaReferenceHistoryModel c).energy ≤ 1/(3*(c.gates.length+1:ℝ)) := by
  obtain ⟨v,hv,he⟩ := qmaReferenceHistory_accepting c hc (qmaFirstUseTime c)
    (qmaFirstUse_untouched c) psi hpsi hacc
  let e := Equiv.sumArrowEquivProdArrow (Fin (qmaHistoryReferenceWork c+1))
    (QMACircuitQubit c) (Fin 2)
  let u : EuclideanSpace ℂ ((Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c) → Fin 2) :=
    WithLp.toLp 2 (v ∘ e)
  have hu : ‖u‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    simp only [u,EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow]
    exact (e.sum_comp (fun p => Complex.normSq (v p))).trans hv
  unfold QMARealLocalModel.energy
  rw [qmaReferenceHistoryModel_sum]
  apply (qmaNormalizedBottom_le _ u hu).trans
  have hq : qmaQuadratic (qmaReferenceOnQubits (qmaHistoryReferenceWork c)
      (qmaHistoryReferenceTerms c (qmaFirstUseTime c))) (fun p => u p) =
      qmaQuadratic (qmaReferenceHistory c (qmaFirstUseTime c)) v :=
    qmaQuadratic_reindex e _ v
  rw [hq]
  exact (le_div_iff₀ (by positivity : 0 < 3*(c.gates.length+1:ℝ))).mpr (by linarith)

theorem qmaReferenceHistoryModel_no (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    2/(5*(c.gates.length+1:ℝ)) ≤ (qmaReferenceHistoryModel c).energy := by
  unfold QMARealLocalModel.energy
  rw [qmaReferenceHistoryModel_sum]
  apply le_qmaNormalizedBottom _ (EuclideanSpace.single (fun _ => (0:Fin 2)) (1:ℂ))
    (by simp [PiLp.norm_single])
  intro u hu
  change EuclideanSpace ℂ ((Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c) → Fin 2) at u
  have hu1 : ‖u‖ = 1 := hu
  let e := Equiv.sumArrowEquivProdArrow (Fin (qmaHistoryReferenceWork c+1))
    (QMACircuitQubit c) (Fin 2)
  have h := qmaReferenceHistory_lower c hc (qmaFirstUseTime c) (qmaFirstUse_untouched c)
    hsound ((fun p => u p) ∘ e.symm)
  have hm : (∑ p, Complex.normSq (((fun q => u q) ∘ e.symm) p)) = 1 := by
    change (∑ p, Complex.normSq (u (e.symm p))) = 1
    rw [qmaMass_reindex e (fun p => u p)]
    calc
      _ = ‖u‖^2 := by
        simpa only [Complex.sq_norm] using (EuclideanSpace.norm_sq_eq u).symm
      _ = 1 := by rw [hu1]; norm_num
  rw [hm,mul_one] at h
  change _ ≤ qmaQuadratic ((qmaReferenceHistory c (qmaFirstUseTime c)).submatrix e e) (fun p => u p)
  rw [qmaQuadratic_reindex_equiv]
  exact h

end ContinuumCoulomb

end

end OAI
