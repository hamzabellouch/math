import OAI.Probability.DilutedSpin.ZeroShape

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma physicalShape_zero (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (a : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (F : (Option (Fin 0) → Option (Fin 0) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    physicalShapeCovariance m S a M C H N u F spinAnchor f =
      F (fun _ _ => L+1) * physicalCoefficient (weights L) prior m direction anchor
        S a M C H N u f (zeroSpec L spinAnchor) 0 := by
  exact shapeCovariance_zero (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S a
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) F spinAnchor f
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend hB hf

 
theorem complete_shape_selection (m : Fin (L+1) → ℝ)
    (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior m direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ (S : PrescribedTree (L+1)) (a : S.Leaf)
        (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
        (B : ℝ), 0 ≤ B → (∀ n x, |f n x| ≤ B) →
        ∀ (k : ℕ) (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool),
        Tendsto (fun n => physicalShapeCovariance m S a M C H (Ns n+1) (us n)
          F spinAnchor (f n)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,he,hcoef⟩ := universal_analytic_selection m M hC hH hc
    hθ hh hθi hhi hm hmono hend hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro S a f B hB hf k F spinAnchor
  by_cases hk : k = 0
  · subst k
    simp_rw [physicalShape_zero m (fun j => hc.trans_le (hm j)) hmono hend S a M C H _ _
      F spinAnchor _ hB (hf _)]
    simpa using (hcoef S a f B hB hf (zeroSpec L spinAnchor) 0).const_mul (F (fun _ _ => L+1))
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  simp_rw [physicalShape_expansion hk' m (fun j => hc.trans_le (hm j)) hmono hend
    S a M C H _ _ F spinAnchor _ hB (hf _)]
  have hh (r : ℕ) (b c : Fin r → Option (Fin k)) (d : Fin r → Fin L) :
      Tendsto (fun n => physicalHistoryCovariance m S a M C H (Ns n+1) (us n)
        b c d spinAnchor (f n)) atTop (𝓝 0) := by
    simp_rw [physicalHistory_polarization hk' m (fun j => hc.trans_le (hm j)) hmono hend
      S a M C H _ _ b c d spinAnchor _ hB (hf _)]
    have ht := tendsto_finsetSum (Finset.univ : Finset (Fin k → Bool))
      (fun e _ => (hcoef S a f B hB hf (polarizedSpec hk' e b c d spinAnchor) k).const_mul
        (∏ j, Polarization.sign (e j)))
    simpa using ht.const_mul ((k:ℝ)^k / 2^k)
  have ht := tendsto_finsetSum (Finset.univ : Finset (Finset (SharingIndex L (Option (Fin k)))))
    (fun s _ => (hh _ (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
        (fun j => (requirementMap s j).2.2)).const_mul
      (BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s))
  simpa using ht

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
