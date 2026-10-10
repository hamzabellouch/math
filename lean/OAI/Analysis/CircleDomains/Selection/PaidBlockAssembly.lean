import OAI.Analysis.CircleDomains.Selection.FiniteChainPotential

namespace OAI

/-! Reconnect finitely many approximating true blocks using unchanged
old jump edges. The block endpoints may vary within each old jump disk. -/

open Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem exists_paid_chain_from_approximate_blocks
    (R : X → X → ℝ≥0∞ → Prop) (n : ℕ)
    (E : Fin (n+2) → Set X) (A : Fin (n+1) → ℝ≥0∞) (J : Fin n → ℝ≥0∞)
    (hjump : ∀i : Fin n, ∀x ∈ E i.succ.castSucc, ∀y ∈ E i.succ.castSucc, R x y (J i))
    (hblock : ∀i : Fin (n+1), ∀ε : ℝ, 0 < ε →
      ∃x ∈ E i.castSucc, ∃y ∈ E i.succ, ∃c : ℝ≥0∞,
        PaidChain R x y c ∧ c ≤ A i + ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) :
    ∃x ∈ E 0, ∃y ∈ E (Fin.last (n+1)), ∃c : ℝ≥0∞,
      PaidChain R x y c ∧ c ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  induction n generalizing η with
  | zero =>
      obtain ⟨x, hx, y, hy, c, hc, hcost⟩ := hblock 0 η hη
      exact ⟨x, hx, y, hy, c, hc, by simpa using hcost⟩
  | succ n ih =>
      have hh : 0 < η/2 := by positivity
      let E' : Fin (n+2) → Set X := fun i => E i.castSucc
      let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
      let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
      have hj' (i : Fin n) (x : X) (hx : x ∈ E' i.succ.castSucc)
          (y : X) (hy : y ∈ E' i.succ.castSucc) : R x y (J' i) :=
        hjump i.castSucc x hx y hy
      have hb' (i : Fin (n+1)) (ε : ℝ) (hε : 0 < ε) :
          ∃x ∈ E' i.castSucc, ∃y ∈ E' i.succ, ∃c : ℝ≥0∞,
            PaidChain R x y c ∧ c ≤ A' i + ENNReal.ofReal ε :=
        hblock i.castSucc ε hε
      obtain ⟨x, hx, z, hz, a, hα, hαc⟩ := ih E' A' J' hj' hb' hh
      obtain ⟨z', hz', y, hy, b, hβ, hβc⟩ := hblock (Fin.last (n+1)) (η/2) hh
      have hbridge := hjump (Fin.last n) z hz z' hz'
      refine ⟨x, hx, y, hy, (a + J (Fin.last n)) + b,
        (hα.append (PaidChain.single hbridge)).append hβ, ?_⟩
      have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hh.le hh.le]
        congr 1
        ring
      have hsA := Fin.sum_univ_castSucc A
      have hsJ := Fin.sum_univ_castSucc J
      calc
        a + J (Fin.last n) + b ≤
            ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) + J (Fin.last n) +
              (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) :=
          add_le_add (add_le_add hαc le_rfl) hβc
        _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
          rw [hsA, hsJ, ← herr]
          dsimp [A', J']
          ac_rfl

end CircleDomainRigidity

end

end OAI
