import OAI.Probability.BenjaminiSchramm.SubcriticalLayerPrefactor

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nonempty V] (G : BondGraph V E)

theorem adjusted_upper_layer_second_moment_constant
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (χ : ℝ) (hχ : 0 ≤ χ)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ ENNReal.ofReal χ)
    (β K : ℝ) (hβ : 0 < β) (hK : 0 < K)
    (hup : ∀ n : ℕ, G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
        {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n)) := by
  let S : ℕ → ℝ := fun n => (G.supAdjustedUpLayerMoment a R p n).toReal
  have hne (n : ℕ) : G.supAdjustedUpLayerMoment a R p n ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup n)
  have hS (n : ℕ) : 0 ≤ S n := ENNReal.toReal_nonneg
  have hSEq (n : ℕ) : ENNReal.ofReal (S n)=G.supAdjustedUpLayerMoment a R p n := ENNReal.ofReal_toReal (hne n)
  have hbound (n : ℕ) : S n ≤ χ := by
    have hb : G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal χ := by
      apply iSup_le
      intro x
      apply iSup_le
      intro u
      exact restrictedLayerCount_expectation_le_row_bound G.ends p _ hrow _ _ x
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_ofReal hχ] at hh
  have hSK (n : ℕ) : S n ≤ K*Real.exp (-β*n) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hup n)
    rwa [ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _))] at hh
  have hdecay (n : ℕ) : S n ≤ K*Real.exp (-(3*β/4)*n) := by
    apply (hSK n).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmul (n j : ℕ) : S (n+j) ≤ S n*S j := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hne n) (hne j))
      (G.supAdjustedUpLayerMoment_submultiplicative hc hl a R hR hjump p n j)
    simpa only [ENNReal.toReal_mul] using hh
  have hF (i : ℤ) : G.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    G.supAdjustedFullLayerMoment_le_row_bound a R p _ hrow i
  have hFpos (n : ℕ) : G.supAdjustedFullLayerMoment a R p n ≤ ENNReal.ofReal (χ*S n) := by
    apply (G.supAdjustedFullLayerMoment_up_bound hc hl a R hR hjump p _ hrow n).trans_eq
    rw [←hSEq n]
    rw [←ENNReal.ofReal_mul (hS n)]
    congr 1
    ring
  obtain ⟨A,hA,hsecond⟩ := signed_upper_convolution_bound S hS β K χ hβ hχ hbound hmul hdecay
    (G.supAdjustedFullLayerMoment a R p) hF hFpos
  have hprefix (n : ℕ) : prefixMaximum (fun j => Real.exp (β*j)*S j) n ≤ K := by
    apply Finset.sup'_le
    intro j _
    calc
      _ ≤ Real.exp (β*j)*(K*Real.exp (-β*j)) :=
        mul_le_mul_of_nonneg_left (hSK j) (Real.exp_nonneg _)
      _ = K := by
        rw [show Real.exp (β*(j : ℝ))*(K*Real.exp (-β*j)) =
          K*(Real.exp (β*j)*Real.exp (-β*j)) by ring,←Real.exp_add,
          show β*(j : ℝ)+ -β*j=0 by ring,Real.exp_zero,mul_one]
  refine ⟨A*K,mul_pos hA hK,?_⟩
  intro n x u
  apply (G.adjusted_upper_layer_second_moment_bound hc hl a R p x u n).trans
  have hb := hsecond n
  simp only [hSEq] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left (hprefix n) (mul_nonneg hA.le (Real.exp_nonneg (-β*n)))
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
