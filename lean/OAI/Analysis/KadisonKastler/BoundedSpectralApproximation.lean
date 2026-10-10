import OAI.Analysis.FactorGeneration.SpectralApproximation
import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection

namespace OAI

/-! # Bounded coefficients in the constructed finite spectral approximations

The dyadic spectral intervals remain inside their initial norm bounds.
This records the coefficient bound needed by the threshold-cut argument.
-/

namespace Generator.Tracial

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem SpectralInterval.level_nested {x : M.toStarSubalgebra} (I : SpectralInterval x)
    (hx : IsSelfAdjoint x) (hI : I.lo ≤ I.hi) :
    ∀ n i, I.lo ≤ (I.level hx n i).lo ∧
      (I.level hx n i).lo ≤ (I.level hx n i).hi ∧ (I.level hx n i).hi ≤ I.hi := by
  intro n
  induction n with
  | zero => intro i; exact ⟨le_rfl,hI,le_rfl⟩
  | succ n ih =>
    rintro ⟨i,b⟩
    obtain ⟨hlo,hw,hhi⟩ := ih i
    change I.lo ≤ ((I.level hx n i).child hx b).lo ∧
      ((I.level hx n i).child hx b).lo ≤ ((I.level hx n i).child hx b).hi ∧
      ((I.level hx n i).child hx b).hi ≤ I.hi
    cases b <;> simp only [SpectralInterval.child,Bool.false_eq_true,ite_false,ite_true,
      SpectralInterval.low,SpectralInterval.high,SpectralInterval.midpoint] <;>
      (refine ⟨?_,?_,?_⟩ <;> linarith)

theorem exists_bounded_spectral_approximation (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (hn : ‖x‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℝ),
      (∀ i, c i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval (identityProjection M) x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,happrox⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,?_,?_⟩
  · intro i
    obtain ⟨hlo,hw,hhi⟩ := I.level_nested hx hI n (e i)
    have hl : -‖x‖ ≤ (I.level hx n (e i)).lo := hlo
    have hh : (I.level hx n (e i)).hi ≤ ‖x‖ := hhi
    exact ⟨by linarith,by linarith⟩
  · have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) •
        (I.level hx n i).proj.val)
    change ‖x - ∑ i, ((I.level hx n (e i)).lo : ℂ) •
      (I.level hx n (e i)).proj.val‖ < ε
    rw [he]
    change ‖(1 : M.toStarSubalgebra) * x * 1 - ∑ i : DyadicIndex n,
      ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val‖ < ε at happrox
    simpa only [one_mul,mul_one] using happrox

end

end Generator.Tracial

end OAI
