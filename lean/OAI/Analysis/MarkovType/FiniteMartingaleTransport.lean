import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import Mathlib.Data.Fintype.EquivFin

namespace OAI

noncomputable section

open scoped BigOperators

universe u v w

namespace MarkovSuperreflexivity

variable {Ω : Type u} {Ξ : Type v} [sectionFintypeΩ : Fintype Ω] [sectionFintypeΞ : Fintype Ξ]

namespace FiniteLaw

def reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) : FiniteLaw Ξ where
  mass ξ := μ.mass (e ξ)
  mass_nonneg ξ := μ.mass_nonneg (e ξ)
  sum_mass := (e.sum_comp μ.mass).trans μ.sum_mass

@[simp] theorem reindex_mass (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (ξ : Ξ) :
    (μ.reindex e).mass ξ = μ.mass (e ξ) := rfl

@[simp] theorem expect_reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → ℝ) :
    (μ.reindex e).expect (f ∘ e) = μ.expect f :=
  e.sum_comp (fun ω => μ.mass ω * f ω)

@[simp] theorem vexpect_reindex {V : Type w} [AddCommMonoid V] [Module ℝ V]
    (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → V) :
    (μ.reindex e).vexpect (f ∘ e) = μ.vexpect f :=
  e.sum_comp (fun ω => μ.mass ω • f ω)

@[simp] theorem prob_reindex (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (A : Ω → Prop) :
    (μ.reindex e).prob (A ∘ e) = μ.prob A := by
  classical
  exact e.sum_comp (fun ω => if A ω then μ.mass ω else 0)

end FiniteLaw

namespace FinitePartitionFiltration

def reindex (F : FinitePartitionFiltration Ω) (e : Ξ ≃ Ω) :
    FinitePartitionFiltration Ξ where
  part n := Setoid.comap e (F.part n)
  refines := by
    intro m n hmn ξ η hξη
    exact F.refines hmn hξη

omit sectionFintypeΩ sectionFintypeΞ in
theorem AdaptedAt.reindex [Fintype Ω] [Fintype Ξ] {V : Type w} {F : FinitePartitionFiltration Ω}
    {n : ℕ} {f : Ω → V} (hf : F.AdaptedAt n f) (e : Ξ ≃ Ω) :
    (F.reindex e).AdaptedAt n (f ∘ e) := by
  intro ξ η hξη
  exact hf hξη

end FinitePartitionFiltration

variable {E : Type w} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem HasZeroConditionalSum.reindex {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (e : Ξ ≃ Ω) :
    HasZeroConditionalSum (μ.reindex e) (Setoid.comap e P) (f ∘ e) := by
  classical
  intro a
  change (∑ ξ, if P.r (e ξ) (e a) then μ.mass (e ξ) • f (e ξ) else 0) = 0
  exact (e.sum_comp (fun ω => if P.r ω (e a) then μ.mass ω • f ω else 0)).trans
    (hf (e a))

omit sectionFintypeΩ sectionFintypeΞ sectionNormedSpaceℝE in
@[simp] theorem finiteDifference_comp_equiv [Fintype Ω] [Fintype Ξ] [NormedSpace ℝ E] (M : ℕ → Ω → E) (e : Ξ ≃ Ω)
    (j : ℕ) :
    finiteDifference (fun n => M n ∘ e) j = finiteDifference M j ∘ e := by
  funext ξ
  by_cases hj : j = 0 <;> simp only [finiteDifference, hj, Function.comp_apply,
    ite_true, ite_false]

omit sectionNormedSpaceℝE in
@[simp] theorem finiteL2Norm_reindex [NormedSpace ℝ E] (μ : FiniteLaw Ω) (e : Ξ ≃ Ω) (f : Ω → E) :
    finiteL2Norm (μ.reindex e) (f ∘ e) = finiteL2Norm μ f := by
  change Real.sqrt ((μ.reindex e).expect ((fun ω => ‖f ω‖ ^ (2 : ℕ)) ∘ e)) =
    Real.sqrt (μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)))
  rw [μ.expect_reindex]

namespace FinitePartitionFiltration

theorem IsMartingaleUpTo.reindex {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {N : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (e : Ξ ≃ Ω) :
    (F.reindex e).IsMartingaleUpTo (μ.reindex e) (fun n => M n ∘ e) N := by
  constructor
  · intro n hn ξ η hξη
    exact hM.1 n hn hξη
  · intro n hn hnN
    rw [finiteDifference_comp_equiv]
    exact (hM.2 n hn hnN).reindex e

end FinitePartitionFiltration

theorem FiniteUpperL2.apply {r χ : ℝ} (h : FiniteUpperL2 E r χ)
    (μ : FiniteLaw Ω) (F : FinitePartitionFiltration Ω) (M : ℕ → Ω → E)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B) (hM : F.IsMartingaleUpTo μ M N)
    (hd : ∀ j : ℕ, j ≤ N → finiteL2Norm μ (finiteDifference M j) ≤ B) :
    finiteL2Norm μ (M N) ≤ χ * (N + 1 : ℝ) ^ (1 / r) * B := by
  let e : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  have hd' : ∀ j : ℕ, j ≤ N →
      finiteL2Norm (μ.reindex e) (finiteDifference (fun n => M n ∘ e) j) ≤ B := by
    intro j hj
    simpa only [finiteDifference_comp_equiv, finiteL2Norm_reindex] using hd j hj
  have hbound := h (Fintype.card Ω) (μ.reindex e) (F.reindex e)
    (fun n => M n ∘ e) N B hB (hM.reindex e) hd'
  simpa only [finiteL2Norm_reindex] using hbound

theorem FiniteLowerL2.apply {s χ : ℝ} (h : FiniteLowerL2 E s χ)
    (μ : FiniteLaw Ω) (F : FinitePartitionFiltration Ω) (M : ℕ → Ω → E)
    (N : ℕ) (hM : F.IsMartingaleUpTo μ M N) :
    (∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference M j)) ≤
      χ * (N + 1 : ℝ) ^ (1 - 1 / s) * finiteL2Norm μ (M N) := by
  let e : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  have hbound := h (Fintype.card Ω) (μ.reindex e) (F.reindex e)
    (fun n => M n ∘ e) N (hM.reindex e)
  simpa only [finiteDifference_comp_equiv, finiteL2Norm_reindex] using hbound

end MarkovSuperreflexivity

end

end OAI
