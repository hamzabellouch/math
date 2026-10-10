import Mathlib
import OAI.Analysis.Commutator.ExponentialMomentBudget
import OAI.Analysis.Commutator.FiniteWordPatchProducer
import OAI.Analysis.Commutator.PartialMomentBudget
import OAI.Analysis.Commutator.PartialUnitaryChain
import OAI.Analysis.Commutator.PartialWordContinuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {J K : Type*} (x : J → M) (k : K → ℤ)

def Admissible (N : ℕ) (ε η : ℝ) : Set (PartialUnitary M) :=
  {v | (v.val : H →L[ℂ] H)∈R ∧ (τ v.support).re ≤ 1-η ∧
    MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re)}

lemma zero_admissible (hcenter : ∀ j,τ (x j)=0) (N : ℕ) {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : η ≤ 1) : PartialUnitary.zero∈Admissible M R τ x k N ε η := by
  refine ⟨R.zero_mem,?_,zero_momentBound τ x k hcenter N (momentBudget_nonneg hε _ _)⟩
  change (τ 0).re ≤ 1-η
  simp only [map_zero,Complex.zero_re]
  linarith

include hτ in
lemma admissible_chain_upper (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (N : ℕ) (ε η : ℝ) (c : Set (PartialUnitary M))
    (hcs : c ⊆ Admissible M R τ x k N ε η) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v∈Admissible M R τ x k N ε η,∀ w∈c,w ≤ v := by
  obtain ⟨v,hv,hmem,ω,hω,htr,hl2⟩ :=
    PartialUnitary.chain_upper_with_L2_and_membership M τ hnormal c hc hne
  have hl2' : Tendsto (fun w : c => TracialL2.norm τ (w.val.val-v.val)) (ω : Filter c) (𝓝 0) := by
    apply hl2.congr'
    exact Eventually.of_forall fun w => by
      simp only [TracialL2.norm,map_sub,norm_sub_rev]
  have hB : Tendsto (fun w : c => momentBudget ε (budgetSlope N η) (τ w.val.support).re)
      (ω : Filter c) (𝓝 (momentBudget ε (budgetSlope N η) (τ v.support).re)) := by
    exact ((Real.continuous_exp.tendsto _).comp (htr.const_mul (budgetSlope N η))).const_mul ε
  refine ⟨v,⟨hmem R (fun w hw => (hcs hw).1),?_,?_⟩,hv⟩
  · exact le_of_tendsto_of_tendsto htr tendsto_const_nhds
      (Eventually.of_forall fun w : c => (hcs w.property).2.1)
  · exact momentBound_limit τ hτ x k hone hx (fun w : c => w.val) v _ _ N hl2' hB
      (fun w => (hcs w.property).2.2)

variable [Fintype J] [Fintype K]

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_almost_full_finite_tests (hRM : R ≤ M)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (hx : ∀ j,‖x j‖ ≤ 1) (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
    (N : ℕ) {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (hη1 : η ≤ 1) :
    ∃ v : PartialUnitary M, (v.val : H →L[ℂ] H)∈R ∧ (τ v.support).re=1-η ∧
      MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (1-η)) := by
  have hzero := zero_admissible M R τ x k hcenter N hε.le hη1
  obtain ⟨v,hv⟩ := zorn_le₀ (Admissible M R τ x k N ε η) (by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with he | hne
    · exact ⟨PartialUnitary.zero,hzero,fun w hw => (he ▸ hw : w∈(∅ : Set (PartialUnitary M))).elim⟩
    · exact admissible_chain_upper M R τ hτ x k hnormal hone hx N ε η c hcs hc hne)
  have hcut : (τ v.support).re=1-η := by
    apply le_antisymm hv.1.2.1
    by_contra hn
    have hlt : (τ v.support).re<1-η := lt_of_not_ge hn
    have hrest : η ≤ (τ (1-v.support)).re := by
      rw [map_sub,hone,Complex.sub_re,Complex.one_re]
      linarith [hv.1.2.1]
    have hvR : (v.support : H →L[ℂ] H)∈R := by
      rw [←v.star_mul]
      exact R.mul_mem (R.star_mem' hv.1.1) hv.1.1
    obtain ⟨w,hwR,_,hqp,horth,hqt,hqsmall,hpure,hsmall,hphase⟩ :=
      exists_finite_word_patch M R hRM τ hτ stage hmono hnormal hfaith hone hirr hgrow hstage
        hdiffuse x k hk v hvR (hη.trans_le hrest) N hε
        (show 0<1-η-(τ v.support).re by linarith)
    have hnew : v.add w horth∈Admissible M R τ x k N ε η := by
      refine ⟨R.add_mem hv.1.1 hwR,?_,?_⟩
      · change (τ (v.support+w.support)).re ≤ 1-η
        rw [map_add,Complex.add_re]
        linarith
      · exact momentBound_add τ hτ x k hx v w horth hqp hε.le hη hrest hv.1.2.2
          hpure hsmall hphase
    have hp := (hv.2 hnew (v.le_add w horth)).1
    have htp := (τ.monotone hp).1
    change (τ (v.support+w.support)).re ≤ (τ v.support).re at htp
    rw [map_add,Complex.add_re] at htp
    linarith
  exact ⟨v,hv.1.1,hcut,by simpa only [hcut] using hv.1.2.2⟩

end Kadison.FinitePatching

end

end
end

end OAI
