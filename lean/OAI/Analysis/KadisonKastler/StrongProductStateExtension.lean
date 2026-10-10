import OAI.Analysis.KadisonKastler.StrongInvariantState
import OAI.Analysis.KadisonKastler.NormalMarginalAgreement
import OAI.Analysis.KadisonKastler.InvariantStateExtension

namespace OAI

/-! # Strongly invariant extensions with normal marginals

This is the normal-marginal specialization of Marrakchi,
arXiv:1811.10253v2, Lemma 4.1 and Proposition 3.10. The initial product
state is an explicit hypothesis; its construction is a separate step.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem exists_strongly_invariant_with_normal_marginals
    (M N : VonNeumannAlgebra H)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (hfix : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (hinv : ∀ t a, φ (stateActionOrbit U a t)=φ a)
    (hφM : ∀ a ∈ M, φ a=productVectorState Ω a)
    (hφN : ∀ a ∈ N, φ a=productVectorState Ω a) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage U hU μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ N, ψ (a*b)=φ (a*b) := by
  let ν := ProbabilityTheory.cauchyMeasure 0 1
  let ψ := φ.comp (stateActionAverageMap U hU ν)
  have hψ : IsState ψ := state_comp_actionAverage U hU ν φ hφ
  have heq (a : H →L[ℂ] H) (ha : Continuous (stateActionOrbit U a)) : ψ a=φ a :=
    invariant_functional_actionAverage U hU φ hinv ν a ha
  have hψM (a : H →L[ℂ] H) (ha : a ∈ M) : ψ a=productVectorState Ω a := by
    change φ (stateActionAverage U hU ν a)=_
    rw [hφM _ (stateActionAverage_mem U hU ν M hM a ha)]
    exact stateActionAverage_vectorState U hU ν Ω hfix a
  have hψN (a : H →L[ℂ] H) (ha : a ∈ N) : ψ a=productVectorState Ω a := by
    change φ (stateActionAverage U hU ν a)=_
    rw [hφN _ (stateActionAverage_mem U hU ν N hN a ha)]
    exact stateActionAverage_vectorState U hU ν Ω hfix a
  refine ⟨ψ,hψ,?_,?_⟩
  · intro μ hμ a
    change φ (stateActionAverage U hU ν (stateActionAverage U hU μ a))=
      φ (stateActionAverage U hU ν a)
    rw [stateActionAverage_commute U hU ν μ a]
    exact invariant_functional_actionAverage U hU φ hinv μ _
      (poissonActionAverage_orbit_continuous U hU a)
  · intro a ha b hb
    exact (normal_marginal_product_agreement U hU M N hM hN Ω φ ψ hφ hψ
      hφM hψM hφN hψN (fun c hc => (heq c hc).symm) a b ha hb).symm

theorem exists_strongly_invariant_product_state
    (M N : VonNeumannAlgebra H)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (hunit : ‖Ω‖=1)
    (hfix : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (hprod : ∀ a ∈ M, ∀ b ∈ N,
      φ (a*b)=productVectorState Ω a*productVectorState Ω b) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage U hU μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ N,
        ψ (a*b)=productVectorState Ω a*productVectorState Ω b := by
  let A : Set (H →L[ℂ] H) := {T | ∃ a ∈ M, ∃ b ∈ N, T=a*b}
  have hA : ∀ T ∈ A, ∀ g : Multiplicative ℝ,
      φ (unitaryConj (U g) T)=φ T := by
    rintro T ⟨a,ha,b,hb,rfl⟩ g
    let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U g)
    have hemul : e (a*b)=e a*e b := e.map_mul a b
    change φ (e (a*b))=φ (a*b)
    rw [hemul,hprod (e a) (hM (Multiplicative.toAdd g) a ha)
      (e b) (hN (Multiplicative.toAdd g) b hb),hprod a ha b hb]
    have hea : productVectorState Ω (e a)=productVectorState Ω a :=
      productVectorState_unitaryConj_of_fixes Ω (U g) (hfix (Multiplicative.toAdd g)) a
    have heb : productVectorState Ω (e b)=productVectorState Ω b :=
      productVectorState_unitaryConj_of_fixes Ω (U g) (hfix (Multiplicative.toAdd g)) b
    rw [hea,heb]
  obtain ⟨φ₀,hφ₀,hinv,heq⟩ := exists_invariant_state_preserving_values U φ hφ A hA
  have hprod₀ (a : H →L[ℂ] H) (ha : a ∈ M) (b : H →L[ℂ] H) (hb : b ∈ N) :
      φ₀ (a*b)=productVectorState Ω a*productVectorState Ω b :=
    (heq _ ⟨a,ha,b,hb,rfl⟩).trans (hprod a ha b hb)
  have hone : productVectorState Ω (1 : H →L[ℂ] H)=1 := by
    change inner ℂ Ω Ω=1
    rw [inner_self_eq_norm_sq_to_K,hunit]
    norm_num
  have hφ₀M (a : H →L[ℂ] H) (ha : a ∈ M) : φ₀ a=productVectorState Ω a := by
    simpa only [mul_one,hone] using hprod₀ a ha 1 N.one_mem
  have hφ₀N (b : H →L[ℂ] H) (hb : b ∈ N) : φ₀ b=productVectorState Ω b := by
    simpa only [one_mul,hone] using hprod₀ 1 M.one_mem b hb
  obtain ⟨ψ,hψ,hstrong,hvalues⟩ := exists_strongly_invariant_with_normal_marginals
    U hU M N hM hN Ω hfix φ₀ hφ₀
    (fun t a => hinv (Multiplicative.ofAdd t) a) hφ₀M hφ₀N
  exact ⟨ψ,hψ,hstrong,fun a ha b hb => (hvalues a ha b hb).trans (hprod₀ a ha b hb)⟩

end

end KadisonKastler

end OAI
