import OAI.MathematicalPhysics.Heisenberg.CubeSelection

namespace OAI

section

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

variable {d ℓ : ℕ}

def averageState {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (ω : I → State d ℓ) : State d ℓ where
  functional:=∑ i,(μ i:ℂ) • (ω i).functional
  normalized:=by
    simp only [sum_apply,smul_apply,smul_eq_mul,State.normalized,mul_one]
    exact_mod_cast hm
  positive:=by
    intro A
    simp only [sum_apply,smul_apply,smul_eq_mul,
      Complex.im_sum,Complex.re_sum,Complex.mul_im,Complex.ofReal_im,zero_mul,add_zero,
      Complex.mul_re,Complex.ofReal_re,sub_zero]
    constructor
    · simp only [(ω _).positive A |>.1,mul_zero,Finset.sum_const_zero]
    · exact Finset.sum_nonneg (fun i _=>mul_nonneg (hμ i) ((ω i).positive A).2)

lemma averageState_apply {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (ω : I → State d ℓ) (A : QuasiLocal d ℓ) :
    (averageState μ hμ hm ω).functional A=∑ i,(μ i:ℂ)*(ω i).functional A := by
  simp only [averageState,sum_apply,smul_apply,smul_eq_mul]

def translationLinear (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ :=
  (translation d ℓ x).toLinearMap.mkContinuous 1 (fun A=>by change ‖translation d ℓ x A‖≤1*‖A‖; rw [norm_translation,one_mul])

@[simp] lemma translationLinear_apply (x : Site d) (A : QuasiLocal d ℓ) :
    translationLinear d ℓ x A=translation d ℓ x A := rfl

def translatedState (ω : State d ℓ) (x : Site d) : State d ℓ where
  functional:=ω.functional.comp (translationLinear d ℓ x)
  normalized:=by simp only [ContinuousLinearMap.comp_apply,translationLinear_apply,map_one,State.normalized]
  positive:=by
    intro A
    simpa only [ContinuousLinearMap.comp_apply,translationLinear_apply,map_mul,map_star] using
      ω.positive (translation d ℓ x A)

lemma diffContOnCl_sum {I : Type*} [Fintype I] {s : Set ℂ} (F : I → ℂ → ℂ)
    (hF : ∀ i,DiffContOnCl ℂ (F i) s) : DiffContOnCl ℂ (fun z=>∑ i,F i z) s := by
  constructor
  · convert DifferentiableOn.sum (u:=Finset.univ) (fun i _=>(hF i).1) using 1
    ext z
    simp only [Finset.sum_apply]
  · exact continuousOn_finsetSum _ (fun i _=>(hF i).2)

lemma norm_convex_sum {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (f : I → ℂ) (C : ℝ) (hf : ∀ i,‖f i‖≤C) :
    ‖∑ i,(μ i:ℂ)*f i‖≤C := by
  calc _ ≤ ∑ i,‖(μ i:ℂ)*f i‖ := norm_sum_le _ _
       _ = ∑ i,μ i*‖f i‖ := by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hμ _)]
       _ ≤ ∑ i,μ i*C := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hf i) (hμ i))
       _ = C := by rw [←Finset.sum_mul,hm,one_mul]

theorem averaged_gibbs_strip {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (x : I → Site d) (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    (K : QuasiLocal d ℓ) (hK : IsSelfAdjoint K) {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z ∈ HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
      (∀ t : ℝ,F t=∑ i,(μ i:ℂ)*(gibbsState τ K β).functional
        (translation d ℓ (x i) A*GibbsStrip.evolve K t (translation d ℓ (x i) B))) ∧
      (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=∑ i,(μ i:ℂ)*(gibbsState τ K β).functional
        (GibbsStrip.evolve K t (translation d ℓ (x i) B)*translation d ℓ (x i) A)) := by
  have hh (i : I):=finite_gibbs_strip τ hτ hK hβ (translation d ℓ (x i) A) (translation d ℓ (x i) B)
  choose F hd hb hzero htop using hh
  refine ⟨fun z=>∑ i,(μ i:ℂ)*F i z,?_,?_,?_,?_⟩
  · apply diffContOnCl_sum
    intro i
    exact ⟨(hd i).1.const_mul _,(hd i).2.const_mul _⟩
  · intro z hz
    apply norm_convex_sum μ hμ hm _ _
    intro i
    simpa only [norm_translation] using hb i z hz
  · intro t
    simp_rw [hzero]
  · intro t
    simp_rw [htop]

end Heisenberg
end
end

end OAI
