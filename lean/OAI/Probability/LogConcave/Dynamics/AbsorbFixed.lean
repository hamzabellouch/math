import Mathlib
import OAI.Probability.LogConcave.Numerics.ChainTaylor
import OAI.Probability.LogConcave.Dynamics.Squared

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped Classical BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

theorem SquaredAt.absorb_fixed (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Point d) (hf : Measurable f) (c b : Point d) {r D K S B τ : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : Point d → (Fin k → Point d) → Point d) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (hC : SquaredAt μ (stdGaussian (Point d)) f (fun g => c+(r/(2*D)) • g) S)
    (hM : SquaredAt (Measure.pi fun _ : Fin k => stdGaussian (Point d)) (stdGaussian (Point d))
      (M c) (fun g => b+τ • g) B) :
    SquaredAt (μ.prod (Measure.pi fun _ : Fin k => stdGaussian (Point d))) (stdGaussian (Point d))
      (fun z => M (f z.1) (slotTransform (sqrtCoefficient (fun i => v i/(2*D)))
        (fun i => v i/(2*D)) z.2)) (fun g => b+τ • g) (2*K^2*S+2*B) := by
  let γ := stdGaussian (Point d)
  let θ := Measure.pi fun _ : Fin k => γ
  obtain ⟨κ,hκ,hcl,hcr,hci,hce⟩ := hC
  let := hκ
  have hMR := hM.reindex (fun g => ((),g)) id (by fun_prop) measurable_id
    (fun z : Unit × (Fin k → Point d) => M c z.2) (fun g => b+τ • g)
    (hm.comp (measurable_const.prodMk measurable_snd)) (by fun_prop) (by intro; rfl) (by intro; rfl)
  rw [←Measure.dirac_prod (),Measure.map_id] at hMR
  obtain ⟨π,hπ,hpl,hpr,hpi,hpe⟩ := hMR
  let := hπ
  have hlaw : κ.map (fun z : Ω × Point d => ((),z.2))=(Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hcr]
    change _=(κ.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  have hnoise : π.map (fun z : (Unit × (Fin k → Point d)) × Point d => (z.1.1,z.2))=
      (Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hpr]
    change _=(π.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  obtain ⟨Λ,hΛ,hLl,hLr,hLi,hLe⟩ := absorb_coupling κ (Measure.dirac ()) γ
    (fun _ => ()) Prod.snd (fun z => f z.1) measurable_const measurable_snd
    (hf.comp measurable_fst) hlaw (fun _ => c) measurable_const hD hK v hv M hm hshift hLip
    (fun _ g => b+τ • g) (by fun_prop) hci hce π hpl hnoise hpi hpe
  let := hΛ
  let T : ((Ω × Point d) × (Fin k → Point d)) × Point d → Ω × (Fin k → Point d) :=
    fun z => (z.1.1.1,z.1.2)
  have hT : Measurable T := by unfold T; fun_prop
  have hTl : Λ.map T=μ.prod θ := by
    change Λ.map ((Prod.map Prod.fst id) ∘ Prod.fst)=_
    rw [←Measure.map_map (by fun_prop) measurable_fst]
    change Λ.fst.map (Prod.map Prod.fst id)=_
    rw [hLl,←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod θ=μ.prod θ
    rw [hcl]
  have hLright : Λ.map Prod.snd=γ := by
    have H := congrArg (Measure.map Prod.snd) hLr
    rw [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod] at H
    simpa only [Function.comp_def,measure_univ,one_smul] using H
  exact SquaredAt.of_joint Λ (μ.prod θ) γ T Prod.snd hT measurable_snd hTl hLright
    _ _ (hm.comp ((hf.comp measurable_fst).prodMk (by
      dsimp only [slotTransform,slotSum]; fun_prop))) (by fun_prop) hLi hLe
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {ι : Type*} [Fintype ι] {Ω Γ : ι → Type*}
  [∀i,MeasurableSpace (Ω i)] [∀i,MeasurableSpace (Γ i)] {d : ℕ}

theorem SquaredAt.weighted_pi (μ : ∀i,Measure (Ω i)) (ν : ∀i,Measure (Γ i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (f : ∀i,Ω i → Point d) (g : ∀i,Γ i → Point d)
    (hf : ∀i,Measurable (f i)) (hg : ∀i,Measurable (g i))
    (w B : ι → ℝ) (h : ∀i,SquaredAt (μ i) (ν i) (f i) (g i) (B i)) :
    SquaredAt (Measure.pi μ) (Measure.pi ν)
      (fun z => ∑i,w i • f i (z i)) (fun z => ∑i,w i • g i (z i))
      ((∑i,|w i|)*(∑i,|w i| * B i)) := by
  choose κ hκ hl hr hi he using h
  let : ∀i,IsProbabilityMeasure (κ i) := hκ
  let Λ := Measure.pi κ
  let T : (∀i,Ω i × Γ i) → (∀i,Ω i) := fun z i => (z i).1
  let U : (∀i,Ω i × Γ i) → (∀i,Γ i) := fun z i => (z i).2
  have hT : Measurable T := by unfold T; fun_prop
  have hU : Measurable U := by unfold U; fun_prop
  have hTl : Λ.map T=Measure.pi μ :=
    (measurePreserving_pi κ μ (fun i => ⟨measurable_fst,hl i⟩)).map_eq
  have hUl : Λ.map U=Measure.pi ν :=
    (measurePreserving_pi κ ν (fun i => ⟨measurable_snd,hr i⟩)).map_eq
  have hm (i : ι) : Measurable (fun z : Ω i × Γ i => f i z.1-g i z.2) := by fun_prop
  have hip (i : ι) : Integrable (fun z : ∀i,Ω i × Γ i => ‖f i (z i).1-g i (z i).2‖^2) Λ :=
    (measurePreserving_eval κ i).integrable_comp_of_integrable (hi i)
  have hep (i : ι) : (∫z : ∀i,Ω i × Γ i,‖f i (z i).1-g i (z i).2‖^2 ∂Λ)≤B i := by
    exact ((measurePreserving_eval κ i).hasLaw.integral_comp
      ((hm i).norm.pow_const 2).aestronglyMeasurable).trans_le (he i)
  have hs := RMSIntegral.weighted_sum_sq_varying w
    (fun i (z : ∀i,Ω i × Γ i) => f i (z i).1-g i (z i).2) B
    (fun i => ((hm i).comp (measurable_pi_apply i)).aestronglyMeasurable) hip hep
  have hid (z : ∀i,Ω i × Γ i) :
      (∑i,w i • f i (T z i))-(∑i,w i • g i (U z i))=
        ∑i,w i • (f i (z i).1-g i (z i).2) := by
    simp only [T,U,smul_sub,Finset.sum_sub_distrib]
  refine SquaredAt.of_joint Λ (Measure.pi μ) (Measure.pi ν) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hid] using hs.1
  · simpa only [hid] using hs.2
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W] {d : ℕ}

theorem SquaredAt.common_noise {μ : Measure Ω} {ν : Measure Γ}
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (h : SquaredAt μ ν f g B) (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hnoise : W → Point d) (hm : Measurable hnoise) :
    SquaredAt (μ.prod ρ) (ν.prod ρ) (fun z => f z.1+hnoise z.2)
      (fun z => g z.1+hnoise z.2) B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  let := hκ
  let T : (Ω × Γ) × W → Ω × W := Prod.map Prod.fst id
  let U : (Ω × Γ) × W → Γ × W := Prod.map Prod.snd id
  have hT : Measurable T := by fun_prop
  have hU : Measurable U := by fun_prop
  have hTl : (κ.prod ρ).map T=μ.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod ρ=μ.prod ρ
    rw [hl]
  have hUl : (κ.prod ρ).map U=ν.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
    change κ.snd.prod ρ=ν.prod ρ
    rw [hr]
  have hcost (z : (Ω × Γ) × W) :
      ‖(f (T z).1+hnoise (T z).2)-(g (U z).1+hnoise (U z).2)‖^2=‖f z.1.1-g z.1.2‖^2 := by
    dsimp only [T,U,Prod.map]; rw [add_sub_add_right_eq_sub]
  refine SquaredAt.of_joint (κ.prod ρ) (μ.prod ρ) (ν.prod ρ) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hcost] using hi.comp_fst ρ
  · simp_rw [hcost]
    rw [integral_prod _ (hi.comp_fst ρ)]
    simpa only [integral_const,probReal_univ,one_smul] using he
end LogConcaveSampling.Coupling

end

end

end OAI
