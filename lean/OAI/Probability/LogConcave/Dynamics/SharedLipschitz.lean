import Mathlib
import OAI.Probability.LogConcave.Dynamics.Squared

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d e : ℕ}

theorem SquaredAt.shared_lipschitz {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Measure W) [IsProbabilityMeasure η]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B K : ℝ} (hK : 0≤K) (hc : SquaredAt μ ν f g B)
    (H : Point d → W → Point e) (hH : Measurable (uncurry H))
    (hLip : ∀x y w,‖H x w-H y w‖≤K*‖x-y‖) :
    SquaredAt (μ.prod η) (ν.prod η) (fun z => H (f z.1) z.2)
      (fun z => H (g z.1) z.2) (K^2*B) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := hc
  let := hκ
  let Λ := κ.prod η
  have hΛf : Λ.map (fun z => (z.1.1,z.2))=μ.prod η := by
    rw [show (fun z : (Ω × Γ) × W => (z.1.1,z.2))=Prod.map Prod.fst id from rfl]
    rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    exact congrArg (fun m => m.prod η) hl
  have hΛg : Λ.map (fun z => (z.1.2,z.2))=ν.prod η := by
    rw [show (fun z : (Ω × Γ) × W => (z.1.2,z.2))=Prod.map Prod.snd id from rfl]
    rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
    exact congrArg (fun m => m.prod η) hr
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
  have hi' : Integrable (fun z : (Ω × Γ) × W => ‖f z.1.1-g z.1.2‖^2) Λ := hi.comp_fst η
  have hp (z : (Ω × Γ) × W) : ‖H (f z.1.1) z.2-H (g z.1.2) z.2‖^2≤
      K^2*‖f z.1.1-g z.1.2‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hLip _ _ _) 2
  have hcmeas : Measurable (fun z : (Ω × Γ) × W => ‖H (f z.1.1) z.2-H (g z.1.2) z.2‖^2) := by
    have h₁ : Measurable (fun z : (Ω × Γ) × W => H (f z.1.1) z.2) := hH.comp ((hf.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have h₂ : Measurable (fun z : (Ω × Γ) × W => H (g z.1.2) z.2) := hH.comp ((hg.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    exact (h₁.sub h₂).norm.pow_const 2
  have hdom := hi'.const_mul (K^2)
  have hIi := hdom.mono' hcmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs,abs_sq] using hp z)
  refine SquaredAt.of_joint Λ (μ.prod η) (ν.prod η)
    (fun z => (z.1.1,z.2)) (fun z => (z.1.2,z.2)) (by fun_prop) (by fun_prop)
    hΛf hΛg _ _ ?_ ?_ hIi ?_
  · exact hH.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  · exact hH.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  · apply (integral_mono hIi hdom hp).trans
    rw [integral_const_mul]
    have hfst : ∫z : (Ω × Γ) × W, ‖f z.1.1-g z.1.2‖^2 ∂Λ = ∫z, ‖f z.1-g z.2‖^2 ∂κ := by
      exact (measurePreserving_fst (μ:=κ) (ν:=η)).hasLaw.integral_comp hm.aestronglyMeasurable
    rw [hfst]
    exact mul_le_mul_of_nonneg_left he (pow_nonneg hK 2)

lemma SquaredAt.add_shared {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Measure W) [IsProbabilityMeasure η]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hc : SquaredAt μ ν f g B) (h : W → Point d) (hh : Measurable h) :
    SquaredAt (μ.prod η) (ν.prod η) (fun z => f z.1+h z.2) (fun z => g z.1+h z.2) B := by
  simpa only [one_pow,one_mul] using hc.shared_lipschitz η hf hg (by norm_num : (0:ℝ)≤1)
    (fun x w => x+h w) (by fun_prop) (fun x y w => by rw [add_sub_add_right_eq_sub,one_mul])

end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {X Ω Γ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]
  {d : ℕ}

theorem SquaredAt.mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (θ : Measure Γ) [IsProbabilityMeasure θ]
    (K : Kernel X (Ω × Γ)) [IsMarkovKernel K]
    (hl : ∀x,(K x).fst=ν) (hr : ∀x,(K x).snd=θ)
    (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable (uncurry g))
    (B : X → ℝ) (hB : Integrable B μ)
    (hi : ∀x,Integrable (fun z => ‖f x z.1-g x z.2‖^2) (K x))
    (he : ∀x,(∫z,‖f x z.1-g x z.2‖^2 ∂K x)≤B x) :
    SquaredAt (μ.prod ν) (μ.prod θ) (uncurry f) (uncurry g) (∫x,B x ∂μ) := by
  let Λ := μ ⊗ₘ K
  let F : X × (Ω × Γ) → ℝ := fun z => ‖f z.1 z.2.1-g z.1 z.2.2‖^2
  have hF : Measurable F := by unfold F; fun_prop
  have hFi : Integrable (fun x => ∫z,F (x,z) ∂K x) μ := by
    apply hB.mono' hF.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact he x)
  have hI : Integrable F Λ := by
    apply (Measure.integrable_compProd_iff hF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi,?_⟩
    simpa only [F,Real.norm_eq_abs,abs_sq] using hFi
  have hleft : K.map Prod.fst=Kernel.const X ν := by
    ext x s hs
    rw [Kernel.map_apply _ measurable_fst]
    exact congrArg (fun m : Measure Ω => m s) (hl x)
  have hright : K.map Prod.snd=Kernel.const X θ := by
    ext x s hs
    rw [Kernel.map_apply _ measurable_snd]
    exact congrArg (fun m : Measure Γ => m s) (hr x)
  apply SquaredAt.of_joint Λ (μ.prod ν) (μ.prod θ)
    (fun z => (z.1,z.2.1)) (fun z => (z.1,z.2.2)) (by fun_prop) (by fun_prop)
    ?_ ?_ (uncurry f) (uncurry g) hf hg hI
  · change (∫z,F z ∂Λ)≤_
    rw [Measure.integral_compProd hI]
    exact integral_mono hFi hB he
  · change Λ.map (Prod.map id Prod.fst)=_
    dsimp only [Λ]
    rw [←Measure.compProd_map measurable_fst,hleft,Measure.compProd_const]
  · change Λ.map (Prod.map id Prod.snd)=_
    dsimp only [Λ]
    rw [←Measure.compProd_map measurable_snd,hright,Measure.compProd_const]
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function Set TopologicalSpace
open scoped Classical

variable {X Ω Γ : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]
  {d : ℕ}

theorem SquaredAt.random_anchor (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (θ : Measure Γ) [IsProbabilityMeasure θ]
    (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable (uncurry g))
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y z,‖g x z-g y z‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν θ (f x) (g x) (E^2*(ρ x)^2)) :
    SquaredAt (μ.prod ν) (μ.prod θ) (uncurry f) (uncurry g)
      (10*E^2*(∫x,(ρ x)^2 ∂μ)) := by
  let e := min 1 (E/(Lf+Lg+1))
  have hden : 0<Lf+Lg+1 := by linarith
  have he : 0<e := lt_min (by norm_num) (div_pos hE hden)
  have he1 : e≤1 := min_le_left _ _
  have heE : (Lf+Lg)*e≤E := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (1:ℝ) (E/(Lf+Lg+1)))
    change e*(Lf+Lg+1)≤E at hh
    nlinarith
  obtain ⟨q,hq,hqe,K,hK,hcouple⟩ := measurable_coupling_of_pointwise ν θ f g hf hg
    (fun x => E^2*(ρ x)^2) hLf hLg he hfl hgl hc
  let := hK
  have hb (x) : 2*(E^2*(ρ (denseSeq X (q x)))^2)+2*((Lf+Lg)*e)^2≤10*E^2*(ρ x)^2 := by
    have hh : ρ (denseSeq X (q x)) ≤ ρ x + e := by
      calc
        _ ≤ ρ x + dist x (denseSeq X (q x)) := hρlip _ _
        _ ≤ ρ x + e := by gcongr; exact (hqe x).le
    have hρx := hρ x
    have hρy := hρ (denseSeq X (q x))
    have hy : (ρ (denseSeq X (q x)))^2≤4*(ρ x)^2 := by nlinarith
    have hys := mul_le_mul_of_nonneg_left hy (sq_nonneg E)
    have hz : ((Lf+Lg)*e)^2≤E^2 := pow_le_pow_left₀ (by positivity) heE 2
    nlinarith [sq_nonneg E,mul_nonneg (sq_nonneg E) (show 0≤(ρ x)^2-1 by nlinarith)]
  have hm := SquaredAt.mixture μ ν θ K (fun x => (hcouple x).1) (fun x => (hcouple x).2.1)
    f g hf hg (fun x => 10*E^2*(ρ x)^2) (hρi.const_mul _) (fun x => (hcouple x).2.2.1)
    (fun x => (hcouple x).2.2.2.trans (hb x))
  simpa only [integral_const_mul] using hm

end LogConcaveSampling.Coupling

end

end

end OAI
