import Mathlib
import OAI.Probability.SKValue.Evolution.EvolutionPatch
import OAI.Probability.SKValue.Evolution.TestEvolution

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma patchTime_testjet {a t x:ℝ} (V W:ℝ → ℝ → ℝ) (n:ℕ) :
    iteratedDeriv n (patchTime a V W t) x=
      patchTime a (fun t ↦ iteratedDeriv n (V t) x) (fun t ↦ iteratedDeriv n (W t) x) t := by
  by_cases ht:t≤a <;> simp [patchTime,ht]

lemma LinearEvolution.rhs_integrable {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hg:IntervalIntegrable γ volume 0 T) (x:ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))) volume 0 T := by
  have h1:ContinuousOn (fun r ↦ deriv (V r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have h2:ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have ha:ContinuousOn (fun r ↦ deriv (A r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using hA.continuous_jet 0 x
  exact ((h2.intervalIntegrable.const_mul _).add (hg.mul_continuousOn (ha.mul h1))).neg

lemma LinearEvolution.patch_pde {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) {s t:ℝ} (hs:s∈Icc (0:ℝ) (a+b)) (ht:t∈Icc (0:ℝ) (a+b)) (x:ℝ) :
    patchTime a V W s x-patchTime a V W t x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (patchTime a V W r)) x+
        patchTime a γ η r*(deriv (patchTime a A B r) x*deriv (patchTime a V W r) x)) := by
  let p := fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))
  let q := fun r ↦ -((1/2:ℝ)*deriv (deriv (W r)) x+η r*(deriv (B r) x*deriv (W r) x))
  have hp := hV.rhs_integrable ha hA hγ x
  have hq := hW.rhs_integrable hb hB hη x
  have hv:∀ t∈Icc (0:ℝ) a,V t x-V 0 x=∫ r in (0:ℝ)..t,p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw:∀ t∈Icc (0:ℝ) b,W t x-W 0 x=∫ r in (0:ℝ)..t,q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr:r≤a <;> simp [patchTime,hr]

lemma LinearEvolution.patch {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) :
    LinearEvolution (a+b) (patchTime a γ η) (patchTime a A B) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta:t≤a
    · rw [patchTime_left V W hta];exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)];exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro n x
    simp_rw [patchTime_testjet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_testjet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_testjet,patchTime_testjet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_pde ha hb hW hA hB hγ hη hjoin hs ht x

noncomputable def profileResponse (ψ f:ℝ → ℝ) : HeatProfile → ℝ → ℝ → ℝ
  | [] => fun _ ↦ f
  | p::l => patchTime (p.1:ℝ)
    (fun t ↦ responseJet (p.2:ℝ) (profileValue ψ l 0) (profileResponse ψ f l 0) 0 ((p.1:ℝ)-t))
    (profileResponse ψ f l)

lemma SmoothTerminal.linear_profile {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f) (l:HeatProfile) :
    LinearEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
  induction l with
  | nil =>
    change LinearEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) (fun _ ↦ f)
    refine ⟨fun t _ ↦ hf,fun _ _ ↦ continuousOn_const,?_,?_,?_⟩
    · intro n
      obtain ⟨C,hC,hb⟩ := hf.bound n
      exact ⟨C,hC,fun _ _ ↦ hb⟩
    · intro n
      exact ⟨0,le_rfl,by intros;simp⟩
    · intro t ht s hs x
      have ht0:t=0 := le_antisymm ht.2 ht.1
      have hs0:s=0 := le_antisymm hs.2 hs.1
      subst t;subst s;simp
  | cons p l ih =>
    have hA := hψ.profile_evolution l
    have hψ' := hA.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hf' := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    apply (hψ'.linear_constant hf' p.2.coe_nonneg (p.1:ℝ)).patch p.1.coe_nonneg (profileTime_nonneg l)
      ih (hψ'.constant_evolution p.2.coe_nonneg (p.1:ℝ)) hA intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,responseJet_zero]

lemma profileResponse_terminal (ψ f:ℝ → ℝ) (l:HeatProfile) :
    profileResponse ψ f l (profileTime l)=f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1:ℝ)+profileTime l)=f
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x;simp only [sub_self,responseJet_zero]
end SKValue

end

end OAI
