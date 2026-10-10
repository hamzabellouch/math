import Mathlib
import OAI.Probability.SKValue.Equations.CoupledDensity
import OAI.Probability.SKValue.Equations.TestPatch
import OAI.Probability.SKValue.Evolution.DensityPairing

namespace OAI

section
open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma BackwardShape.profile {A:ℝ → ℝ} {M c : ℝ} (hA:SmoothTerminal A) (hB:BackwardShape M A)
    (hM : 0<M) (hc : 0<c) (hcM : c≤M)
    {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2))
    (hlow : ∀ p∈l,c≤(p.2:ℝ)) (hupp : ∀ p∈l,(p.2:ℝ)≤M) (t : ℝ) :
    BackwardShape c (profileValue A l t) := by
  induction l generalizing c t with
  | nil => exact hB.lower hM hc.le hcM
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    have hcp : c≤(p.2:ℝ) := hlow p (by simp)
    have hp0 : 0<(p.2:ℝ) := hc.trans_le hcp
    have hpM : (p.2:ℝ)≤M := hupp p (by simp)
    have hlo : ∀ q∈l,c≤(q.2:ℝ) := fun q hq ↦ hlow q (by simp [hq])
    have hup : ∀ q∈l,(q.2:ℝ)≤M := fun q hq ↦ hupp q (by simp [hq])
    change BackwardShape c (patchTime (p.1:ℝ) _ _ t)
    by_cases ht : t≤(p.1:ℝ)
    · rw [patchTime_left _ _ ht]
      have hs := ih hp0 hpM hl (fun q hq ↦ by exact_mod_cast hp q hq) hup 0
      have hψ := hA.profile_evolution l
      have hsm := hψ.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
      exact (hs.evolve hsm hp0 (sub_nonneg.mpr ht)).lower hp0 hc.le hcp
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih hc hcM hl hlo hup _

end SKValue

end

section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SKValue
lemma profileValue_zero_cons (A:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileValue A (p::l) 0=coleHopf p.2 p.1 (profileValue A l 0) := by
  simp only [profileValue,patchTime_left _ _ p.1.coe_nonneg,sub_zero]
lemma profileResponse_zero_cons (A f:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileResponse A f (p::l) 0=responseJet p.2 (profileValue A l 0) (profileResponse A f l 0) 0 p.1 := by
  simp only [profileResponse,patchTime_left _ _ p.1.coe_nonneg,sub_zero]

lemma ForwardShape.profile {A:ℝ → ℝ} {C d:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) (hd:0<d) (hdC:d≤C) {l:HeatProfile}
    (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) (hlo:∀ p∈l,d≤(p.2:ℝ))
    (hup:∀ p∈l,(p.2:ℝ)≤C) {D:ForwardDensityData}
    (hF:ForwardShape d (profileValue A l 0) D) :
    ∃ E:ForwardDensityData,ForwardShape C A E ∧ ∀ f:ℝ → ℝ,BoundedSmooth f →
      (∫ x,(Real.exp (d*profileValue A l 0 x)*D.weight x)*profileResponse A f l 0 x)=
        ∫ x,(Real.exp (C*A x)*E.weight x)*f x := by
  induction l generalizing d D with
  | nil =>
    let E:=D.jump hA hB.even (C-d) (sub_nonneg.mpr hdC)
    refine ⟨E,hF.jump hA (hB.lower (hd.trans_le hdC) hd.le hdC) hd hdC,?_⟩
    intro f hf
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ForwardDensityData.jump_density _ _ _ hdC]
    rfl
  | cons p l ih =>
    have hdp:d≤(p.2:ℝ) := hlo p (by simp)
    have hp:0<(p.2:ℝ) := hd.trans_le hdp
    have hpC:(p.2:ℝ)≤C := hup p (by simp)
    obtain ⟨hpl,hll⟩:=List.pairwise_cons.mp hl
    have hpl':∀ q∈l,(p.2:ℝ)≤(q.2:ℝ) := fun q hq ↦ by exact_mod_cast hpl q hq
    have hup':∀ q∈l,(q.2:ℝ)≤C := fun q hq ↦ hup q (by simp [hq])
    let B:=profileValue A l 0
    have hBs:SmoothTerminal B := (hA.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hBb:BackwardShape p.2 B := hB.profile hA (hd.trans_le hdC) hp hpC hll hpl' hup' 0
    let V:=profileValue A (p::l) 0
    have hVs:SmoothTerminal V := (hA.profile_evolution (p::l)).slices 0 ⟨le_rfl,profileTime_nonneg _⟩
    have hVb:BackwardShape d V := hB.profile hA (hd.trans_le hdC) hd hdC hl hlo hup 0
    let D':=D.jump hVs hVb.even ((p.2:ℝ)-d) (sub_nonneg.mpr hdp)
    have hF':ForwardShape p.2 V D' := hF.jump hVs hVb hd hdp
    have hstart:ForwardShape p.2 (coleHopf p.2 p.1 B) D' := by
      simpa only [V,profileValue_zero_cons] using hF'
    have hend:ForwardShape p.2 B (D'.evolve p.1 p.1.coe_nonneg) :=
      hstart.evolve hBs hBb hp p.1.coe_nonneg
    obtain ⟨E,hE,hpair⟩:=ih hp hpC hll hpl' hup' hend
    refine ⟨E,hE,?_⟩
    intro f hf
    have htest:BoundedSmooth (profileResponse A f l 0) :=
      (hA.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    calc
      _ = ∫ x,(Real.exp ((p.2:ℝ)*V x)*D'.weight x)*profileResponse A f (p::l) 0 x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [ForwardDensityData.jump_density _ _ _ hdp]
      _ = ∫ x,(Real.exp ((p.2:ℝ)*B x)*(D'.evolve p.1 p.1.coe_nonneg).weight x)*profileResponse A f l 0 x := by
        rw [profileResponse_zero_cons]
        change (∫ x,(Real.exp ((p.2:ℝ)*profileValue A (p::l) 0 x)*D'.weight x)*_) = _
        rw [profileValue_zero_cons]
        exact D'.response_pairing hBs htest hp p.1.coe_nonneg
      _ = _ := hpair f hf

lemma BackwardShape.profile_density {A:ℝ → ℝ} {C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) {p:ℝ≥0 × ℝ≥0} {l:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:(p::l).Pairwise (fun p q ↦ p.2≤q.2)) (hup:∀ q∈p::l,(q.2:ℝ)≤C) :
    ∃ E:ForwardDensityData,ForwardShape C A E ∧ ∀ f:ℝ → ℝ,BoundedSmooth f →
      profileResponse A f (p::l) 0 0=Real.exp (-((p.2:ℝ)*profileValue A (p::l) 0 0))*
        (∫ x,(Real.exp (C*A x)*E.weight x)*f x) := by
  obtain ⟨hpl,hll⟩:=List.pairwise_cons.mp hl
  have hpC:(p.2:ℝ)≤C := hup p (by simp)
  have hpl':∀ q∈l,(p.2:ℝ)≤(q.2:ℝ) := fun q hq ↦ by exact_mod_cast hpl q hq
  have hup':∀ q∈l,(q.2:ℝ)≤C := fun q hq ↦ hup q (by simp [hq])
  have hBs:SmoothTerminal (profileValue A l 0) := (hA.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
  have hBb:BackwardShape p.2 (profileValue A l 0) := hB.profile hA (hp.trans_le hpC) hp hpC hll hpl' hup' 0
  have hF:=hBb.gaussian_forwardShape hBs ht
  obtain ⟨E,hE,hpair⟩:=hF.profile hA hB hp hpC hll hpl' hup'
  refine ⟨E,hE,?_⟩
  intro f hf
  rw [profileResponse_zero_cons,profileValue_zero_cons]
  have htest:BoundedSmooth (profileResponse A f l 0) := (hA.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
  rw [first_response_density hBs htest hp ht,hpair f hf]
end SKValue

end

end OAI
