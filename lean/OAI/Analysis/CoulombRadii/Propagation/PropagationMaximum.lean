import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.RadialMaxSplice

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationCandidates (B R Z l1 l2 : ℝ) (u H : Position → ℝ) : Fin 3 → Position → ℝ :=
  ![fun x => u x-l1/R^4,fun x => H x-l2/R^4,propagationBarrierOffset B R Z]

def propagationCandidateSources (r R Z : ℝ) (u μ p b : Position → ℝ) : Fin 3 → Position → ℝ :=
  ![fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x),
    fun x => 4*Real.pi*μ x,cutoffReaction R (fun x => Z*coulombKernel x+b x)]

theorem propagation_finite_max_step {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ}
    {u H μ p : Position → ℝ} {U : Set Position} (s : Finset (Fin 3)) (h0 : 0∈s)
    (h1 : 1∈s ↔ ¬bad) (h2 : 2∈s → ∀ x∈U,R<‖x‖)
    (hB : 0<B) (hr : 0<r) (hR : R=2*r) (hL : 0≤L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (he : 0<e) (hξ : 0≤ξ)
    (hξl : ξ<l2) (hgap : 16*ξ+2*e<l1-l2)
    (hhl : hl≤(7/8:ℝ)*B-2*e*(2*L)^4) (hhh : C≤hh)
    (hU : IsOpen U) (hUb : ∀ x∈U,‖x‖≤2*L*R)
    (huc : Continuous u) (hHc : Continuous H)
    (hμ : ∀ x,0≤μ x) (hp : ∀ x,0≤p x)
    (hqi : ∀ i∈s,LocallyIntegrable
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) volume)
    (hb : Measurable (fun x => propagationCoreSource R ‖x‖ (μ x)
      (propagationStepError bad r R ‖x‖ (μ x) (p x))))
    (hbb : ∀ D : ℝ, ∃ K : ℝ, ∀ x∈Metric.closedBall 0 D,
      |propagationCoreSource R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))|≤K)
    (hwu : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z U
      (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)))
    (hwH : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z U (fun x => 4*Real.pi*μ x))
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4)
    (hinv : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → ∀ h∈Icc hl hh,
      (‖x‖^6*μ x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H x)≤h+ξ) ∧
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ x → h-ξ≤‖x‖^4*(Z*coulombKernel x+H x)))
    (hlo : ∀ x∈U,R≤‖x‖ → propagationBarrier B R x≤Z*coulombKernel x+
      s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) :
    WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) Z U
      (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x))) := by
  have hRp : 0<R := by rw [hR]; positivity
  have hrR : r≤R := by rw [hR]; linarith only [hr]
  have hη : 0<e/R^4 := div_pos he (pow_pos hRp 4)
  have hf : ∀ i∈s,Continuous (propagationCandidates B R Z l1 l2 u H i) := by
    intro i hi
    fin_cases i
    · exact huc.sub continuous_const
    · exact hHc.sub continuous_const
    · exact propagationBarrierOffset_continuous B Z hRp
  have hw : ∀ i∈s,WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+propagationCandidates B R Z l1 l2 u H i x) Z U
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) := by
    intro i hi
    fin_cases i
    · exact hwu.sub_offset_const huc (l1/R^4)
    · exact hwH.sub_offset_const hHc (l2/R^4)
    · apply ((propagationBarrier_weak (Z:=Z) hB hRp hsmall).mono_domain (h2 hi)).congr_on (fun x hx => rfl)
      intro x hx
      simp [propagationCandidateSources,cutoffReaction,le_of_lt (h2 hi x hx),propagationBarrierOffset_eq]
  have Hmax := WeakNuclearSubsolution.near_active_cutoffTF s ⟨0,h0⟩
    (propagationCandidates B R Z l1 l2 u H)
    (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z))
    hRp hη hU hf hqi hb hbb hw
  apply (Hmax ?_).congr_on (fun x hx => rfl)
  · intro x hx
    simp [propagationRHS,cutoffReaction,Set.indicator]
  · intro i hi x hx hnear
    change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationCandidates B R Z l1 l2 u H i x) ≤ _
    fin_cases i
    · change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+(u x-l1/R^4)) ≤ propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)
      rw [←add_sub_assoc]
      apply propagation_old_source hrR hRp (hl2.trans hl21)
      intro hbad hrx hRx
      have hcand := Finset.le_sup' (f:=fun j => propagationCandidates B R Z l1 l2 u H j x) ((h1).2 hbad)
      have hn : (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-
          (Z*coulombKernel x+u x-l1/R^4)<2*e/R^4 := by
        change (s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-(u x-l1/R^4)<2*(e/R^4) at hnear
        rw [←mul_div_assoc] at hnear
        linarith only [hnear]
      have hc : Z*coulombKernel x+H x-l2/R^4≤
          Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x) := by
        change H x-l2/R^4 ≤ s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x) at hcand
        linarith only [hcand]
      have hhlo : hl≤(7/8:ℝ)*B := by
        have ht : 0≤2*e*(2*L)^4 := by positivity
        linarith only [hhl,ht]
      exact propagation_near_old_gain (hl:=hl) (hh:=hh) hB.le hr hR hrx hhlo
        hhh (hu x hrx) hξ hgap (fun a ha => (hinv hbad x hrx (hUb x hx) a ha).2) hc hn
    · have hbad := h1.mp hi
      change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+(H x-l2/R^4)) ≤ 4*Real.pi*μ x
      rw [←add_sub_assoc]
      apply @propagation_physical_source _ _ _ _ _ _ _ ξ _ (hμ x) (hp x)
      intro hRx
      have hrx := hrR.trans hRx
      apply propagation_near_physical_reaction hB.le hRp hL he.le hRx (hUb x hx) hhl hhh
        (hH hbad x hrx (hUb x hx)) hξ hl2 hξl (hlo x hx hRx)
      · change (s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-(H x-l2/R^4)<2*(e/R^4) at hnear
        rw [←mul_div_assoc] at hnear
        linarith only [hnear]
      · exact fun a ha => (hinv hbad x hrx (hUb x hx) a ha).1
    · have hRx := (h2 hi x hx).le
      simpa [propagationCandidates,propagationCandidateSources,cutoffReaction,hRx] using
        (propagation_barrier_source (bad:=bad) (r:=r) (v:=Z*coulombKernel x+propagationBarrierOffset B R Z x)
          hRx (hμ x) (hp x))

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationInnerIndices (bad : Prop) : Finset (Fin 3) := if bad then {0} else {0,1}
def propagationMiddleIndices (bad : Prop) : Finset (Fin 3) := insert 2 (propagationInnerIndices bad)

lemma zero_mem_propagationInnerIndices (bad : Prop) : (0:Fin 3)∈propagationInnerIndices bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma one_mem_propagationInnerIndices (bad : Prop) : (1:Fin 3)∈propagationInnerIndices bad ↔ ¬bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma two_not_mem_propagationInnerIndices (bad : Prop) : (2:Fin 3)∉propagationInnerIndices bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma zero_mem_propagationMiddleIndices (bad : Prop) : (0:Fin 3)∈propagationMiddleIndices bad :=
  Finset.mem_insert_of_mem (zero_mem_propagationInnerIndices bad)
lemma one_mem_propagationMiddleIndices (bad : Prop) : (1:Fin 3)∈propagationMiddleIndices bad ↔ ¬bad := by
  simp [propagationMiddleIndices,one_mem_propagationInnerIndices]
lemma two_mem_propagationMiddleIndices (bad : Prop) : (2:Fin 3)∈propagationMiddleIndices bad :=
  Finset.mem_insert_self _ _

lemma propagationInner_sup (bad : Prop) (B R Z l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    (propagationInnerIndices bad).sup' ⟨0,zero_mem_propagationInnerIndices bad⟩
      (fun i => propagationCandidates B R Z l1 l2 u H i x)=propagationPairOffset bad R l1 l2 u H x := by
  by_cases h : bad <;> simp [propagationInnerIndices,propagationCandidates,propagationPairOffset,h]

lemma propagationMiddle_sup (bad : Prop) (B R Z l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    (propagationMiddleIndices bad).sup' ⟨0,zero_mem_propagationMiddleIndices bad⟩
      (fun i => propagationCandidates B R Z l1 l2 u H i x)=
      max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x) := by
  change (insert 2 (propagationInnerIndices bad)).sup' _ _=_
  rw [Finset.sup'_insert ⟨0,zero_mem_propagationInnerIndices bad⟩,propagationInner_sup]
  exact max_comm _ _

end NeutralAtom
end

end

end OAI
