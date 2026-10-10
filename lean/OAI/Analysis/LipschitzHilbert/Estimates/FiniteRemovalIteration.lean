import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeForestIntegral

namespace OAI

/-! Finite iteration of proved removal steps, with exact telescoping
packet sums. The step is supplied by the density and size selections. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def finitePacketSum {ι V : Type*} [AddCommMonoid V]
    (v : ι → ℝ×ℝ → V) (S : Finset ι) (z : ℝ×ℝ) : V := ∑ q∈S, v q z

theorem iterate_finite_removal {ι V : Type*} [NormedAddCommGroup V]
    (v : ι → ℝ×ℝ → V) (E : Set (ℝ×ℝ)) (P : ℤ → Finset ι → Prop) (B : ℤ → ℝ)
    (step : ∀ k S, P k S → ∃ T, T⊆S ∧ P (k-1) T ∧
      IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B k)
    (n : ℕ) (k : ℤ) (S : Finset ι) (hS : P k S) :
    ∃ T, T⊆S ∧ P (k-(n:ℤ)) T ∧
      IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤
        ∑ i∈Finset.range n, B (k-(i:ℤ)) := by
  induction n generalizing k S with
  | zero =>
    refine ⟨S,Finset.Subset.refl _,?_,?_,?_⟩
    · simpa only [Nat.cast_zero,sub_zero] using hS
    · simpa only [sub_self] using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ×ℝ => (0:V)) E (volume.prod volume))
    · simp only [sub_self,norm_zero,integral_zero,Finset.range_zero,Finset.sum_empty,le_refl]
  | succ n ih =>
    obtain ⟨U,hUS,hU,hIU,hBU⟩ := step k S hS
    obtain ⟨T,hTU,hT,hIT,hBT⟩ := ih (k-1) U hU
    have heq (z : ℝ×ℝ) : finitePacketSum v S z-finitePacketSum v T z=
        (finitePacketSum v S z-finitePacketSum v U z)+
        (finitePacketSum v U z-finitePacketSum v T z) := by abel
    have hI : IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E
        (volume.prod volume) := (hIU.add hIT).congr (Filter.Eventually.of_forall fun z => (heq z).symm)
    refine ⟨T,hTU.trans hUS,?_,hI,?_⟩
    · convert hT using 1
      push_cast
      ring
    · calc
        _ ≤ ∫ z in E, ‖finitePacketSum v S z-finitePacketSum v U z‖+
            ‖finitePacketSum v U z-finitePacketSum v T z‖ ∂volume.prod volume :=
          integral_mono hI.norm (hIU.norm.add hIT.norm) (fun z => by rw [heq]; exact norm_add_le _ _)
        _ = (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v U z‖ ∂volume.prod volume)+
            (∫ z in E, ‖finitePacketSum v U z-finitePacketSum v T z‖ ∂volume.prod volume) :=
          integral_add hIU.norm hIT.norm
        _ ≤ B k+∑ i∈Finset.range n, B ((k-1)-(i:ℤ)) := add_le_add hBU hBT
        _ = ∑ i∈Finset.range (n+1), B (k-(i:ℤ)) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero,sub_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          push_cast
          ring

theorem finite_removal_zero_remainder {ι V : Type*} [NormedAddCommGroup V]
    (v : ι → ℝ×ℝ → V) (E : Set (ℝ×ℝ)) (S T : Finset ι)
    (hI : IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume))
    (hzero : finitePacketSum v T=ᵐ[(volume.prod volume).restrict E] 0) (B : ℝ)
    (hB : (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B) :
    IntegrableOn (finitePacketSum v S) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z‖ ∂volume.prod volume)≤B := by
  have heq : (fun z => finitePacketSum v S z-finitePacketSum v T z)
      =ᵐ[(volume.prod volume).restrict E] finitePacketSum v S := by
    filter_upwards [hzero] with z hz
    rw [hz,Pi.zero_apply,sub_zero]
  refine ⟨hI.congr heq,?_⟩
  have hn : (fun z => ‖finitePacketSum v S z-finitePacketSum v T z‖)
      =ᵐ[(volume.prod volume).restrict E] fun z => ‖finitePacketSum v S z‖ := by
    filter_upwards [heq] with z hz
    rw [hz]
  exact (integral_congr_ae hn).symm.le.trans hB

end LipschitzHilbert

end

end OAI
