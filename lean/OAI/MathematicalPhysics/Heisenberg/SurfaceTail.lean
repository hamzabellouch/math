import OAI.MathematicalPhysics.Heisenberg.PinnedMagnetization

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pinned_sum_le_trace (π : Equiv.Perm V) (P : Set V) (f : (V → Bool) → ℝ)
    (hf : ∀ c,0≤f c) :
    (∑ c : PinnedColor π P,f c.val)≤Matrix.trace (SlotColor.matrix π * Matrix.diagonal f) := by
  rw [←pinned_trace,SlotColor.trace_diagonal,SlotColor.trace_diagonal]
  apply Finset.sum_le_sum
  intro c _
  split_ifs <;> simp_all

def colorTail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (C : Finset V) : ℝ :=
  ∑ ω,μ ω * Matrix.trace (SlotColor.matrix (π ω) *
    Matrix.diagonal (fun c=>if C.card/4≤cutSpin C c then (1:ℝ) else 0))

lemma normalized_pinned_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) (C : Finset V) :
    (∑ ω,∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0)=
    (∑ ω,μ ω*∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then (1:ℝ) else 0)/pinPartition μ π P := by
  simp_rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem color_surface_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (hC : C.Nonempty) (p : ℝ) (hp : p≤1/4)
    (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p)
    (K : ℝ) (hK : (∑ ω,pinDensity μ π ∅ ω*((hitClasses (π ω) P).card:ℝ))≤K) :
    Real.exp (-(Real.log 2)*K)/2 ≤ colorTail μ π C/pinPartition μ π ∅ := by
  have hpin:=pinned_cut_tail μ π hμ hpos P C hC p hp hmiss
  rw [normalized_pinned_tail] at hpin
  have hZP:=pinPartition_pos μ π hμ hpos P
  have hZ0:=pinPartition_pos μ π hμ hpos ∅
  have hsum : (∑ ω,μ ω*∑ c : PinnedColor (π ω) P,if C.card/4≤cutSpin C c.val then (1:ℝ) else 0)≤colorTail μ π C := by
    apply Finset.sum_le_sum
    intro ω _
    exact mul_le_mul_of_nonneg_left (pinned_sum_le_trace (π ω) P (fun c=>if C.card/4≤cutSpin C c then 1 else 0) (fun c=>by split_ifs <;> norm_num)) (hμ ω)
  have hpin' : pinPartition μ π P/2≤colorTail μ π C := by
    have hh:=(le_div_iff₀ hZP).mp hpin
    linarith
  have hsurface:=partition_surface_lower μ π hμ hpos P K hK
  have hh:=div_le_div_of_nonneg_right hpin' hZ0.le
  rw [div_right_comm] at hh
  linarith

end Heisenberg.Surface
end
end

end OAI
