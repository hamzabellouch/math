import OAI.MathematicalPhysics.Heisenberg.PinnedColors

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def cutSpin (C : Finset V) (c : V → Bool) : ℝ := ∑ i∈C,halfSpin (c i)

omit [Fintype V] in
lemma cutSpin_le (C : Finset V) (c : V → Bool) : cutSpin C c≤C.card/2 := by
  calc
    _ ≤ ∑ _i∈C,(1:ℝ)/2 := by
      apply Finset.sum_le_sum
      intro i _
      cases c i <;> norm_num [halfSpin]
    _ = _ := by simp [div_eq_mul_inv]

lemma sum_pinned_cutSpin (π : Equiv.Perm V) (P : Set V) (C : Finset V) :
    (∑ c : PinnedColor π P,cutSpin C c.val)=
      (2:ℝ)^missingCount π P/2 * ∑ i∈C,if HasHit π P i then (1:ℝ) else 0 := by
  unfold cutSpin
  rw [Finset.sum_comm]
  simp_rw [sum_pinned_spin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma pinned_color_normalization (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) :
    (∑ ω,∑ _c : PinnedColor (π ω) P,μ ω/pinPartition μ π P)=1 := by
  simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pinnedColor]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  have he : (∑ ω,(2:ℝ)^missingCount (π ω) P*μ ω)=pinPartition μ π P := by
    unfold pinPartition
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [←mul_div_assoc]
  rw [←Finset.sum_div,he,div_self (ne_of_gt (pinPartition_pos μ π hμ hpos P))]

lemma mean_pinned_cutSpin (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (p : ℝ) (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p) :
    (1-p)*C.card/2 ≤ ∑ ω,∑ c : PinnedColor (π ω) P,
      μ ω/pinPartition μ π P*cutSpin C c.val := by
  have he : (∑ ω,∑ c : PinnedColor (π ω) P,μ ω/pinPartition μ π P*cutSpin C c.val)=
      (∑ i∈C,(1-(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0))/2) := by
    simp_rw [←Finset.mul_sum,sum_pinned_cutSpin,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hh (ω : Ω) : μ ω/pinPartition μ π P*((2:ℝ)^missingCount (π ω) P/2 *
        (if HasHit (π ω) P i then 1 else 0))=
        (pinDensity μ π P ω-(if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0))/2 := by
      unfold pinDensity
      split_ifs <;> simp_all
      ring
    simp_rw [hh]
    rw [←Finset.sum_div,Finset.sum_sub_distrib,pinDensity_sum μ π hμ hpos P]
  rw [he]
  calc
    _ = ∑ _i∈C,(1-p)/2 := by simp [div_eq_mul_inv]; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi=>by linarith [hmiss i hi])

theorem pinned_cut_tail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0≤μ ω) (hpos : 0<∑ ω,μ ω) (P : Set V) (C : Finset V)
    (hC : C.Nonempty) (p : ℝ) (hp : p≤1/4)
    (hmiss : ∀ i∈C,(∑ ω,if ¬HasHit (π ω) P i then pinDensity μ π P ω else 0)≤p) :
    (1:ℝ)/2 ≤ ∑ ω,∑ c : PinnedColor (π ω) P,
      if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0 := by
  have hZ:=pinPartition_pos μ π hμ hpos P
  have hmean:=mean_pinned_cutSpin μ π hμ hpos P C p hmiss
  have hn:=pinned_color_normalization μ π hμ hpos P
  have hu : (∑ ω,∑ c : PinnedColor (π ω) P,μ ω/pinPartition μ π P*cutSpin C c.val)≤
      C.card/4+(C.card/4)*(∑ ω,∑ c : PinnedColor (π ω) P,
      if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0) := by
    calc
      _ ≤ ∑ ω,∑ c : PinnedColor (π ω) P,((μ ω/pinPartition μ π P)*(C.card/4)+
          C.card/4*(if C.card/4≤cutSpin C c.val then μ ω/pinPartition μ π P else 0)) := by
        apply Finset.sum_le_sum
        intro ω _
        apply Finset.sum_le_sum
        intro c _
        have hw:=div_nonneg (hμ ω) hZ.le
        split_ifs with hh
        · have hh':=mul_le_mul_of_nonneg_left (cutSpin_le C c.val) hw
          nlinarith
        · have hh':=mul_le_mul_of_nonneg_left (le_of_not_ge hh) hw
          nlinarith
      _ = _ := by
        simp_rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
        rw [hn]
        ring
  have hcard : (0:ℝ)<C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hprod:=mul_le_mul_of_nonneg_right hp hcard.le
  nlinarith

end Heisenberg.Surface
end
end

end OAI
