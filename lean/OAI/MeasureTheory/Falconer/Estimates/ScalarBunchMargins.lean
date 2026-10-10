import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchSizes

namespace OAI

/-! Each discarded porous level contributes a full block of geometric
 separation. These bounds use the actual increasing endpoint indices. -/
namespace Falconer

 theorem scalar_increasing_endpoint_gap (e : ℕ → ℕ) (he : StrictMono e)
    {a b : ℕ} (hab : a ≤ b) : e a+(b-a) ≤ e b := by
  have hh := he.add_le_nat (b-a) a
  simpa only [Nat.sub_add_cancel hab,Nat.add_comm] using hh

 theorem scalar_bunch_margin (e n : ℕ → ℕ) (he : StrictMono e) (B C : ℕ)
    (b : ScalarBunch) (hporous : n (e b.cut-1)+C ≤ B*e b.cut) :
    n (e b.cut-1)+(C+B*(b.stop-b.cut)) ≤ B*e b.stop := by
  have hg := Nat.mul_le_mul_left B (scalar_increasing_endpoint_gap e he b.cut_le_stop)
  rw [Nat.mul_add] at hg
  omega

 theorem scalar_bunch_long_margin (e n : ℕ → ℕ) (he : StrictMono e) (B C : ℕ)
    {b : ScalarBunch} {w : ℕ → ℝ} {theta : ℝ}
    (hgood : ScalarBunchGood w theta b)
    (hporous : n (e b.cut-1)+C ≤ B*e b.cut) :
    (b.stop = b.cut ∧ b.stop-b.start ≤ 1000 ∧
      n (e b.cut-1)+C ≤ B*e b.stop) ∨
    (b.stop-b.start ≤ 200*(b.stop-b.cut) ∧
      n (e b.cut-1)+(C+B*(b.stop-b.cut)) ≤ B*e b.stop) := by
  rcases hgood.gap with ⟨hcut,hlen⟩ | hlen
  · left
    exact ⟨hcut,hlen,by simpa only [hcut] using hporous⟩
  · right
    exact ⟨hlen,scalar_bunch_margin e n he B C b hporous⟩

end Falconer

end OAI
