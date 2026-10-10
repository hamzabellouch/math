import OAI.MeasureTheory.Falconer.Recursion.ProfileIntervalChain

namespace OAI

/-! Apply interval gains to an ordered subfamily; omitted gaps use the
nonempty-pencil estimate. No gain or profile hypothesis is imposed on a gap. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

def OrderedBlockIntervals (i j : ℕ) : List (ℕ × ℕ) → Prop
  | [] => j ≤ i
  | (a,b)::R => a ≤ i ∧ b ≤ a ∧ OrderedBlockIntervals b j R

theorem OrderedBlockIntervals.end_le {i j : ℕ} {R : List (ℕ × ℕ)}
    (h : OrderedBlockIntervals i j R) : j ≤ i := by
  induction R generalizing i with
  | nil => exact h
  | cons c R ih => exact (ih h.2.2).trans (h.2.1.trans h.1)

theorem profileEndpointBound_ordered_intervals {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (R : List (ℕ × ℕ)) (i j : ℕ) (hR : OrderedBlockIntervals i j R) (hi : i ≤ K)
    (F : ℕ × ℕ → ℝ) (hF : ∀ c ∈ R, 0 ≤ F c)
    (W : ℕ → ℝ) (hW : ∀ k, 1 ≤ W k) (hWmono : Monotone W)
    (hWstep : ∀ k, W (k+1) = profileStepBudget (4*(N+2)+11:ℕ)
      ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) (W k))
    (hbase : ∀ c ∈ R, ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) (F c)) :
    ProfileEndpointBound N B K L f p Q i j s (W 0)
      ((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length)) := by
  induction R generalizing i W with
  | nil => simpa using profileEndpointBound_trivial N B K L f p Q i j s (W 0)
  | cons c R ih =>
    obtain ⟨hci,hcc,hrest⟩ := hR
    have hcK : c.1 ≤ K := hci.trans hi
    have hdK : c.2 ≤ K := hcc.trans hcK
    have hhead := (hbase c (by simp)).mono_budget
      (hWmono (show 2 ≤ 2*(c::R).length by simp))
    have htail := ih c.2 hrest hdK (fun c hc => hF c (by simp [hc]))
      (fun k => W (k+2)) (fun k => hW (k+2))
      (fun a b hab => hWmono (Nat.add_le_add_right hab 2))
      (fun k => by simpa only [Nat.add_assoc] using hWstep (k+2)) (by
        intro d hd
        have hh := hbase d (by simp [hd])
        exact hh)
    have htail0 : 0 ≤ (R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) := by
      apply div_nonneg
      · apply List.prod_nonneg
        intro x hx
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
        exact hF d (by simp [hd])
      · positivity
    have hFc : 0 ≤ F c := hF c (by simp)
    rw [hWstep 1] at hhead htail
    have hmid := profileEndpointBound_split hL f p Q hQ hrest.end_le hcc hcK
      hs hs1 (hW 1) hFc htail0 hhead htail
    have hmid0 : 0 ≤ F c*((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length))/
        (43264*((4*(N+2)+11:ℕ):ℝ)^4) := by positivity
    have hgap := profileEndpointBound_trivial N B K L f p Q i c.1 s (W 1)
    rw [hWstep 0] at hgap hmid
    have hh := profileEndpointBound_split hL f p Q hQ (hrest.end_le.trans hcc) hci hi
      hs hs1 (hW 0) (by norm_num : (0:ℝ) ≤ 1) hmid0 hgap hmid
    have he : 1*(F c*((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length))/
        (43264*((4*(N+2)+11:ℕ):ℝ)^4))/(43264*((4*(N+2)+11:ℕ):ℝ)^4) =
        (((c::R).map F).prod)/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*(c::R).length) := by
      rw [List.map_cons,List.prod_cons,List.length_cons,
        show 2*(R.length+1) = 2*R.length+2 by omega,pow_add]
      ring
    simpa only [he] using hh

end Falconer

end OAI
