import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketSelection

namespace OAI

/-! All geometric properties retained by the packet-size freezing step. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem freeze_regular_packets {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s K (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l)
    (b : Space 2 → ℕ) (D : ℕ) (hb : ∀ l ∈ P.biUnion T, 0 < b l ∧ b l ≤ D) :
    let J := Nat.log 2 D+1
    let F := 2*(J:ℝ)*M/m
    ∃ k : ℕ, ∃ B ⊆ P.biUnion T, B.Nonempty ∧
      (∀ l ∈ B, 2^k ≤ b l ∧ b l < 2^(k+1)) ∧
      ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
        NormalizedFiniteBallBound δ t (K*F) R ∧
        ∀ x ∈ R, (T x ∩ B).Nonempty ∧ m/(2*(J:ℝ)) ≤ ((T x ∩ B).card:ℝ) ∧
          InBoundedLineChart (T x ∩ B) ∧ FiniteSeparatedAt δ (T x ∩ B) ∧
          NormalizedFiniteBallBound δ s (K*F) (T x ∩ B) ∧
          ∀ l ∈ T x ∩ B, TubeIncident δ x l := by
  let J := Nat.log 2 D+1
  let F := 2*(J:ℝ)*M/m
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨k,B,hBU,hB,hband,R,hRP,hR,hsize,hlarge⟩ := freeze_coarse_packet_sizes
    P T b D hP hm hM (fun x hx => ⟨(hT x hx).1,(hT x hx).2.1⟩) hb
  have hPsize : (P.card:ℝ) ≤ F*(R.card:ℝ) := by
    have hh := (div_le_iff₀ (show 0 < 2*(J:ℝ)*M by positivity)).1 hsize
    calc
      _ ≤ (2*(J:ℝ)*M)*(R.card:ℝ)/m := (le_div_iff₀ hm).2 (by nlinarith only [hh])
      _ = _ := by dsimp [F]; ring
  refine ⟨k,B,hBU,hB,hband,R,hRP,hR,hPsize,
    normalized_finite_ball_bound_subset hδ.le hK hRP hPsize hPball,?_⟩
  intro x hx
  have hxP := hRP hx
  have ht := hT x hxP
  have hcard : 0 < ((T x ∩ B).card:ℝ) := (div_pos hm (by positivity)).trans_le (hlarge x hx)
  have hTsize : ((T x).card:ℝ) ≤ F*((T x ∩ B).card:ℝ) := by
    calc
      _ ≤ M := ht.2.1
      _ = F*(m/(2*(J:ℝ))) := by dsimp [F]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlarge x hx) hF.le
  refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp hcard),hlarge x hx,
    (fun l hl => ht.2.2.1 l (Finset.mem_inter.mp hl).1),
    finiteSeparatedAt_subset Finset.inter_subset_left ht.2.2.2.1,
    normalized_finite_ball_bound_subset hδ.le hK Finset.inter_subset_left hTsize ht.2.2.2.2.1,
    fun l hl => ht.2.2.2.2.2 l (Finset.mem_inter.mp hl).1⟩

end Falconer

end OAI
