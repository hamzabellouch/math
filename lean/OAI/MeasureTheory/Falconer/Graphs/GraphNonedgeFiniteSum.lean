import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeIndexCount

namespace OAI

namespace PlanarFalconer

theorem graph_nonedge_sum_power (N p n : ℕ) (hp : p ≤ N) {C T outer : ℝ}
    (hC : 0 ≤ C) (hn : (n:ℝ) ≤ C*(2:ℝ)^N) (hconst : 2*C^2 ≤ (2:ℝ)^N)
    (I : Finset GraphNonedgeIndex) (hI : I ⊆ graphNonedgeIndices p n)
    (F : GraphNonedgeIndex → ℂ) (c : GraphNonedgeIndex → ℝ)
    (hc : ∀ i ∈ I, |c i| ≤ 1) (houter : |outer| ≤ ((2:ℝ)^N)^2)
    (hb : ∀ i ∈ I, ‖F i‖ ≤ ((2:ℝ)^N)^(-(T+13))) :
    ‖outer • (∑ i ∈ I, c i • F i)‖ ≤ ((2:ℝ)^N)^(-T) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : (I.card : ℝ) ≤ ((graphNonedgeIndices p n).card : ℝ) := by exact_mod_cast Finset.card_le_card hI
  have hcard : (I.card : ℝ) ≤ 2*C^2*R^10 :=
    hsub.trans (graph_nonedge_index_count_le N p n hp hC hn)
  have hsum : ‖∑ i ∈ I, c i • F i‖ ≤ (I.card:ℝ)*R^(-(T+13)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ I, R^(-(T+13)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul (hc i hi) (hb i hi) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ R^2*((2*C^2*R^10)*R^(-(T+13))) :=
      mul_le_mul houter (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity)))
        (norm_nonneg _) (by positivity)
    _ = (2*C^2)*R^(-T-1) := by
      have he : R^12*R^(-(T+13)) = R^(-T-1) := by
        rw [← Real.rpow_natCast R 12,← Real.rpow_add hR]
        congr 1
        norm_num
        ring
      calc
        _ = (2*C^2)*(R^12*R^(-(T+13))) := by ring
        _ = _ := by rw [he]
    _ ≤ R*R^(-T-1) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = R^(-T) := by
      nth_rw 1 [← Real.rpow_one R]
      rw [← Real.rpow_add hR]
      congr 1
      ring

theorem uniform_graph_nonedge_sum_power {sig c₀ : ℝ} (hsig : 0 ≤ sig)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : ℕ), p ≤ N → ∀ t : ℝ, t ≤ (N:ℝ) →
    ∀ (T outer : ℝ) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig t c₀)) →
    ∀ (F : GraphNonedgeIndex → ℂ) (c : GraphNonedgeIndex → ℝ),
    (∀ i ∈ I, |c i| ≤ 1) → |outer| ≤ ((2:ℝ)^N)^2 →
    (∀ i ∈ I, ‖F i‖ ≤ ((2:ℝ)^N)^(-(T+13))) →
    ‖outer • (∑ i ∈ I, c i • F i)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (2*(graphBinCountConstant c₀)^2)
  refine ⟨N₀,?_⟩
  intro N hN p hp t ht T outer I hI F c hcoeff houter hb
  exact graph_nonedge_sum_power N p _ hp (graphBinCountConstant_nonneg c₀)
    (graph_source_bin_count_le N hsig hc hcap ht) (by simpa using hN₀ N hN) I hI F c hcoeff houter hb

end PlanarFalconer

end OAI
