import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Sampling.PhaseRanges
import OAI.Analysis.IrrationalRotation.Rotation.FiniteSupportCocycle

namespace OAI

noncomputable section

namespace Invariant233.TaggedNearWindow

theorem rounded_tag_endpoints {m K X Y u v : ℝ}
    (hm : 0 < m) (hK : 2 ≤ K)
    (hX : X < 1 / (2 * m)) (hY : 1 - 1 / (2 * m) ≤ Y)
    (hu : |u - X| ≤ 1 / (m * K)) (hv : |v - Y| ≤ 1 / (m * K)) :
    u < 1 / m ∧ 1 - 1 / m ≤ v := by
  have herror : 1 / (m * K) ≤ 1 / (2 * m) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hhalves : 1 / (2 * m) + 1 / (2 * m) = 1 / m := by ring
  have hu' := (abs_le.mp hu).2
  have hv' := (abs_le.mp hv).1
  constructor <;> linarith

theorem rounded_tag_crossing {m K α k X Y u v : ℝ}
    (hm : 0 < m) (hK : 2 ≤ K)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : K ≤ |k|) (hkhi : |k| ≤ m * K / 4)
    (hX : X < 1 / (2 * m)) (hY : 1 - 1 / (2 * m) ≤ Y)
    (hu : |u - X| ≤ 1 / (m * K)) (hv : |v - Y| ≤ 1 / (m * K)) :
    u < 1 - Int.fract (k * α) ∧ 1 - Int.fract (k * α) ≤ v := by
  have he := rounded_tag_endpoints hm hK hX hY hu hv
  have ht := phase_small_window (m := m) (K := K) (G := 1) (α := α) (k := k)
    hm (by linarith) (by norm_num) hαlo hαhi (by simpa using hklo) hkhi
  exact ⟨he.1.trans_le ht.1, ht.2.trans he.2⟩

theorem coordinate_circleValue_eq (p : CircleParameterData)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (i : ℕ) :
    p.coordinate i (MixedRadix.circleValue d) =
      Int.fract ((p.q i : ℝ) * MixedRadix.ofDigits d) := by
  unfold CircleParameterData.coordinate CircleParameterData.rep MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul]
  simpa only [nsmul_eq_mul, Nat.cast_commute] using
    CircleCharacterDynamics.representative_coe ((p.q i : ℝ) * MixedRadix.ofDigits d)

end TaggedNearWindow

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem tagged_K_ge_initial (j : ℕ) (hj : 1 ≤ j) : 100 ≤ p.K j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => simpa using hp.initial_K.ge
  | succ n ih =>
      have hd := hp.K_double (1 + n) (by omega)
      have he : 1 + (n + 1) = 1 + n + 1 := by omega
      rw [he]
      omega

theorem tagged_radix_eq_ratio (i : ℕ) :
    (MixedRadix.radices p.q i : ℝ) = (p.q (i + 1) : ℝ) / p.q i := by
  have hq : (p.q i : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos i).ne'
  apply (eq_div_iff hq).mpr
  have h := Nat.mul_div_cancel' (hp.frequency_divisible i)
  have hr : p.q i * MixedRadix.radices p.q i = p.q (i + 1) := h
  exact_mod_cast (show MixedRadix.radices p.q i * p.q i = p.q (i + 1) by simpa only [mul_comm] using hr)

theorem tagged_coordinate_error {j i : ℕ} (hj : 1 ≤ j) (hi : i ∈ p.block j)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (hd : MixedRadix.Nonterminal d)
    {X : ℝ} (hX : 0 ≤ X)
    (hfloor : ⌊(MixedRadix.radices p.q i : ℝ) * X⌋₊ = (d i : ℕ)) :
    |p.coordinate i (MixedRadix.circleValue d) - X| ≤ 1 / p.N j := by
  rw [TaggedNearWindow.coordinate_circleValue_eq]
  refine (MixedRadix.abs_coordinate_sub_raw_le hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible d hd i hX hfloor).trans ?_
  apply one_div_le_one_div_of_le
  · exact mul_pos (Nat.cast_pos.mpr (hp.m_pos j hj)) (Nat.cast_pos.mpr (hp.K_pos j hj))
  · rw [hp.tagged_radix_eq_ratio]
    exact hp.frequency_ratios j hj i hi

theorem tagged_near_window_crossing {j i : ℕ} (hj : 1 ≤ j) (hi : i ∈ p.block j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (k : ℤ) (hklo : (p.K j : ℝ) < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ p.N j / 4)
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hX : X < 1 / (2 * (p.m j : ℝ))) (hY : 1 - 1 / (2 * (p.m j : ℝ)) ≤ Y)
    (hfloorX : ⌊(MixedRadix.radices p.q i : ℝ) * X⌋₊ = (d i : ℕ))
    (hfloorY : ⌊(MixedRadix.radices p.q i : ℝ) * Y⌋₊ = (e i : ℕ)) :
    p.coordinate i (MixedRadix.circleValue d) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) ∧
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤
        p.coordinate i (MixedRadix.circleValue e) := by
  apply TaggedNearWindow.rounded_tag_crossing
    (Nat.cast_pos.mpr (hp.m_pos j hj))
    (show (2 : ℝ) ≤ p.K j by exact_mod_cast (show 2 ≤ p.K j by have := hp.tagged_K_ge_initial j hj; omega))
    (hp.phase_bounds j hj i hi).1.le (hp.phase_bounds j hj i hi).2.le
    hklo.le hkhi hX hY
  · exact hp.tagged_coordinate_error hj hi d hd hX0 hfloorX
  · exact hp.tagged_coordinate_error hj hi e he hY0 hfloorY

theorem tagged_near_window_attenuation {j i : ℕ} (hj : 1 ≤ j) (hi : i ∈ p.block j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (hde : ∀ n, d n ≤ e n)
    (k : ℤ) (hklo : (p.K j : ℝ) < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ p.N j / 4)
    {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hX : X < 1 / (2 * (p.m j : ℝ))) (hY : 1 - 1 / (2 * (p.m j : ℝ)) ≤ Y)
    (hfloorX : ⌊(MixedRadix.radices p.q i : ℝ) * X⌋₊ = (d i : ℕ))
    (hfloorY : ⌊(MixedRadix.radices p.q i : ℝ) * Y⌋₊ = (e i : ℕ))
    (hsd : Function.HasFiniteSupport (fun n : ℕ =>
      ⌊p.coordinate (n + 1) (MixedRadix.circleValue d) + (k : ℝ) * p.alpha θ (n + 1)⌋))
    (hse : Function.HasFiniteSupport (fun n : ℕ =>
      ⌊p.coordinate (n + 1) (MixedRadix.circleValue e) + (k : ℝ) * p.alpha θ (n + 1)⌋)) :
    Real.exp (-(∑' n : ℕ, p.flattenedCost n *
      (⌊p.coordinate (n + 1) (MixedRadix.circleValue e) + (k : ℝ) * p.alpha θ (n + 1)⌋ : ℝ))) /
    Real.exp (-(∑' n : ℕ, p.flattenedCost n *
      (⌊p.coordinate (n + 1) (MixedRadix.circleValue d) + (k : ℝ) * p.alpha θ (n + 1)⌋ : ℝ)))
      ≤ Real.exp (-p.L j) := by
  have hip : 1 ≤ i := by
    have h := (p.mem_block_iff j i).mp hi
    omega
  have hin : i - 1 + 1 = i := Nat.sub_add_cancel hip
  have hcoord (a : MixedRadix.Digits (MixedRadix.radices p.q)) (n : ℕ) :
      p.coordinate (n + 1) (MixedRadix.circleValue a) ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [CircleParameterData.coordinate, CircleParameterData.rep, zero_add] using
      (AddCircle.equivIco (1 : ℝ) 0 (p.q (n + 1) • MixedRadix.circleValue a)).property
  have hcost (n : ℕ) : 0 ≤ p.flattenedCost n :=
    (hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))).le
  have horder (n : ℕ) :
      p.coordinate (n + 1) (MixedRadix.circleValue d) ≤
        p.coordinate (n + 1) (MixedRadix.circleValue e) := by
    simp only [TaggedNearWindow.coordinate_circleValue_eq]
    exact MixedRadix.coordinates_ordered hp.frequency_zero hp.q_pos
      hp.frequency_increasing hp.frequency_divisible hd he hde (n + 1)
  have hcross := hp.tagged_near_window_crossing hj hi d e hd he k hklo hkhi
    hX0 hY0 hX hY hfloorX hfloorY
  have hbound := FiniteSupportCocycle.exp_tsum_floor_ratio_le_finite_crossings
    (fun n => p.coordinate (n + 1) (MixedRadix.circleValue d))
    (fun n => p.coordinate (n + 1) (MixedRadix.circleValue e))
    (fun n => (k : ℝ) * p.alpha θ (n + 1)) p.flattenedCost {i - 1}
    (hcoord d) (hcoord e) hcost horder hsd hse (by
      intro n hn
      have hn' : n = i - 1 := Finset.mem_singleton.mp hn
      subst n
      simpa only [hin] using hcross)
  simp only [Finset.sum_singleton] at hbound
  have hc : p.flattenedCost (i - 1) = p.C j :=
    p.flattenedCost_eq_of_mem hp.m_pos (by simpa only [hin] using hi)
  rw [hc] at hbound
  exact hbound.trans (Real.exp_le_exp.mpr (neg_le_neg (by
    rw [hp.C_eq j hj]
    exact le_max_left _ _)))

end CircleParameterLaws
end Invariant233

end

end OAI
