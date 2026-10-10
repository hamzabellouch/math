import OAI.Analysis.IrrationalRotation.Model.RationalGraphTrimming
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingLp
import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseTails

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.CircleParameterData

theorem coordinate_mem_Ico (p : CircleParameterData) (i : ℕ) (x : Circle) :
    p.coordinate i x ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [coordinate, rep, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)).property

theorem coordinate_orbit (p : CircleParameterData) (θ : ℝ) (i n : ℕ)
    (x : Circle) :
    p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x + (n : ℝ) * p.alpha θ i) := by
  simpa only [coordinate, rep, alpha, Int.cast_natCast, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul] using
    CircleCharacterDynamics.character_orbit_representative (p.q i : ℤ) (n : ℤ) θ x

theorem kernel_ne_zero_support {m : ℕ} {z v : ℝ} (h : kernel m z v ≠ 0) :
    1 / (m : ℝ)^2 ≤ delta z ∧ 0 < v ∧ v < kernelWidth m * delta z := by
  unfold kernel at h
  split_ifs at h with hs
  · exact hs
  · exact (h rfl).elim

theorem kernel_no_wrap {m : ℕ} (hm : 1 ≤ m) {z v : ℝ}
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hk : kernel m z v ≠ 0) :
    0 < v ∧ z + v < 1 := by
  have hs := kernel_ne_zero_support hk
  have hw : kernelWidth m ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)
  have hd : 0 ≤ delta z := by
    unfold delta
    exact le_min (Int.fract_nonneg z) (by linarith [Int.fract_lt_one z])
  have hd' : delta z ≤ 1 - z := by
    unfold delta
    rw [Int.fract_eq_self.mpr hz]
    exact min_le_right _ _
  have hv : v < delta z := hs.2.2.trans_le (by nlinarith)
  exact ⟨hs.2.1, by linarith⟩

theorem current_block_ordered (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (hm : 1 ≤ p.m j) (x : Circle) (hd : p.orbitGraphDensity θ j n x ≠ 0)
    {i : ℕ} (hi : i ∈ p.block j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  have hk : kernel (p.m j) (p.coordinate i x)
      (Int.fract ((n : ℝ) * p.alpha θ i)) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hd) i hi
  obtain ⟨hv, hsum⟩ := kernel_no_wrap hm (p.coordinate_mem_Ico i x) hk
  rw [p.coordinate_orbit]
  have he : Int.fract (p.coordinate i x + (n : ℝ) * p.alpha θ i) =
      Int.fract (p.coordinate i x + Int.fract ((n : ℝ) * p.alpha θ i)) := by
    conv_lhs => rw [← Int.fract_add_floor ((n : ℝ) * p.alpha θ i)]
    rw [← add_assoc, Int.fract_add_intCast]
  rw [he, Int.fract_eq_self.mpr
    ⟨by linarith [(p.coordinate_mem_Ico i x).1], hsum⟩]
  linarith

theorem measurableSet_rationalGraphGood (p : CircleParameterData) (A j : ℕ) :
    MeasurableSet (p.rationalGraphGood A j) := by
  unfold rationalGraphGood
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (p.measurable_coordinate i) measurable_const
  · exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_lt (p.measurable_coordinate i) measurable_const

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimming_frequency_dvd_of_le {a b : ℕ} (hab : a ≤ b) : p.q a ∣ p.q b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b _ ih => exact ih.trans (hp.frequency_divisible b)

theorem trimming_coordinate_rational_translation {A i : ℕ} (hAi : A ≤ i)
    (r : ℤ) (x : Circle) :
    p.coordinate i (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) =
      p.coordinate i x := by
  simpa only [coordinate, rep, Int.cast_natCast, natCast_zsmul] using
    CircleCharacterDynamics.character_rational_translation
      (q := (p.q i : ℤ)) (d := (p.q A : ℤ))
      (by exact_mod_cast (hp.q_pos A).ne')
      (by exact_mod_cast hp.trimming_frequency_dvd_of_le hAi) r x

alias frequency_dvd_of_le := trimming_frequency_dvd_of_le

alias coordinate_rational_translation := trimming_coordinate_rational_translation

theorem early_coordinate_ordered {A j i n : ℕ} (hAi : A ≤ i)
    (hia : i ≤ p.blockEnd (j - 1)) (x : Circle)
    (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hn : Int.fract ((n : ℝ) * θ - t) < p.ell j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  let δ : ℝ := Int.fract ((n : ℝ) * θ - t)
  have hδ : 0 ≤ δ := Int.fract_nonneg _
  have hqi : 0 ≤ (p.q i : ℝ) := Nat.cast_nonneg _
  have hqa : (p.q i : ℝ) ≤ p.q (p.blockEnd (j - 1)) := by
    exact_mod_cast hp.frequency_increasing.monotone hia
  have hell : 0 < p.ell j := by
    unfold ell
    have hq : (0 : ℝ) < p.q (p.blockEnd (j - 1)) := by
      exact_mod_cast hp.q_pos _
    positivity
  have hmove : (p.q i : ℝ) * δ ≤ (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j := by
    exact mul_le_mul hqa hn.le hδ (Nat.cast_nonneg _)
  have hnowrap : p.coordinate i x + (p.q i : ℝ) * δ < 1 := by
    have htrim := hx.1 i hAi hia
    linarith
  have hti : p.q i • (t : Circle) = 0 := by
    obtain ⟨k, hk⟩ := hp.trimming_frequency_dvd_of_le hAi
    rw [hk, mul_nsmul, ht, nsmul_zero]
  have he : (((n : ℝ) * θ : ℝ) : Circle) = (t : Circle) + (δ : Circle) := by
    dsimp [δ]
    rw [AddCircle.coe_fract, AddCircle.coe_sub]
    abel
  have hecoord : p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x + (p.q i : ℝ) * δ) := by
    change rep (p.q i • (x + (((n : ℝ) * θ : ℝ) : Circle))) = _
    rw [he, nsmul_add, nsmul_add, hti, zero_add,
      ← AddCircle.coe_nsmul, nsmul_eq_mul]
    exact CircleCharacterDynamics.representative_add_real _ _
  rw [hecoord, Int.fract_eq_self.mpr ⟨add_nonneg (p.coordinate_mem_Ico i x).1
    (mul_nonneg hqi hδ), hnowrap⟩]
  exact le_add_of_nonneg_right (mul_nonneg hqi hδ)

theorem future_coordinate_ordered {A j s i n : ℕ} (hjs : j < s)
    (hi : i ∈ p.block s) (x : Circle) (hx : x ∈ p.rationalGraphGood A j)
    (hn : (n : ℝ) ≤ p.Q j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  have hs : 1 ≤ s := by omega
  have hN : 0 < p.N s := mul_pos (by exact_mod_cast hp.m_pos s hs)
    (by exact_mod_cast hp.K_pos s hs)
  have hα := hp.phase_bounds s hs i hi
  have hmove : (n : ℝ) * p.alpha θ i ≤ 2 * p.Q j / p.N s := by
    calc
      _ ≤ p.Q j * (2 / p.N s) := mul_le_mul hn hα.2.le
        (one_div_pos.mpr hN |>.le.trans hα.1.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by ring
  have hnowrap : p.coordinate i x + (n : ℝ) * p.alpha θ i < 1 := by
    have htrim := hx.2 s hjs i hi
    linarith
  have hmove0 : 0 ≤ (n : ℝ) * p.alpha θ i :=
    mul_nonneg (Nat.cast_nonneg _) ((one_div_pos.mpr hN).le.trans hα.1.le)
  rw [p.coordinate_orbit, Int.fract_eq_self.mpr
    ⟨add_nonneg (p.coordinate_mem_Ico i x).1 hmove0, hnowrap⟩]
  exact le_add_of_nonneg_right hmove0

theorem ordered_of_rationalGraphGood {A j n : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j)
    (x : Circle) (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hphase : Int.fract ((n : ℝ) * θ - t) < p.ell j)
    (hn : (n : ℝ) ≤ p.Q j)
    (hd : p.orbitGraphDensity θ j n x ≠ 0) :
    ∀ i, A ≤ i → p.coordinate i x ≤
      p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  intro i hAi
  by_cases hia : i ≤ p.blockEnd (j - 1)
  · exact hp.early_coordinate_ordered hAi hia x hx t ht hphase
  · by_cases hij : i ≤ p.blockEnd j
    · exact p.current_block_ordered θ j n (hp.m_pos j hj) x hd
        ((p.mem_block_iff j i).mpr ⟨by omega, hij⟩)
    · obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (hA.trans hAi)
      have hjs : j < s := by
        by_contra h
        have hsj : s ≤ j := by omega
        have hb := (p.blockEnd_strictMono hp.m_pos).monotone hsj
        have hi := (p.mem_block_iff s i).mp his
        omega
      exact hp.future_coordinate_ordered hjs his x hx hn

theorem ordered_of_rationalGraphGood_rational {A j n : ℕ}
    (hA : 1 ≤ A) (hj : 1 ≤ j) (r : ℤ) (x : Circle)
    (hx : x ∈ p.rationalGraphGood A j)
    (hphase : Int.fract ((n : ℝ) * θ - (r : ℝ) / p.q A) < p.ell j)
    (hn : (n : ℝ) ≤ p.Q j) (hd : p.orbitGraphDensity θ j n x ≠ 0) :
    ∀ i, A ≤ i → p.coordinate i x ≤
      p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  apply hp.ordered_of_rationalGraphGood hA hj x hx ((r : ℝ) / p.q A) _ hphase hn hd
  simpa only [Int.cast_natCast, natCast_zsmul] using
    CircleCharacterDynamics.zsmul_rational_eq_zero
      (q := (p.q A : ℤ)) (d := (p.q A : ℤ))
      (by exact_mod_cast (hp.q_pos A).ne') dvd_rfl r

end Invariant233.CircleParameterLaws

end

end OAI
