import OAI.Probability.GammaPassage.CharacteristicLengths

namespace OAI

/-! Integer meshes with a final unit interval, and their comparison with
characteristic lengths at record indices. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Filter Set MeasureTheory
open scoped Topology

def gridMeshExponent (m j : ℕ) : ℕ := m-(4*j+1)
def gridLastLevel (m : ℕ) : ℕ := (m+2)/4
noncomputable def gridMesh (m j : ℕ) : ℤ := (2 : ℤ)^gridMeshExponent m j
noncomputable def gridWidth (k j : ℕ) : ℤ := (2 : ℤ)^(k-j)

lemma gridMesh_pos (m j : ℕ) : 0 < gridMesh m j := by unfold gridMesh; positivity
lemma gridWidth_pos (k j : ℕ) : 0 < gridWidth k j := by unfold gridWidth; positivity
lemma gridLastLevel_unit (m : ℕ) : gridMesh m (gridLastLevel m)=1 := by
  have he : gridMeshExponent m (gridLastLevel m)=0 := by
    unfold gridMeshExponent gridLastLevel
    omega
  simp [gridMesh,he]

lemma gridMesh_antitone (m : ℕ) : Antitone (gridMesh m) := by
  intro i j hij
  apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
  unfold gridMeshExponent
  omega

lemma gridMesh_ratio_le (m j : ℕ) : gridMesh m j ≤ 16*gridMesh m (j+1) := by
  have he : gridMeshExponent m j ≤ 4+gridMeshExponent m (j+1) := by unfold gridMeshExponent; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he
  simpa [gridMesh,pow_add] using hh

lemma gridMesh_divides (m j : ℕ) : gridMesh m (j+1) ∣ gridMesh m j := by
  apply pow_dvd_pow
  unfold gridMeshExponent
  omega

lemma gridMesh_level_bound (m k j : ℕ) (hm : m ≤ 3*k) (hj : j ≤ gridLastLevel m) :
    4*(k-j)+3 ≥ k := by
  unfold gridLastLevel at hj
  omega

lemma gridMesh_count_ratio (m j : ℕ) :
    (2 : ℝ)^m / (gridMesh m j : ℝ) ≤ (2 : ℝ)^(4*j+1) := by
  have hg : (0 : ℝ) < (gridMesh m j : ℝ) := by exact_mod_cast gridMesh_pos m j
  rw [div_le_iff₀ hg]
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

lemma gridWidth_ratio (k j : ℕ) (hj : j ≤ k) :
    (2 : ℝ)^k / (gridWidth k j : ℝ) = (2 : ℝ)^j := by
  have he : k=j+(k-j) := by omega
  simp only [gridWidth,Int.cast_pow,Int.cast_ofNat]
  rw [show (2 : ℝ)^k=(2 : ℝ)^j*(2 : ℝ)^(k-j) by rw [← pow_add,← he]]
  rw [mul_div_cancel_right₀ _ (by positivity)]

lemma gridMesh_below_record_length (L : ℕ → ℤ) (k m j : ℕ)
    (hL : L k=(2 : ℤ)^m)
    (hrec : (1/16 : ℝ)^j*(L k : ℝ) ≤ (L (k-j) : ℝ))
    (hunit : 1 < L (k-j)) : gridMesh m j < L (k-j) := by
  by_cases hsmall : m ≤ 4*j+1
  · simpa [gridMesh,gridMeshExponent,Nat.sub_eq_zero_of_le hsmall] using hunit
  · have he : m=gridMeshExponent m j+(4*j+1) := by unfold gridMeshExponent; omega
    have hr : (1/16 : ℝ)^j*((2 : ℤ)^m : ℝ) = 2*(gridMesh m j : ℝ) := by
      simp only [Int.cast_pow,Int.cast_ofNat,gridMesh]
      conv_lhs => rw [he,pow_add]
      rw [pow_add,pow_one,show (2 : ℝ)^(4*j)=(16 : ℝ)^j by rw [pow_mul]; norm_num]
      have hh : (1/16 : ℝ)^j*16^j=1 := by rw [← mul_pow]; norm_num
      calc
        _ = (2 : ℝ)^gridMeshExponent m j*((1/16 : ℝ)^j*16^j)*2 := by ring
        _ = _ := by rw [hh]; ring
    rw [hL] at hrec
    simp only [Int.cast_pow,Int.cast_ofNat] at hrec hr
    rw [hr] at hrec
    have hp : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
    exact_mod_cast (show (gridMesh m j : ℝ) < L (k-j) by linarith)

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Crossing trial probabilities at every allowed level of each sufficiently
large characteristic record index. -/
theorem gamma_grid_trial_probabilities (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
      j ≤ gridLastLevel (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) →
      ((1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k : ℝ) ≤
        (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) : ℝ)) →
      q₀ < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm henv hs hr) (direction b))
        (sourceCrossingK shape rate (gammaMeanNorm henv hs hr) b) (gridWidth k j) (gridMesh (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j) 0} := by
  have hlarge := (gamma_characteristic_lengths_ratio henv hs hr b q₀ hb hq hq1).eventually
    (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlarge
  filter_upwards [eventually_ge_atTop (4*N+4),
    gamma_characteristic_lengths_exist henv hs hr b q₀ hb hq] with k hk hex
  intro j hj hrec
  have hlev := gridMesh_level_bound (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) k j hex.1 hj
  have hjk : j ≤ k := by unfold gridLastLevel at hj; omega
  have hNk : N ≤ k-j := by omega
  have hunit : 1 < characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^(k-j))).mp (hN (k-j) hNk)
    have hp : (1 : ℝ) ≤ 2^(k-j) := one_le_pow₀ (by norm_num)
    exact_mod_cast (show (1 : ℝ) < characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j) by linarith)
  have hmesh := gridMesh_below_record_length (characteristicLength P τ shape rate (gammaMeanNorm henv hs hr) b q₀) k
    (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j rfl hrec hunit
  have hp := characteristicLength_minimal shape rate (gammaMeanNorm henv hs hr) b q₀ (k-j)
    (gridMeshExponent (characteristicExponent P τ shape rate (gammaMeanNorm henv hs hr) b q₀ k) j) hmesh
  simpa only [sourceDyadicCrossingProbability,gridWidth,gridMesh,Int.cast_pow,Int.cast_ofNat] using hp

end GammaFPP.CrossingBridge

end OAI
