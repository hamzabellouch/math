import Mathlib
import OAI.Probability.BinarySweep.Trajectories.EndpointEntryBound
import OAI.Probability.BinarySweep.Trajectories.SparseOccupancy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma card_gridOutside_mul (j : Fin b) :
    Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun i : Fin b => Slot (bits i)))
  simpa only [Fintype.card_prod,card_gridSlot,Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.mul_comm] using he.symm

lemma sum_endpointLineCount (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) :
    ∑y, endpointLineCount Finset.univ e j y=k := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun i : ↥(Finset.univ : Finset (Fin k)) => endpointLine (e i) j))
  simpa only [Fintype.card_sigma,Fintype.card_coe,Finset.card_univ,Fintype.card_fin,
    endpointLineCount] using he

lemma heavy_count {L : Type*} [Fintype L] (f : L → ℕ) (τ : ℝ) :
    τ*(Finset.univ.filter (fun l => τ<(f l:ℝ))).card ≤ ∑l, (f l:ℝ) := by
  let S := Finset.univ.filter (fun l => τ<(f l:ℝ))
  calc
    _ = ∑l∈S, τ := by simp [S,mul_comm]
    _ ≤ ∑l∈S, (f l:ℝ) := Finset.sum_le_sum (fun l hl => (Finset.mem_filter.mp hl).2.le)
    _ ≤ ∑l, (f l:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

def holeHeavyLines (j : Fin b) (η : ℝ) : Finset (GridOutside bits j) :=
  Finset.univ.filter (fun l => (2^bits j:ℕ)*η/2<(lineHoles H j l:ℝ))

def particleHeavyLines (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) (η : ℝ) :
    Finset (GridOutside bits j) :=
  Finset.univ.filter (fun l => (2^bits j:ℕ)*η/2<(endpointLineCount Finset.univ e j l:ℝ))

lemma holeHeavy_card (j : Fin b) {η : ℝ} (hη : 0<η) :
    ((holeHeavyLines H j η).card:ℝ) ≤ 2*h/((2^bits j:ℕ)*η) := by
  have hh := heavy_count (lineHoles H j) ((2^bits j:ℕ)*η/2)
  rw [← Nat.cast_sum,sum_lineHoles] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  change (2^bits j:ℕ)*η/2*(holeHeavyLines H j η).card≤(h:ℝ) at hh
  nlinarith

lemma particleHeavy_card (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b)
    {η : ℝ} (hη : 0<η) :
    (particleHeavyLines e j η).card ≤ ⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ := by
  apply Nat.le_floor
  have hh := heavy_count (endpointLineCount Finset.univ e j) ((2^bits j:ℕ)*η/2)
  rw [← Nat.cast_sum,sum_endpointLineCount] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  change (2^bits j:ℕ)*η/2*(particleHeavyLines e j η).card≤(k:ℝ) at hh
  nlinarith

lemma endpoint_not_light (e : Fin k → GridSlot bits × GridSlot bits)
    (j : Fin b) (l : GridOutside bits j) (η : ℝ)
    (hn : ¬endpointLight H η e ⟨j,l⟩) :
    l∈holeHeavyLines H j η ∨ l∈particleHeavyLines e j η := by
  simp only [holeHeavyLines,particleHeavyLines,Finset.mem_filter,Finset.mem_univ,true_and]
  change ¬((lineHoles H j l:ℝ)+endpointLineCount Finset.univ e j l≤(2^bits j:ℕ)*η) at hn
  push Not at hn
  rcases lt_or_ge ((2^bits j:ℕ)*η/2) (lineHoles H j l:ℝ) with hh | hh
  · exact Or.inl hh
  · exact Or.inr (by linarith)

lemma endpoint_line_set_mass (j : Fin b) (S : Finset (GridOutside bits j)) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈S)=
      (S.card:ℝ)*(2^bits j:ℕ)/gridSize bits := by
  change finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
    (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)∈S)=_
  rw [independent_line_set_uniform]
  have he : (Fintype.card (GridOutside bits j):ℝ)*(2^bits j:ℕ)=gridSize bits := by
    exact_mod_cast card_gridOutside_mul j
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have hm : ((2^bits j:ℕ):ℝ)≠0 := by positivity
  rw [← he]
  field_simp

lemma holeHeavy_mass (j : Fin b) {η : ℝ} (hη : 0<η) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      endpointLine z j∈holeHeavyLines H j η) ≤ 2*h/((gridSize bits:ℝ)*η) := by
  rw [endpoint_line_set_mass]
  have hh := holeHeavy_card H j hη
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hm : (0:ℝ)<(2^bits j:ℕ) := by positivity
  calc
    _ ≤ (2*h/((2^bits j:ℕ)*η))*(2^bits j:ℕ)/gridSize bits := by gcongr
    _ = _ := by field_simp

lemma small_lines_mass (j : Fin b) {η : ℝ} (hη : 0<η)
    (S : Finset (GridOutside bits j)) (hS : S.card≤⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈S) ≤
      2*k/((gridSize bits:ℝ)*η) := by
  rw [endpoint_line_set_mass]
  have hnon : 0≤2*(k:ℝ)/((2^bits j:ℕ)*η) := by positivity
  have hh : (S.card:ℝ)≤2*(k:ℝ)/((2^bits j:ℕ)*η) :=
    (Nat.cast_le.mpr hS).trans (Nat.floor_le hnon)
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hm : (0:ℝ)<(2^bits j:ℕ) := by positivity
  calc
    _ ≤ (2*k/((2^bits j:ℕ)*η))*(2^bits j:ℕ)/gridSize bits := by gcongr
    _ = _ := by field_simp

lemma holeHeavy_occupancy_bound (j : Fin b) {η : ℝ} (hη : 0<η)
    (hsmall : 2*h/((gridSize bits:ℝ)*η)≤1) (w : ℕ) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (Finset.univ.filter (fun i => endpointLine (e i) j∈holeHeavyLines H j η)).card) ≤
      (2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^w := by
  have he := occupancy_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈holeHeavyLines H j η) _
    (by positivity) hsmall (holeHeavy_mass H j hη) w
  simp only [Fintype.card_fin] at he
  convert he using 1
  congr 1
  funext e
  congr 1
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

lemma particleHeavy_occupancy_bound (j : Fin b) {η : ℝ} (hη : 0<η)
    (hsmall : 2*k/((gridSize bits:ℝ)*η)≤1) (w : ℕ) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (Finset.univ.filter (fun i => endpointLine (e i) j∈particleHeavyLines e j η)).card) ≤
      (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
        (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^w := by
  have hb := line_sets_occupancy_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    (fun z : GridSlot bits × GridSlot bits => endpointLine z j) _ w _ (by positivity)
    hsmall (small_lines_mass j hη)
  apply le_trans (b:=productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
    ∃S : Finset (GridOutside bits j), S.card≤⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ ∧
      w≤(Finset.univ.filter (fun i => endpointLine (e i) j∈S)).card))
  · exact productProbability_mono uniformWeight_nonneg (fun e he =>
      ⟨particleHeavyLines e j η,particleHeavy_card e j hη,he⟩)
  · simpa only [Fintype.card_fin] using hb

end BinaryCoordinateSweeps

end

end OAI
