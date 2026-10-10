import OAI.InformationTheory.BooleanNoise.MonotoneDissipation
import OAI.InformationTheory.SoftChannel.PerspectiveInequality

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar
variable {n : ℕ}

theorem sortCoordinate_property (i : Fin n) (F : Cube n → ℝ)
    (P : ℝ → Prop) (hF : ∀ x, P (F x)) : ∀ x, P (sortCoordinate i F x) := by
  intro x
  unfold sortCoordinate
  split <;> first | exact (max_rec (fun _ => hF _) (fun _ => hF _)) | exact (min_rec (fun _ => hF _) (fun _ => hF _))

theorem sortCoordinate_interior (i : Fin n) {F : Cube n → ℝ} (hF : IsInterior F) :
    IsInterior (sortCoordinate i F) := sortCoordinate_property i F (fun v => v ∈ Ioo (-1 : ℝ) 1) hF

theorem sortCoordinate_closed (i : Fin n) {F : Cube n → ℝ}
    (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) : ∀ x, sortCoordinate i F x ∈ Icc (-1 : ℝ) 1 :=
  sortCoordinate_property i F _ hF

theorem cubeAverage_comp_sortCoordinate (i : Fin n) (F : Cube n → ℝ) (h : ℝ → ℝ) :
    cubeAverage (fun x => h (sortCoordinate i F x)) = cubeAverage (fun x => h (F x)) := by
  have hp (x : Cube n) : h (sortCoordinate i F (setBit i false x)) +
      h (sortCoordinate i F (setBit i true x)) =
      h (F (setBit i false x)) + h (F (setBit i true x)) := by
    simp only [sortCoordinate_false, sortCoordinate_true]
    rcases le_total (F (setBit i false x)) (F (setBit i true x)) with hz | hz
    · rw [min_eq_left hz, max_eq_right hz]
    · rw [min_eq_right hz, max_eq_left hz, add_comm]
  have hh := congrArg (fun f : Cube n → ℝ => ∑ x, f x) (funext hp)
  rw [sum_setBit_pair i (fun x => h (sortCoordinate i F x)),
    sum_setBit_pair i (fun x => h (F x))] at hh
  unfold cubeAverage
  have hs : (∑ x, h (sortCoordinate i F x)) = ∑ x, h (F x) := by linarith
  rw [hs]

theorem psi_noise_sortCoordinate_pair_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) (x : Cube n) :
    psi (noiseOperator u F (setBit i false x)) +
        psi (noiseOperator u F (setBit i true x)) ≤
      psi (noiseOperator u (sortCoordinate i F) (setBit i false x)) +
        psi (noiseOperator u (sortCoordinate i F) (setBit i true x)) := by
  let A := coordinateOffNoise i u (coordinatePairMean i F) x
  let B := u * coordinateOffNoise i u (coordinatePairDifference i F) x
  let C := u * coordinateOffNoise i u (fun y => |coordinatePairDifference i F y|) x
  have hc : 0 ≤ C := mul_nonneg hu.1
    (coordinateOffNoise_nonneg i hu (fun y => abs_nonneg _) x)
  have hbound := coordinateOffNoise_abs_bound i hu (coordinatePairDifference i F) x
  have hb : -C ≤ B ∧ B ≤ C := by
    dsimp only [B, C]
    constructor
    · have h := mul_le_mul_of_nonneg_left hbound.1 hu.1
      nlinarith
    · exact mul_le_mul_of_nonneg_left hbound.2 hu.1
  have hfminus : noiseOperator u F (setBit i false x) = A - B := by
    rw [noiseOperator_setBit]
    dsimp [A, B]
    ring
  have hfplus : noiseOperator u F (setBit i true x) = A + B := by
    rw [noiseOperator_setBit]
    rfl
  have hsminus : noiseOperator u (sortCoordinate i F) (setBit i false x) = A - C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    dsimp [A, C]
    ring
  have hsplus : noiseOperator u (sortCoordinate i F) (setBit i true x) = A + C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    rfl
  have hsort := sortCoordinate_closed i hF
  have hminus : A - C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsminus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  have hplus : A + C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsplus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  rw [hfminus, hfplus, hsminus, hsplus]
  simpa only [add_comm] using psi_symmetric_pair_mono A B C hc hb hminus hplus

theorem cubeAverage_psi_noise_sortCoordinate_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    cubeAverage (fun x => psi (noiseOperator u F x)) ≤
      cubeAverage (fun x => psi (noiseOperator u (sortCoordinate i F) x)) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
    psi_noise_sortCoordinate_pair_closed i hu hF x)
  rw [sum_setBit_pair i (fun x => psi (noiseOperator u F x)),
    sum_setBit_pair i (fun x => psi (noiseOperator u (sortCoordinate i F) x))] at h
  have hs : (∑ x, psi (noiseOperator u F x)) ≤
      ∑ x, psi (noiseOperator u (sortCoordinate i F) x) := by linarith
  exact div_le_div_of_nonneg_right hs (cube_denominator_pos n).le

theorem informationDeficit_noise_sortCoordinate_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinate i F)) := by
  rw [informationDeficit_eq_psi_difference, informationDeficit_eq_psi_difference,
    cubeAverage_noiseOperator, cubeAverage_noiseOperator, cubeAverage_sortCoordinate]
  exact sub_le_sub_right (cubeAverage_psi_noise_sortCoordinate_closed i hu hF) _

theorem sortCoordinates_interior (is : List (Fin n)) {F : Cube n → ℝ}
    (hF : IsInterior F) : IsInterior (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (sortCoordinate_interior i hF)

theorem sortCoordinates_closed (is : List (Fin n)) {F : Cube n → ℝ}
    (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) : ∀ x, sortCoordinates is F x ∈ Icc (-1 : ℝ) 1 := by
  induction is generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (sortCoordinate_closed i hF)

theorem cubeAverage_comp_sortCoordinates (is : List (Fin n)) (F : Cube n → ℝ) (h : ℝ → ℝ) :
    cubeAverage (fun x => h (sortCoordinates is F x)) = cubeAverage (fun x => h (F x)) := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih => rw [sortCoordinates, ih, cubeAverage_comp_sortCoordinate]

theorem informationDeficit_noise_sortCoordinates_closed (is : List (Fin n)) {u : ℝ}
    (hu : u ∈ Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinates is F)) := by
  induction is generalizing F with
  | nil => exact le_rfl
  | cons i is ih =>
      exact (informationDeficit_noise_sortCoordinate_closed i hu hF).trans
        (ih (sortCoordinate_closed i hF))

theorem exists_increasing_dissipation_le (F : Cube n → ℝ) (hF : IsInterior F) :
    ∃ G : Cube n → ℝ, IsInterior G ∧ IsIncreasing G ∧
      (∀ h : ℝ → ℝ, cubeAverage (fun x => h (G x)) = cubeAverage (fun x => h (F x))) ∧
      dissipation G ≤ dissipation F := by
  classical
  let is : List (Fin n) := Finset.univ.toList
  let G := sortCoordinates is F
  have hG : IsInterior G := sortCoordinates_interior is hF
  have hlaw (h : ℝ → ℝ) : cubeAverage (fun x => h (G x)) =
      cubeAverage (fun x => h (F x)) := cubeAverage_comp_sortCoordinates is F h
  have hinc : IsIncreasing G := by
    apply isIncreasing_of_forall_increasingIn
    intro j
    apply sortCoordinates_increasingIn is j
    exact Or.inl (by simp [is])
  have heq : informationDeficit G = informationDeficit F := by
    unfold informationDeficit entropyAverage
    have hm : cubeAverage G = cubeAverage F := hlaw id
    rw [hlaw entropy, hm]
  let f : ℝ → ℝ := fun t =>
    informationDeficit (noiseFlow G t) - informationDeficit (noiseFlow F t)
  have hf0 : f 0 = 0 := by simp [f, noiseFlow_zero, heq]
  have hd : HasDerivAt f (dissipation F - dissipation G) 0 := by
    have h1 := hasDerivAt_informationDeficit_noiseFlow_of_isInterior G 0
      (by simpa only [noiseFlow_zero] using hG)
    have h2 := hasDerivAt_informationDeficit_noiseFlow_of_isInterior F 0
      (by simpa only [noiseFlow_zero] using hF)
    convert! h1.sub h2 using 1; simp [noiseFlow_zero]; ring
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ f t := by
    have hu : Real.exp (-t) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
    exact sub_nonneg.mpr (informationDeficit_noise_sortCoordinates_closed is hu
      (fun x => ⟨(hF x).1.le, (hF x).2.le⟩))
  have hderiv : 0 ≤ dissipation F - dissipation G := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hf0, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg t ht)
  exact ⟨G, hG, hinc, hlaw, by linarith⟩

theorem all_soft_reserve {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
      dissipation g := by
  obtain ⟨G, hG, hinc, hlaw, hD⟩ := exists_increasing_dissipation_le g hg
  have hmean : cubeAverage G = cubeAverage g := hlaw id
  have hent : entropyAverage G = entropyAverage g := hlaw entropy
  have hI : informationDeficit G = informationDeficit g := by
    simp only [informationDeficit, hent, hmean]
  have hv : meanVariance G = meanVariance g := by simp only [meanVariance, hmean]
  have h := monotone_dissipation G hG hinc
  rw [hI, hent, hv] at h
  exact h.trans hD

end LeanBlast.CourtadeKumar
end
end

end OAI
