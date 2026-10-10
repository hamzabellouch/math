import OAI.Probability.ContinuumTransition.OccupationEnergy

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def cellPairEnvelope {κ : Type} [Fintype κ] (F : ConfigFamily)
    (e : κ → Lattice) (J : κ → κ → ℝ) : ConfigFamily :=
  fun ι _ x => ∑ k, ∑ l, (J k l/2)*occupationPairFamily F (latticeCell (e k)) (latticeCell (e l)) ι x

theorem GrandFinite.cellPairEnvelope {κ : Type} [Fintype κ] {F : ConfigFamily}
    {D : Set Space} (e : κ → Lattice) (J : κ → κ → ℝ)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D) :
    GrandFinite (cellPairEnvelope F e J) D :=
  GrandFinite.sum _ (fun k => GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2)))

theorem grandIntegral_cellPairEnvelope {κ : Type} [Fintype κ] {F : ConfigFamily}
    {D : Set Space} (e : κ → Lattice) (J : κ → κ → ℝ)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D) :
    grandIntegral (cellPairEnvelope F e J) D =
      ∑ k, ∑ l, (J k l/2)*grandIntegral (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D := by
  unfold cellPairEnvelope
  rw [grandIntegral_sum _ D
    (fun k n => (GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2))).integrable (Fin n))
    (fun k => (GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2))).summable)]
  apply Finset.sum_congr rfl
  intro k _
  rw [grandIntegral_sum _ D (fun l n => ((hp k l).const_mul (J k l/2)).integrable (Fin n))
    (fun l => ((hp k l).const_mul (J k l/2)).summable)]
  simp_rw [grandIntegral_const_mul]

theorem interactionFamily_le_cellPairEnvelope {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : ConfigFamily) (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    {D : Set Space} (e : κ → Lattice) (he : Function.Injective e)
    (hcover : ∀ x ∈ D, ∃ k, cellIndex x = e k)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (W : Space → Space → ℝ) (hWs : ∀ x y, W x y = W y x)
    (hW : ∀ k l x y, x ∈ D → y ∈ D → cellIndex x = e k → cellIndex y = e l → W x y ≤ J k l)
    (ι : Type) [Fintype ι] (x : ι → Space) (hx : ∀ i, x i ∈ D) :
    interactionFamily F W ι x ≤ cellPairEnvelope F e J ι x := by
  let c (i : ι) : κ := Classical.choose (hcover (x i) (hx i))
  have hc (i : ι) : cellIndex (x i) = e (c i) := Classical.choose_spec (hcover (x i) (hx i))
  have hh := mul_le_mul_of_nonneg_left
    (gibbsEnergy_le_cell_pairs W hWs J hJ x c e he hc
      (fun i j => hW (c i) (c j) (x i) (x j) (hx i) (hx j) (hc i) (hc j))) (hF ι x)
  apply hh.trans_eq
  unfold cellPairEnvelope occupationPairFamily
  simp only [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem grand_interaction_bound {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : ConfigFamily) {D : Set Space} (hD : MeasurableSet D)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (e : κ → Lattice) (he : Function.Injective e) (hcover : ∀ x ∈ D, ∃ k, cellIndex x = e k)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (W : Space → Space → ℝ) (hWs : ∀ x y, W x y = W y x)
    (hWm : Measurable (Function.uncurry W)) (hW0 : ∀ x y, 0 ≤ W x y)
    (hW : ∀ k l x y, x ∈ D → y ∈ D → cellIndex x = e k → cellIndex y = e l → W x y ≤ J k l)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D)
    {M : ℝ} (hZ : 0 < grandIntegral F D)
    (hmom : ∀ k l, grandIntegral (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D/
      grandIntegral F D ≤ M) :
    GrandFinite (interactionFamily F W) D ∧
      grandIntegral (interactionFamily F W) D/grandIntegral F D ≤ (M/2)*∑ k, ∑ l, J k l := by
  have hG := GrandFinite.cellPairEnvelope e J hp
  have hb := interactionFamily_le_cellPairEnvelope F hF e he hcover J hJ W hWs hW
  have hH := GrandFinite.of_le_on hD hG (fun ι _ => (hFm ι).mul (measurable_gibbsEnergy hWm))
    (interactionFamily_nonneg F hF W hW0) hb
  refine ⟨hH, ?_⟩
  have hi := grandIntegral_mono (interactionFamily F W) (cellPairEnvelope F e J) hD
    (fun n => hH.integrable (Fin n)) (fun n => hG.integrable (Fin n)) hH.summable hG.summable
    (fun n => hb (Fin n))
  rw [grandIntegral_cellPairEnvelope e J hp] at hi
  apply (div_le_div_of_nonneg_right hi hZ.le).trans
  simp only [Finset.sum_div, mul_div_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  have hh := mul_le_mul_of_nonneg_left (hmom k l) (div_nonneg (hJ k l) (by norm_num : (0:ℝ) ≤ 2))
  convert hh using 1
  ring

end ContinuumTemperature
end

end OAI
