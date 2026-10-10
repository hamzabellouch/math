import OAI.NumberTheory.DukePrimeDegree.Geometry.QuantitativeDistanceNet
import OAI.NumberTheory.DukePrimeDegree.Geometry.SmallMatrixLength

namespace OAI

/-! # Uniform local packing after rescaling a quotient chart

The number of separated points in a fixed multiple of a sufficiently
small chart is bounded independently of the chart radius and base point.
The proof uses the existing finite matrix grid and actual right lifts.
-/

noncomputable section
open Matrix Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

def localQuotientPackingBound (n : ℕ) (C : ℝ) : ℝ :=
  (2*C+2)^(n*n)/(1/(96*(n:ℝ)^2))^(n*n)

theorem local_quotient_packing_bound {n N : ℕ} (hn : 0 < n)
    (x : X n) (g : Fin N → G n) {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hg : ∀ i, g i ∈ matrixBall n (C*δ))
    (hsep : ∀ i j, i ≠ j → δ ≤
      quotientLogDistance (rightAction x (g i)) (rightAction x (g j))) :
    (N:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let η : ℝ := 1/(96*(n:ℝ)^2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < 96*(n:ℝ)^2)).mpr
    nlinarith
  have hscale : 8*(n:ℝ)^2*η=1/12 := by
    dsimp [η]
    field_simp [hnp.ne']
    ring
  let q (i : Fin N) (t : Fin (n*n)) : ℝ :=
    ((g i).val (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 -
      (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)/δ
  have hq (i : Fin N) (t : Fin (n*n)) : |q i t| ≤ C := by
    dsimp [q]
    rw [abs_div,abs_of_pos hδ]
    apply (div_le_iff₀ hδ).mpr
    exact (hg i _ _).le
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover (n*n) hC hη hη1
  choose c hc hclose using (fun i => hcover (q i) (hq i))
  let f : Fin N → s := fun i => ⟨c i,hc i⟩
  have hinv (i : Fin N) : ∀ a b, |(g i)⁻¹.val a b| ≤ 2 := by
    have hnorm : ‖(g i).val-1‖ ≤ 1/2 :=
      (matrix_operator_norm_le_card_mul _ (mul_nonneg hC hδ.le)
        (fun a b => (hg i a b).le)).trans (by simpa only [mul_assoc] using hsmall)
    exact fun a b => (matrix_entry_abs_le_operator_norm _ a b).trans
      (specialLinear_inverse_norm_le_two hn (g i) hnorm)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hcij : c i=c j := congrArg Subtype.val hij
    have hdiff (a b : Fin n) : |(g j).val a b-(g i).val a b| ≤ 2*η*δ := by
      let t := finProdFinEquiv (a,b)
      have hi := hclose i t
      have hj := hclose j t
      rw [hcij] at hi
      have hqdiff : |q j t-q i t| ≤ 2*η := by
        calc
          _ = |(q j t-c j t)+(c j t-q i t)| := by congr 1; ring
          _ ≤ |q j t-c j t|+|c j t-q i t| := abs_add_le _ _
          _ ≤ 2*η := by rw [abs_sub_comm (c j t)]; linarith
      have he : (g j).val a b-(g i).val a b = δ*(q j t-q i t) := by
        dsimp [q,t]
        simp only [Equiv.symm_apply_apply]
        field_simp [hδ.ne']
        ring
      rw [he,abs_mul,abs_of_pos hδ]
      nlinarith [mul_le_mul_of_nonneg_left hqdiff hδ.le]
    let r : ℝ := 8*(n:ℝ)*η*δ
    have hr : 0 < r := by dsimp [r]; positivity
    have hnr : (n:ℝ)*r=δ/12 := by
      dsimp [r]
      calc
        _ = (8*(n:ℝ)^2*η)*δ := by ring
        _ = _ := by rw [hscale]; ring
    have hrel : (g i)⁻¹*g j ∈ matrixBall n r := by
      intro a b
      have hh := left_div_entry_bound (g i) (g j) (by norm_num : (0:ℝ) ≤ 2)
        (hinv i) hdiff a b
      apply hh.trans_lt
      dsimp [r]
      nlinarith [mul_pos hnp hη, mul_pos (mul_pos hnp hη) hδ]
    have ha : rightAction (rightAction x (g i)) ((g i)⁻¹*g j)=rightAction x (g j) := by
      rw [rightAction_mul]
      congr 1
      group
    have hd := (quotientLogDistance_le_length _ _ _ ha).trans
      (matrixLogLength_le_three_card_radius hn hr.le (by rw [hnr]; linarith) hrel)
    have hsep' := hsep i j hne
    have hh : 3*(n:ℝ)*r=δ/4 := by nlinarith [hnr]
    rw [hh] at hd
    linarith
  have hNs : N ≤ s.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact (show (N:ℝ) ≤ s.card by exact_mod_cast hNs).trans hcard

lemma local_quotient_packing_finset_bound {n : ℕ} (hn : 0 < n)
    {α : Type*} (S : Finset α) (z : α → X n) (x : X n)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hlift : ∀ i ∈ S, ∃ g ∈ matrixBall n (C*δ), rightAction x g=z i)
    (hsep : (S : Set α).Pairwise (fun i j => δ ≤ quotientLogDistance (z i) (z j))) :
    (S.card:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  choose g hg ha using (fun i : S => hlift i.val i.prop)
  let e : Fin S.card ≃ S := S.equivFin.symm
  apply local_quotient_packing_bound hn x (fun i => g (e i)) hC hδ hδ1 hsmall
    (fun i => hg (e i))
  intro i j hij
  rw [ha (e i),ha (e j)]
  apply hsep (e i).prop (e j).prop
  intro he
  exact hij (e.injective (Subtype.ext he))

lemma local_quotient_distance_packing_bound {n : ℕ} (hn : 0 < n)
    {α : Type*} (S : Finset α) (z : α → X n) (x : X n)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hloc : ∀ i ∈ S, quotientLogDistance x (z i) < Real.log (1+C*δ))
    (hsep : (S : Set α).Pairwise (fun i j => δ ≤ quotientLogDistance (z i) (z j))) :
    (S.card:ℝ) ≤ localQuotientPackingBound n C := by
  apply local_quotient_packing_finset_bound hn S z x hC.le hδ hδ1 hsmall _ hsep
  intro i hi
  exact exists_matrix_lift_of_logDistance_lt (mul_pos hC hδ) (hloc i hi)

end DukePrimeDegree

end

end OAI
