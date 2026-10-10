import OAI.Probability.ContinuumTransition.LatticeBounds

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem sum_comp_eq_sum_fibres {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (c : ι → κ) (f : κ → ℝ) :
    (∑ i, f (c i)) = ∑ k, (Fintype.card {i // c i = k} : ℝ) * f k := by
  symm
  calc
    _ = ∑ k, ∑ _i : {i // c i = k}, f k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ k, ∑ i : {i // c i = k}, f (c i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ = _ := Fintype.sum_fiberwise c (fun i => f (c i))

theorem pairSum_le_cell_quadratic {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (J : κ → κ → ℝ) (F : ι → ι → ℝ)
    (hJ : ∀ k l, 0 ≤ J k l) (hsym : ∀ i j, F i j = F j i)
    (hF : ∀ i j, F i j ≤ J (c i) (c j)) :
    pairSum F ≤ (1 / 2 : ℝ) * ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
  classical
  have hh (i j : ι) : (if i = j then 0 else F i j) ≤ J (c i) (c j) := by
    split_ifs
    · exact hJ _ _
    · exact hF _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hh i j))
  rw [← two_mul_pairSum F hsym] at hs
  have hsum : (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
    calc
      _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ) * J (c i) l := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
      _ = ∑ k, (Fintype.card {i // c i = k} : ℝ) *
          (∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l) :=
        sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum] at hs
  linarith

theorem physicalProfile_pairSum_lower {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    {ι : Type u_1} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    -(t ^ 2 / 2) * Fintype.card ι ≤ pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let s := Finset.univ.image (fun i : ι => cellIndex (x i))
  let c (i : ι) : s := ⟨cellIndex (x i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let J (k l : s) := (t * kernelHeight) * mixedEnvelope σ R k l
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : s) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) k l)
  have hJsym (k l : s) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : s) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left
      (sum_mixedEnvelope_le (fun l : s => (l : Lattice)) Subtype.val_injective hσ hR hs k)
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => attraction_le_mixedEnvelope ht hσ hR hs _ _)
  have hb := superstable_algebra J (fun k : s => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  have hn : 0 ≤ ∑ k : s, (Fintype.card {i // c i = k} : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 0 ≤ t ^ 2 / 8 - M / 2 := sub_nonneg.mpr hsmall
  have hp := mul_nonneg hm hn
  have heq : pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) =
      pairSum (fun i j => coreProfile t ‖x i - x j‖) -
      pairSum (fun i j => attraction t σ R ‖x i - x j‖) := by
    simp only [pairSum, physicalProfile, Finset.sum_sub_distrib]
  rw [heq]
  linarith

theorem ereal_coe_sum {ι : Type u_1} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simpa only [Finset.sum_insert hi, EReal.coe_add] using congrArg (fun z => (f i : EReal) + z) ih

theorem coe_pairSum_le_energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    ((pairSum (fun i j => φ ‖x i - x j‖) : ℝ) : EReal) ≤ energy φ x := by
  classical
  simp only [pairSum, energy, ereal_coe_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold radialPotential
  split_ifs
  · exact le_top
  · rfl

theorem physicalProfile_stable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) :
    ((-(t ^ 2 / 2) * (N : ℝ) : ℝ) : EReal) ≤ energy (physicalProfile t σ R) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simpa only [Fintype.card_fin] using physicalProfile_pairSum_lower ht hσ hR hs hsmall x

theorem admissible_physicalProfile {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (hσ0 : 0 < σ 0) (hR0 : 4 ≤ R 0) : Admissible (physicalProfile t σ R) := by
  refine ⟨measurable_radialPotential (measurable_physicalProfile t hσ hR hs), ?_,
    physicalProfile_tendsto_zero (by linarith) hσ hR hs, ?_, ?_, ?_⟩
  · intro a b ha _
    exact physicalProfile_locally_bounded (by linarith) hσ hR hs ha
  · obtain ⟨a, ha, hneg⟩ := physicalProfile_negative_annulus ht hσ hR hs hσ0 hR0
    exact ⟨1, 2, a, by norm_num, by norm_num, ha, hneg⟩
  · exact ⟨1, by norm_num, integrable_weighted_physicalProfile ht hσ hR hs⟩
  · exact ⟨t ^ 2 / 2, physicalProfile_stable (by linarith) hσ hR hs hsmall⟩

theorem physicalProfile_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let J (k l : κ) := (t * kernelHeight) * mixedEnvelope σ R (e k) (e l)
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : κ) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) (e k) (e l))
  have hJsym (k l : κ) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : κ) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs (e k))
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq ((hc i).trans ((congrArg e hij).trans (hc j).symm)))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => by
      have hh := attraction_le_mixedEnvelope ht hσ hR hs (x i) (x j)
      simpa only [hc, J] using hh)
  have hb := superstable_algebra J (fun k : κ => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  simpa only [pairSum, physicalProfile, Finset.sum_sub_distrib] using hb

end
end ContinuumTemperature
end

end OAI
