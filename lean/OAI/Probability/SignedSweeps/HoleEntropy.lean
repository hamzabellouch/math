import OAI.Probability.SignedSweeps.BaseCases

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def occupancy {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) : Fin (l + 1) :=
  ⟨(Finset.univ.filter (fun i => f i = j)).card,
    Nat.lt_succ_iff.mpr ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Fintype.card_fin l))⟩

lemma occupancy_sum {l q : ℕ} (f : Fin l → Fin q) :
    ∑ j, (occupancy f j).val = l := by
  simpa [occupancy] using
    Finset.sum_fiberwise' Finset.univ f (fun _ : Fin q => (1 : ℕ))

lemma occupancy_at_pos {l q : ℕ} (f : Fin l → Fin q) (i : Fin l) :
    0 < (occupancy f (f i)).val := by
  change 0 < (Finset.univ.filter (fun j => f j = f i)).card
  exact Finset.card_pos.mpr ⟨i, by simp⟩

lemma occupancy_sum_smul {l q : ℕ} (f : Fin l → Fin q) (a : Fin q → ℝ) :
    ∑ j, ((occupancy f j).val : ℝ) * a j = ∑ i, a (f i) := by
  simpa [occupancy] using Finset.sum_fiberwise' Finset.univ f a

def occupancyEntropy {l q : ℕ} (a : ℝ) (f : Fin l → Fin q) : ℝ :=
  ∑ j, ((occupancy f j).val : ℝ) * Real.log (a / (occupancy f j).val)

def empiricalDensity {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) : ℝ :=
  (occupancy f j).val / (l : ℝ)

lemma empiricalDensity_nonneg {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) :
    0 ≤ empiricalDensity f j := by unfold empiricalDensity; positivity

lemma empiricalDensity_sum {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) :
    ∑ j, empiricalDensity f j = 1 := by
  unfold empiricalDensity
  rw [← Finset.sum_div, ← Nat.cast_sum, occupancy_sum, div_self]
  exact_mod_cast hl.ne'

lemma empiricalDensity_at_pos {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) (i : Fin l) :
    0 < empiricalDensity f (f i) := by
  unfold empiricalDensity
  exact div_pos (by exact_mod_cast occupancy_at_pos f i) (by exact_mod_cast hl)

lemma empiricalDensity_total {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q) :
    ∑ g : Fin l → Fin q, ∏ i, empiricalDensity f (g i) = 1 := by
  rw [← Fintype.sum_pow, empiricalDensity_sum hl f, one_pow]

lemma occupancy_entropy_weight {l q : ℕ} (hl : 0 < l) (f : Fin l → Fin q)
    {a : ℝ} (ha : 0 < a) :
    Real.exp (-occupancyEntropy a f) =
      Real.exp (-(l : ℝ) * Real.log (a / l)) * ∏ i, empiricalDensity f (f i) := by
  have hn : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have halog : ∀ i, Real.log (a / (occupancy f (f i)).val) =
      Real.log (a / l) - Real.log (empiricalDensity f (f i)) := by
    intro i
    have hh : ((occupancy f (f i)).val : ℝ) ≠ 0 := by
      exact_mod_cast (occupancy_at_pos f i).ne'
    rw [empiricalDensity, Real.log_div ha.ne' hh, Real.log_div ha.ne' hn,
      Real.log_div hh hn]
    ring
  have hd : -occupancyEntropy a f =
      -(l : ℝ) * Real.log (a / l) + ∑ i, Real.log (empiricalDensity f (f i)) := by
    unfold occupancyEntropy
    rw [occupancy_sum_smul]
    simp_rw [halog]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hd, Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.exp_log (empiricalDensity_at_pos hl f i)

lemma occupancy_entropy_fiber_bound {l q : ℕ} (hl : 0 < l)
    {a : ℝ} (ha : 0 < a) (h : Fin q → Fin (l + 1)) :
    ∑ f : Fin l → Fin q with occupancy f = h, Real.exp (-occupancyEntropy a f) ≤
      Real.exp (-(l : ℝ) * Real.log (a / l)) := by
  classical
  let S := Finset.univ.filter (fun f : Fin l → Fin q => occupancy f = h)
  change ∑ f ∈ S, _ ≤ _
  rcases Finset.eq_empty_or_nonempty S with hempty | ⟨f, hf⟩
  · simp only [hempty, Finset.sum_empty]
    exact (Real.exp_pos _).le
  · have hh : occupancy f = h := (Finset.mem_filter.mp hf).2
    have he (g : Fin l → Fin q) (hg : g ∈ S) : empiricalDensity g = empiricalDensity f := by
      have hhg := (Finset.mem_filter.mp hg).2
      funext j
      simp only [empiricalDensity, hhg, hh]
    calc
      _ = Real.exp (-(l : ℝ) * Real.log (a / l)) *
          ∑ g ∈ S, ∏ i, empiricalDensity f (g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [occupancy_entropy_weight hl g ha, he g hg]
      _ ≤ Real.exp (-(l : ℝ) * Real.log (a / l)) *
          ∑ g : Fin l → Fin q, ∏ i, empiricalDensity f (g i) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun g hg hgn => Finset.prod_nonneg (fun i hi => empiricalDensity_nonneg f (g i)))
      _ = _ := by rw [empiricalDensity_total hl f, mul_one]

lemma occupancy_entropy_sum {l q : ℕ} {a : ℝ} (ha : 0 < a) :
    ∑ f : Fin l → Fin q, Real.exp (-occupancyEntropy a f) ≤
      Real.exp (-(l : ℝ) * Real.log (a / l)) * (l + 1 : ℝ) ^ q := by
  classical
  by_cases hl : l = 0
  · subst l
    simp [occupancyEntropy, occupancy]
  · have hl' : 0 < l := Nat.pos_of_ne_zero hl
    rw [← Finset.sum_fiberwise Finset.univ occupancy
      (fun f : Fin l → Fin q => Real.exp (-occupancyEntropy a f))]
    apply (Finset.sum_le_sum (fun h _ => occupancy_entropy_fiber_bound hl' ha h)).trans_eq
    simp [mul_comm]

abbrev HolePlacement (s m l : ℕ) :=
  {z : Fin l → Fin s × Fin m // Function.Injective z}

def holeLineEntropy {s m l : ℕ} (z : Fin l → Fin s × Fin m) : ℝ :=
  occupancyEntropy (s : ℝ) (fun i => (z i).2) +
    occupancyEntropy (m : ℝ) (fun i => (z i).1)

lemma hole_entropy_with_replacement {s m l : ℕ} :
    ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) =
      (∑ rows : Fin l → Fin s, Real.exp (-occupancyEntropy (m : ℝ) rows)) *
      (∑ cols : Fin l → Fin m, Real.exp (-occupancyEntropy (s : ℝ) cols)) := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin l) (fun _ => Fin s) (fun _ => Fin m)
  calc
    _ = ∑ p : (Fin l → Fin s) × (Fin l → Fin m),
        Real.exp (-occupancyEntropy (m : ℝ) p.1) *
          Real.exp (-occupancyEntropy (s : ℝ) p.2) := by
      apply Fintype.sum_equiv e
      intro z
      change Real.exp (-(occupancyEntropy (s : ℝ) (fun i => (z i).2) +
        occupancyEntropy (m : ℝ) (fun i => (z i).1))) = _
      rw [neg_add, Real.exp_add, mul_comm]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun rows : Fin l → Fin s => Real.exp (-occupancyEntropy (m : ℝ) rows))
        (fun cols : Fin l → Fin m => Real.exp (-occupancyEntropy (s : ℝ) cols))).symm

lemma hole_entropy_drop_distinctness {s m l : ℕ} :
    ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun z : Fin l → Fin s × Fin m =>
    Function.Injective z)) (by simp) (fun z => Real.exp (-holeLineEntropy z))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun z hz hzn => (Real.exp_pos _).le)

lemma inverse_pow_eq_exp_log {x : ℝ} (hx : 0 < x) (l : ℕ) :
    (x ^ l)⁻¹ = Real.exp (-(l : ℝ) * Real.log x) := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx]

lemma hole_assignment_entropy_bound {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l)) *
        (l + 1 : ℝ) ^ (s + m) := by
  classical
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hl : l = 0
  · subst l
    simp [holeLineEntropy, occupancyEntropy, occupancy, HolePlacement]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hl' : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
  have hn : (0 : ℝ) < (s * m : ℕ) := by exact_mod_cast Nat.mul_pos hs hm
  have hf : (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        (Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) * (l + 1 : ℝ) ^ s) *
        (Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l)) * (l + 1 : ℝ) ^ m) =
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l)) *
        (l + 1 : ℝ) ^ (s + m) := by
    rw [inverse_pow_eq_exp_log hn, pow_add]
    calc
      _ = (Real.exp (-(l : ℝ) * Real.log ((s * m : ℕ) : ℝ)) *
          Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) *
          Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l))) *
            ((l + 1 : ℝ) ^ s * (l + 1 : ℝ) ^ m) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [Nat.cast_mul, Real.log_mul hs'.ne' hm'.ne',
          Real.log_div hm'.ne' hl'.ne', Real.log_div hs'.ne' hl'.ne',
          Real.log_div (mul_pos hs' hm').ne' hl'.ne', Real.log_mul hs'.ne' hm'.ne']
        ring
  calc
    _ ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : Fin l → Fin s × Fin m, Real.exp (-holeLineEntropy z) :=
      mul_le_mul_of_nonneg_left hole_entropy_drop_distinctness (by positivity)
    _ = (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ((∑ rows : Fin l → Fin s, Real.exp (-occupancyEntropy (m : ℝ) rows)) *
          ∑ cols : Fin l → Fin m, Real.exp (-occupancyEntropy (s : ℝ) cols)) := by
      rw [hole_entropy_with_replacement]
    _ ≤ (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ((Real.exp (-(l : ℝ) * Real.log ((m : ℝ) / l)) * (l + 1 : ℝ) ^ s) *
          (Real.exp (-(l : ℝ) * Real.log ((s : ℝ) / l)) * (l + 1 : ℝ) ^ m)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (occupancy_entropy_sum hm') (occupancy_entropy_sum hs')
        (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    _ = _ := by rw [← mul_assoc, hf]

lemma hole_assignment_entropy_bound_exp {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) :
    (((s * m : ℕ) : ℝ) ^ l)⁻¹ *
        ∑ z : HolePlacement s m l, Real.exp (-holeLineEntropy z.1) ≤
      Real.exp (-2 * (l : ℝ) * Real.log (((s * m : ℕ) : ℝ) / l) +
        (s + m : ℝ) * Real.log (l + 1)) := by
  refine (hole_assignment_entropy_bound hs hm).trans_eq ?_
  rw [Real.exp_add, show (s + m : ℝ) = ((s + m : ℕ) : ℝ) by norm_cast,
    Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < l + 1)]

end SignedSweeps
end

end OAI
