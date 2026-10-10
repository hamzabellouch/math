import OAI.Combinatorics.ContingencyTables.Dense.AffineRegionVolume
import OAI.Combinatorics.ContingencyTables.Dense.DenseLocalGeometry

namespace OAI

/-! # Inner-polytope and penalty-sublevel volume for the actual margins -/

namespace ContingencyTables.DenseAffine

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def normalizedOffset (R : Option I → ℕ) (P : Option J → ℕ) (g : Option I × Option J) : ℝ :=
  entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

def normalizedCoeff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (g : Option I × Option J) (p : I × J) : ℝ :=
  entryCoeff (denseWidth R P d) g p /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

def normalizedRegion (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (γ : ℝ) : Set (I × J → ℝ) := {x | ∀ g, γ ≤ normalizedEntry R P d x g}

theorem normalizedRegion_eq_affine (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (γ : ℝ) :
    normalizedRegion R P d γ =
      AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d) γ := by
  ext x
  simp only [normalizedRegion, AffinePenalty.region, Set.mem_ofPred_eq,
    normalizedEntry, normalized_table_affine, normalizedOffset]
  rfl

theorem normalizedEntry_continuous (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (g : Option I × Option J) : Continuous (fun x => normalizedEntry R P d x g) := by
  have heq : (fun x => normalizedEntry R P d x g) =
      (fun x => AffinePenalty.affineValue (normalizedOffset R P g) (normalizedCoeff R P d g) x) := by
    funext x
    exact normalized_table_affine _ _ _ _ _
  rw [heq]
  exact continuous_const.add (continuous_finsetSum Finset.univ
    (fun p _ => continuous_const.mul (continuous_apply p)))

theorem normalizedRegion_closed (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (γ : ℝ) : IsClosed (normalizedRegion R P d γ) := by
  have heq : normalizedRegion R P d γ =
      ⋂ g, {x | γ ≤ normalizedEntry R P d x g} := by
    ext x
    simp only [normalizedRegion, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun g => isClosed_le continuous_const (normalizedEntry_continuous R P d g))

omit [DecidableEq I] [DecidableEq J] in
theorem normalizedRegion_zero (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) :
    normalizedRegion R P d 0 = {x | Feasible R P d x} := by
  have hs (g : Option I × Option J) :
      0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
    change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
    apply lt_min
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR _))
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP _))
  ext x
  constructor
  · intro hx i j
    have h := hx (i, j)
    change 0 ≤ _ / cellScale _ _ (i, j) at h
    simpa only [zero_mul] using (le_div_iff₀ (hs (i, j))).mp h
  · intro hx g
    exact div_nonneg (hx g.1 g.2) (hs g).le

theorem dense_feasible_compact (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (htotal : ∑ i, R i = ∑ j, P j) :
    IsCompact {x : I × J → ℝ | Feasible R P d x} := by
  have hclosed : IsClosed {x : I × J → ℝ | Feasible R P d x} := by
    rw [← normalizedRegion_zero R P d hd hR hP]
    exact normalizedRegion_closed R P d 0
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro x hx
  have h := feasible_in_cube R P d hd hR hP htotal x hx
  exact ⟨fun p => (h p).1, fun p => (h p).2⟩

theorem dense_inner_contraction (d : ℕ) (hd : 14 ≤ d) (q : ℕ) (hq : q ≤ d) :
    0 ≤ 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8 ∧
    4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8 ≤ 1 ∧
    (1 / 2 : ℝ) ≤ (1 - 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) ^ q := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  let α := 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8
  have hα : 0 ≤ α := by positivity
  have hp : 8 * d ^ 3 ≤ d ^ 8 := by
    have hfive : 8 ≤ d ^ 5 := (show 8 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
    calc
      _ ≤ d ^ 5 * d ^ 3 := Nat.mul_le_mul_right _ hfive
      _ = _ := by ring
  have hsmall : (d : ℝ) * α ≤ 1 / 2 := by
    have hp' : 8 * (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 8 := by exact_mod_cast hp
    have heq : (d : ℝ) * α = 4 * (d : ℝ) ^ 3 / (d : ℝ) ^ 8 := by dsimp [α]; ring
    rw [heq]
    apply (div_le_iff₀ (pow_pos hd₀ 8)).mpr
    nlinarith
  have hα₁ : α ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hd₁ hα
    nlinarith
  have hq' : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hbern := one_add_mul_le_pow (a := -α) (by linarith : -2 ≤ -α) q
  have hqα := mul_le_mul_of_nonneg_right hq' hα
  refine ⟨hα, hα₁, ?_⟩
  change (1 / 2 : ℝ) ≤ (1 - α) ^ q
  have heq : 1 + -α = 1 - α := by ring
  rw [heq] at hbern
  nlinarith

theorem dense_inner_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j) :
    (1 / 2 : ℝ≥0∞) * volume {x : I × J → ℝ | Feasible R P d x} ≤
      volume (normalizedRegion R P d (2 * (d : ℝ) / (d : ℝ) ^ 8)) := by
  obtain ⟨u, _, _, hu⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hα := dense_inner_contraction d hd (Fintype.card (I × J)) hfree
  have hc : u ∈ AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d)
      (1 / (2 * (d : ℝ))) := by
    rw [← normalizedRegion_eq_affine]
    exact hu
  have hvol := AffinePenalty.inner_region_volume (normalizedOffset R P) (normalizedCoeff R P d)
    u (1 / (2 * (d : ℝ))) (4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) hα.1 hα.2.1 hc
  have heq : (4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) * (1 / (2 * (d : ℝ))) =
      2 * (d : ℝ) / (d : ℝ) ^ 8 := by field_simp; ring
  rw [heq, ← normalizedRegion_eq_affine, ← normalizedRegion_eq_affine,
    normalizedRegion_zero R P d hd hR hP] at hvol
  apply le_trans _ hvol
  apply mul_le_mul_left
  have hb := ENNReal.ofReal_le_ofReal hα.2.2
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hb

theorem dense_relaxed_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    volume (normalizedRegion R P d (-γ)) ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 * γ)) *
        volume {x : I × J → ℝ | Feasible R P d x} := by
  obtain ⟨u, _, _, hu⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hc : u ∈ AffinePenalty.region (normalizedOffset R P) (normalizedCoeff R P d)
      (1 / (2 * (d : ℝ))) := by
    rw [← normalizedRegion_eq_affine]
    exact hu
  have hvol := AffinePenalty.relaxed_region_volume_exp (normalizedOffset R P) (normalizedCoeff R P d)
    u (d : ℝ) γ (by exact_mod_cast (show 0 < d by omega)) hγ (by exact_mod_cast hfree) hc
  rw [← normalizedRegion_eq_affine, ← normalizedRegion_eq_affine,
    normalizedRegion_zero R P d hd hR hP] at hvol
  exact hvol

theorem dense_sublevel_volume (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (s : ℝ) (hs : 0 ≤ s) :
    volume {x : I × J → ℝ | densePenalty R P d x ≤ s} ≤
      ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + s))) *
        volume {x : I × J → ℝ | Feasible R P d x} := by
  have hsub : {x : I × J → ℝ | densePenalty R P d x ≤ s} ⊆
      normalizedRegion R P d (-((d : ℝ) / (d : ℝ) ^ 8 + s)) := by
    intro x hx g
    change densePenalty R P d x ≤ s at hx
    have hb := AffinePenalty.component_le_penalty (normalizedOffset R P) (normalizedCoeff R P d)
      ((d : ℝ) / (d : ℝ) ^ 8) x (some g)
    change -AffinePenalty.affineValue _ _ x - (d : ℝ) / (d : ℝ) ^ 8 ≤ densePenalty R P d x at hb
    change -((d : ℝ) / (d : ℝ) ^ 8 + s) ≤ normalizedEntry R P d x g
    have heq : normalizedEntry R P d x g =
        AffinePenalty.affineValue (normalizedOffset R P g) (normalizedCoeff R P d g) x :=
      normalized_table_affine _ _ _ _ _
    rw [heq]
    linarith
  exact (measure_mono hsub).trans (dense_relaxed_volume R P d hd hR hP hdimR hdimP hfree
    htotal _ (add_nonneg (by positivity) hs))

end

end ContingencyTables.DenseAffine

end OAI
