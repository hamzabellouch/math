import OAI.MeasureTheory.Falconer.Estimates.ScalarDyadicPowers

namespace OAI

/-! A quantitative scalar projection theorem with weak Frostman constants.
 It is proved on the original dyadic point set, with no published input. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ B M0 : ℕ, ∃ ε : ℝ, 0 < B ∧ 0 < M0 ∧ 0 < ε ∧
      ∀ M : ℕ, M0 ≤ M →
      let δ := (1/2:ℝ)^(B*M)
      let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
      ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
        W*(L.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass (L.image scalarPathCenter) u r ≤
        W*r^κ*(L.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(L.card:ℝ) <
        ((scalarCells δ (L.image scalarPathCenter+
          (L.image scalarPathCenter).image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,copies,η,hB,hcopies,hη,hgrowth⟩ :=
    scalar_weak_block_projection hκ hκ1 (by positivity : 0 < (12:ℝ)^κ)
  obtain ⟨c,p,q,hc,hp,hq,hcost⟩ := scalar_normalization_cost hκ
  obtain ⟨ε,M0,hε,hM0,hparameters⟩ := scalar_weak_scale_parameters hκ hη hc hp hq B copies hB
  refine ⟨B,M0,ε,hB,hM0,hε,?_⟩
  intro M hM
  dsimp only
  intro L hL hne hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^(B*M)
  let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hprefix,hfold,hsmall,hstrict,hfinal⟩ := hparameters M hM
  have hballbudget : W^2*δ^κ ≤ 1 := by
    have he : W^2*δ^κ = Real.exp ((2*ε-κ)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
      dsimp [W,δ]
      rw [pow_two,← Real.exp_add,scalar_dyadic_power,← Real.exp_add]
      push_cast
      congr 1
      ring
    rw [he]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hradiusbudget : (2:ℝ)^κ*W*δ^κ < 1 := by
    have he : (2:ℝ)^κ*W*δ^κ =
        Real.exp (κ*Real.log 2+(ε-κ)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
      dsimp [W,δ]
      rw [Real.rpow_def_of_pos (by norm_num),scalar_dyadic_power,
        ← Real.exp_add,← Real.exp_add]
      push_cast
      congr 1
      ring
    rw [he]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  obtain ⟨z,hz,R,hRδ,hR2,hcandidate,hradius,hA,hAb,hAsize,hAball⟩ :=
    scalar_normalized_coefficients_candidate hδ hδ1 hκ.le hW1 hballbudget E hE hEbound hEball
  let A := scalarZoom (z-3*R) (6*R) (E.filter fun x => |x-z| ≤ R)
  have hR : 0 < R := hδ.trans_le hRδ
  have hRstrict : δ < R := scalar_density_radius_strict hRδ hradius hradiusbudget
  have hcell : (scalarCells δ (L.image scalarPathCenter)).card = L.card := scalar_leaf_cells_card L hL
  have hLcard : (L.image scalarPathCenter).card = L.card := scalar_leaf_center_card L hL
  have hweak : Real.log W ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 := by
    rw [show Real.log W = ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _]
    nlinarith
  have hsum : Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*W) ≤
      (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    rw [Real.log_mul (by norm_num) hW.ne',show Real.log W =
      ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _]
    nlinarith
  have hadd' : ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
      W*(scalarCells δ (L.image scalarPathCenter)).card := by rwa [hcell]
  have hpoint' : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u r ≤ W*r^κ*((L.image scalarPathCenter).card:ℝ) := by
    simpa only [hLcard] using hpoint
  obtain ⟨t,ht,hgain⟩ := hgrowth M (hM0.trans_le hM) W W hW hW hweak hsum L hL hne
    hsize hadd' hpoint' A hA hAb hAball
  by_contra hn
  push Not at hn
  have hproj : ∀ a ∈ E, ((scalarCells δ (L.image scalarPathCenter+
      (L.image scalarPathCenter).image (fun x => a*x))).card:ℝ) ≤
        W*(scalarCells δ (L.image scalarPathCenter)).card := by
    simpa only [hcell] using hn
  have hupper := scalar_normalized_projection_bound hδ hW1 (L.image scalarPathCenter) E
    (hne.image _) hz hEbound hcandidate hRstrict (scalarNormalizationRadius κ W)
    (scalar_density_inverse_radius hκ hW hR hradius) hadd' hproj t ht
  have hlog := hcost W W hW1 hW1
  rw [show Real.log W = ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _] at hlog
  have hlog' : Real.log (scalarNormalizedProjectionBudget (scalarNormalizationRadius κ W) W) ≤
      η*(M:ℝ)*Real.log 2 := by nlinarith
  have hpos : 0 < scalarNormalizedProjectionBudget (scalarNormalizationRadius κ W) W :=
    lt_of_lt_of_le (by norm_num) (scalarCoefficientBudget_one_le _
      (scalar_normalized_base_one_le _ hW1) _)
  have hb := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log hpos] at hb
  rw [hcell] at hupper
  have hh := hupper.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg L.card))
  exact (not_lt_of_ge hh) hgain

end Falconer.Regularization

end OAI
