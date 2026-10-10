import OAI.NumberTheory.TotientAsymptotic.PPTTerminalPreimage
import OAI.NumberTheory.TotientAsymptotic.PPTHeadEdge
import OAI.NumberTheory.TotientAsymptotic.PPTResidualFamily

namespace OAI

/-! The actual residual lists determine one of the finite comparison grids.
The hypotheses below are arithmetic and geometric properties of those lists;
the published comparison conditions and parameters are conclusions. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_B_mono {x y : ℝ} (hx : 1<x) (hxy : x≤y) : B x≤B y :=
  Real.log_le_log (Real.log_pos hx) (Real.log_le_log (zero_lt_one.trans hx) hxy)

/-- A predecessor bounded by the comparison endpoint gives an upper
bound on its normalized largest-factor coordinate. -/
lemma ppt_factor_coordinate_upper {p : ℕ} {z : ℝ}
    (hp : 3 ≤ p) (hB : 0 < B z) (hpz : (p-1 : ℕ) ≤ z) :
    B (largestPrimeFactor (p-1))/B z ≤ 1 := by
  have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
  apply (div_le_one hB).mpr
  exact ppt_B_mono hlp
    ((Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega))).trans hpz)

/-- The vacant terminal interval pays for normality alignment at every
retained index, including the full bottom-grid padding. -/
lemma ppt_terminal_coordinate_padding {j H : ℕ} {t L U δ u v w : ℝ}
    (hj : j ≤ H) (ht : 0 < t) (hδ : 0 ≤ δ)
    (hhigh : U < w) (hfactor : w/t-δ ≤ u)
    (halign : |u-v| ≤ (2*(j : ℝ)+1)*δ)
    (hbudget : (8*(H : ℝ)+20)*δ*t < (U-L)/4) :
    (L+U)/(2*t)+3*δ < min u v := by
  have hjr : (j : ℝ) ≤ H := by exact_mod_cast hj
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hcost : (2*(j : ℝ)+5)*δ*t < (U-L)/2 := by
    have hc : (2*(j : ℝ)+5)*δ*t ≤ (8*(H : ℝ)+20)*δ*t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hjr,hH0]) hδ) ht.le
    have hw : 0 < U-L := by
      have hh : 0 ≤ (8*(H : ℝ)+20)*δ*t := by positivity
      linarith only [hbudget,hh]
    linarith only [hc,hbudget,hw]
  have hhigh' : U/t < w/t := div_lt_div_of_pos_right hhigh ht
  have hdiff : (L+U)/(2*t)+3*δ+(2*(j : ℝ)+1)*δ+δ < U/t := by
    apply (lt_div_iff₀ ht).mpr
    have he : ((L+U)/(2*t)+3*δ+(2*(j : ℝ)+1)*δ+δ)*t =
        (L+U)/2+(2*(j : ℝ)+5)*δ*t := by field_simp; ring
    rw [he]
    linarith only [hcost]
  apply lt_min
  · have hc : 0 ≤ (2*(j : ℝ)+1)*δ := by positivity
    linarith only [hdiff,hhigh',hfactor,hc]
  · linarith only [hdiff,hhigh',hfactor,(abs_le.mp halign).2]

/-- A terminal gap in the prime coordinates survives passage to the
largest factors and supplies the full bottom padding of the paired grid. -/
lemma ppt_terminal_grid_bottom {b H : ℕ} {t L U δ : ℝ}
    (hb : 0 < b) (hbH : b ≤ H) (ht : 0 < t) (hδ : 0 ≤ δ)
    (u v w : Fin b → ℝ)
    (hhigh : U < w ⟨b-1,by omega⟩)
    (hfactor : w ⟨b-1,by omega⟩/t-δ ≤ u ⟨b-1,by omega⟩)
    (halign : |u ⟨b-1,by omega⟩-v ⟨b-1,by omega⟩| ≤
      (2*((b-1 : ℕ) : ℝ)+1)*δ)
    (hbudget : (8*(H : ℝ)+20)*δ*t < (U-L)/4) :
    (L+U)/(2*t)+3*δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩) := by
  exact ppt_terminal_coordinate_padding (show b-1 ≤ H by omega) ht hδ
    hhigh hfactor halign hbudget

/-- Normality aligns the actual lists after cancellation.  Smoothness
of both integer multipliers is used only below their retained predecessors. -/
theorem ppt_pair_alignment_in_mesh {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop, ∀ (b H D : ℕ) (S V : ℝ) (p : ShiftedPair b),
      (H : ℝ) ≤ A*Real.log (B z) →
      1 < S → 0 ≤ B S → B S ≤ (H : ℝ)^4 → S ≤ V → V ≤ z →
      0 < D → 0 < p.remainder →
      (∀ i, IsNormalPrime S (p.left i) ∧ IsNormalPrime S (p.right i)) →
      (∀ i, 3 ≤ p.left i ∧ 3 ≤ p.right i) →
      Antitone p.left → Antitone p.right →
      D*shiftedProduct p.left = p.remainder*shiftedProduct p.right →
      (largestPrimeFactor D : ℝ) ≤ V → (largestPrimeFactor p.remainder : ℝ) ≤ V →
      (∀ i, V ≤ (p.left i-1 : ℕ) ∧ V ≤ (p.right i-1 : ℕ)) →
      (∀ i, (p.left i-1 : ℕ) ≤ z ∧ (p.right i-1 : ℕ) ≤ z) →
      ∀ i : Fin b,
        |B (largestPrimeFactor (p.left i-1))/B z-
          B (largestPrimeFactor (p.right i-1))/B z| ≤
          (2*(i.val : ℝ)+1)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
  filter_upwards [B_tendsto.eventually (ppt_local_alignment_in_paired_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hmesh hB
  intro b H D S V p hdim hS hBS hheight hSV hVz hD hE hp hp3 hpa hqa heq
    hDV hEV hsmall hsize i
  apply hmesh H i.val S _ _ hdim hBS hheight
  exact ppt_normalized_coordinate_alignment p.left p.right i.isLt i.isLt
    hS hBS hB (hSV.trans hVz) hD.ne' hE.ne'
    (fun j => (hp j).1) (fun j => (hp j).2) hpa hqa heq
    (hp3 i).1 (hp3 i).2 (hsize i).1 (hsize i).2
    (le_min (hDV.trans (hsmall i).1) (hDV.trans (hsmall i).2))
    (le_min (hEV.trans (hsmall i).1) (hEV.trans (hsmall i).2))
    (le_min (hSV.trans (hsmall i).1) (hSV.trans (hsmall i).2))

/-- All literal grid intervals, parameters, and comparison conditions
for an actual residual pair.  The first cutoff and the adjacent separation
are the quantitative prime-row conclusions established before grouping. -/
theorem ppt_pointwise_grid_realization {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (b H D c : ℕ) (S V L U : ℝ) (p : ShiftedPair b), ∀ hb : 0 < b,
      b ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H : ℝ)^4 →
      V = Real.exp (Real.exp ((L+U)/2)) → S ≤ V → V ≤ z →
      0 < D → 0 < c → 0 < p.remainder →
      (D : ℝ) ≤ z^(1/100 : ℝ) → (c.totient : ℝ) ≤ z^(1/10 : ℝ) →
      (∀ i, IsNormalPrime S (p.left i) ∧ IsNormalPrime S (p.right i)) →
      (∀ i, 3 ≤ p.left i ∧ 3 ≤ p.right i ∧ p.left i ≠ p.right i) →
      Antitone p.left → Antitone p.right →
      D*shiftedProduct p.left = p.remainder*shiftedProduct p.right →
      ((D*shiftedProduct p.left : ℕ) : ℝ) ≤ z/c.totient →
      SquarefreeAbove (D*shiftedProduct p.left) V →
      (largestPrimeFactor D : ℝ) ≤ V → (largestPrimeFactor p.remainder : ℝ) ≤ V →
      (∀ i, V ≤ (p.left i-1 : ℕ) ∧ V ≤ (p.right i-1 : ℕ)) →
      (∀ i, (p.left i-1 : ℕ) ≤ z ∧ (p.right i-1 : ℕ) ≤ z) →
      z^(9/10 : ℝ) ≤ p.left ⟨0,hb⟩ →
      0 ≤ L → U < B (p.left ⟨b-1,by omega⟩) →
      (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
      let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
      let label := fun i => collisionGridIndex δ (u i) (v i)
      let ζ := (L+U)/(2*B z)
      let θ := pptUniformHeadEdge (B z)-δ
      let ν := pairedGridUpper δ ζ label
      let μ := pptGridLower δ θ label
      ν 1 ≤ 1-γ/(Real.log (B z))^3 →
      (∀ i : Fin b, ∀ hi : i.val+1 < b,
        max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
          (2*(i.val : ℝ)+8)*δ < min (u i) (v i)) →
      label ∈ collisionGridFamilies δ b ∧
      FordComparisonParameters b z S D c.totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) ∧
      FordComparisonConditions b z S D c.totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) p ∧
      (∀ i : Fin b, 0 < i.val → ν i ≤ u i+(2*(b : ℝ)+3)*δ) ∧
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ (2*(b : ℝ)+3)*δ) := by
  filter_upwards [ppt_pair_alignment_in_mesh hA, ppt_normal_factor_loss_mesh,
    ppt_normal_head_uniform_edge, ppt_normalized_pair_conditions,
    B_tendsto.eventually (ppt_first_cutoff_below_aligned_head hγ),
    B_tendsto.eventually (ppt_inverse_log_cube_cutoff_loss hγ),
    B_tendsto.eventually (ppt_local_normality_error_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z halign hfactor hhead hconditions hfirst
      hlogloss hmesh hB hz
  intro b H D c S V L U p hb hbH hdim hS hheight hV hSV hVz hD hc hE hDz hcz
    hp hp3 hpa hqa heq hsize hsq hDV hEV hsmall hpred hlarge hL hhigh hbudget
  dsimp only
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (p.left i-1))/B z
  let v := fun i => B (largestPrimeFactor (p.right i-1))/B z
  let label := fun i => collisionGridIndex δ (u i) (v i)
  let ζ := (L+U)/(2*B z)
  let θ := pptUniformHeadEdge (B z)-δ
  let ν := pairedGridUpper δ ζ label
  let μ := pptGridLower δ θ label
  intro hν hnext
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hlog : 0 < Real.log (B z) := Real.log_pos hB
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hS1 : 1 < S :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hSz := hSV.trans hVz
  have hclose : ∀ i : Fin b, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ :=
    halign b H D S V p hdim hS1 hBS hheight hSV hVz hD hE hp
      (fun i => ⟨(hp3 i).1,(hp3 i).2.1⟩) hpa hqa heq hDV hEV hsmall hpred
  have hU : L < U := by
    have hh : 0 ≤ (8*(H : ℝ)+20)*δ*B z := by positivity
    linarith only [hbudget,hh]
  have hζ : 0 ≤ ζ := by
    dsimp only [ζ]
    exact div_nonneg (by linarith only [hL,hU]) (by positivity)
  have hpadding (i : Fin b) : ζ+3*δ < min (u i) (v i) := by
    have hilast : i ≤ (⟨b-1,by omega⟩ : Fin b) := by
      change i.val ≤ b-1
      omega
    have hmono : B (p.left ⟨b-1,by omega⟩) ≤ B (p.left i) :=
      ppt_B_mono (by exact_mod_cast (show 1 < p.left ⟨b-1,by omega⟩ by
        have := (hp3 ⟨b-1,by omega⟩).1; omega))
        (Nat.cast_le.mpr (hpa hilast))
    exact ppt_terminal_coordinate_padding (show i.val ≤ H by omega) hB0 hδ.le
      (hhigh.trans_le hmono)
      (hfactor (p.left i) S (hp3 i).1 hS1 hBS hSz (hp i).1 (hpred i).1).1
      (hclose i) hbudget
  have hu (i : Fin b) : 0 ≤ u i ∧ u i ≤ 1 :=
    ⟨(by have := (hpadding i).trans_le (min_le_left _ _); linarith only [this,hζ,hδ]),
      ppt_factor_coordinate_upper (hp3 i).1 hB0 (hpred i).1⟩
  have hv (i : Fin b) : 0 ≤ v i ∧ v i ≤ 1 :=
    ⟨(by have := (hpadding i).trans_le (min_le_right _ _); linarith only [this,hζ,hδ]),
      ppt_factor_coordinate_upper (hp3 i).2.1 hB0 (hpred i).2⟩
  have hbottom := hpadding ⟨b-1,by omega⟩
  have hheadL := hhead (p.left ⟨0,hb⟩) S hS1 hBS hSz (hp _).1 hlarge (hpred _).1
  have hθ := ppt_aligned_heads_uniform_edge hB.le hheadL.1 (hclose ⟨0,hb⟩)
  have hθ' : θ ≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩) ∧ θ < 1 := by
    simpa [θ,u,v] using hθ
  have hνθ : ν 1 < θ := hfirst (ν 1) δ hν le_rfl
  have hnext4 (i : Fin b) (hi : i.val+1 < b) :
      max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
        (2*(i.val+1 : ℕ)+4 : ℝ)*δ < min (u i) (v i) := by
    have hh := hnext i hi
    push_cast
    linarith only [hh,hδ]
  have hnext6 (i : Fin b) (hi : i.val+1 < b) :
      max (u ⟨i.val+1,hi⟩) (v ⟨i.val+1,hi⟩)+
        (2*(i.val+1 : ℕ)+6 : ℝ)*δ < min (u i) (v i) := by
    have he : (2*(i.val+1 : ℕ)+6 : ℝ) = 2*(i.val : ℝ)+8 := by
      push_cast
      ring
    rw [he]
    exact hnext i hi
  have hinterval := ppt_grid_intervals hb hδ u v (fun i => (hu i).1)
    (fun i => (hv i).1) hclose (max_le (hu _).2 (hv _).2) hθ'.1 hθ'.2 hνθ hnext4
    (lt_of_le_of_lt (by linarith only [hδ] : ζ+δ ≤ ζ+3*δ) hbottom)
  have hgaps := paired_grid_gaps hb hδ u v (fun i => (hu i).1)
    (fun i => (hv i).1) hclose hnext6 hbottom
  have hη : Real.sqrt (B S/B z) ≤ δ := by
    have hh := hmesh H S hdim hBS hheight
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by positivity
    linarith only [hh,hm]
  have hVeq : comparisonCutoffs z ν b = V := by
    have he : ν b = ζ := by simp [ν,pairedGridUpper,show b ≠ 0 by omega]
    rw [comparisonCutoffs,he,hV]
    congr 2
    dsimp only [ζ]
    field_simp
  have hfirstlog : Real.log (10*B z) ≤ B z*(1-ν 1) := by
    have hh := mul_le_mul_of_nonneg_left
      (show γ/(Real.log (B z))^3 ≤ 1-ν 1 by linarith only [hν]) hB0.le
    have he : B z*(γ/(Real.log (B z))^3) = γ*B z/(Real.log (B z))^3 := by ring
    rw [he] at hh
    exact hlogloss.trans hh
  have hparams : FordComparisonParameters b z S D c.totient
      (comparisonCutoffs z ν) (comparisonCutoffs z μ) :=
    ppt_ford_parameters_from_grid hb hz hB0 D c.totient label hS
      (hVeq.symm ▸ hSV) hinterval.2.2.2 hfirstlog
      (fun j hj => (mul_le_mul_of_nonneg_left hη (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
        (hgaps j hj)) hD hDz (hVeq.symm ▸ hDV) (Nat.totient_pos.mpr hc) hcz
  refine ⟨collisionGridFamilies_mem hδ u v (fun i => (hu i).2),hparams,?_,?_⟩
  · apply hconditions b D c.totient S ν μ p hb hB0 hS1 hBS hSz
      (fun i => (hp i).1) (fun i => (hp i).2)
      (fun i => (hp3 i).1) (fun i => (hp3 i).2.1) (fun i => (hp3 i).2.2)
      hE heq hsize (hVeq.symm ▸ hsq) (hVeq.symm ▸ hEV)
    · intro i
      exact ⟨(hinterval.2.2.1 i).1,(hinterval.2.2.1 i).2.2.1,
        (hinterval.2.2.1 i).2.1,(hinterval.2.2.1 i).2.2.2⟩
    · exact hlarge
    · exact (hpred _).1
    · exact (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).le
    · exact ppt_comparison_cutoff_power_of_log_loss hz hB0 hfirstlog
  · exact ppt_paired_grid_row_errors hδ u v (fun i => (hu i).1)
      (fun i => (hv i).1) hclose

end TotientAsymptotic

end

end OAI
