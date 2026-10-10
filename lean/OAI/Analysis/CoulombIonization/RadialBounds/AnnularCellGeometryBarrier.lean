import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.UnshiftedCellCountBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombObservation CoulombBarrier

 def closedAnnularShell (alpha beta : ℝ) : Set Space := {x | alpha ≤ ‖x‖ ∧ ‖x‖ ≤ beta}
lemma closedAnnularShell_compact (alpha beta : ℝ) : IsCompact (closedAnnularShell alpha beta) := by
  have he : closedAnnularShell alpha beta = closedBall (0:Space) beta ∩ {x | alpha ≤ ‖x‖} := by
    ext x
    simp only [closedAnnularShell,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
    exact and_comm
  rw [he]
  exact (isCompact_closedBall (0:Space) beta).inter_right (isClosed_le continuous_const continuous_norm)

lemma exists_annularCellStencil {alpha : ℝ} (ha : 0 < alpha) (beta : ℝ) :
    ∃ T : Finset Space, (∀ v ∈ T, alpha ≤ ‖v‖ ∧ ‖v‖ ≤ beta) ∧
      ∀ x : Space, alpha ≤ ‖x‖ → ‖x‖ ≤ beta → ∃ v ∈ T, ‖x-v‖ < localCellRadius v := by
  classical
  let S := closedAnnularShell alpha beta
  have hc : S ⊆ ⋃ v : S, ball (v:Space) (localCellRadius v) := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hx.1)
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa using localCellRadius_pos hx0⟩
  obtain ⟨t,ht⟩ := (closedAnnularShell_compact alpha beta).elim_finite_subcover
    (fun v : S => ball (v:Space) (localCellRadius v)) (fun _ => isOpen_ball) hc
  refine ⟨t.image (fun v : S => (v:Space)),?_,?_⟩
  · intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  · intro x hx hxb
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp (ht (show x ∈ S from ⟨hx,hxb⟩))
    exact ⟨v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,mem_ball_iff_norm.mp hxv⟩

lemma localCellRadius_smul {u : ℝ} (hu : 0 ≤ u) (v : Space) :
    localCellRadius (u • v) = u*localCellRadius v := by
  simp only [localCellRadius,norm_smul,Real.norm_of_nonneg hu]
  ring

lemma annularCell_scaled_cover {alpha beta u : ℝ} (hu : 0 < u)
    (T : Finset Space)
    (hC : ∀ x : Space, alpha ≤ ‖x‖ → ‖x‖ ≤ beta → ∃ v ∈ T, ‖x-v‖ < localCellRadius v)
    {x : Space} (hx : alpha*u ≤ ‖x‖) (hxb : ‖x‖ ≤ beta*u) :
    ∃ v ∈ T.image (fun v => u • v), ‖x-v‖ < localCellRadius v := by
  have hnorm : ‖u⁻¹ • x‖ = ‖x‖/u := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]
    ring
  have hal : alpha ≤ ‖u⁻¹ • x‖ := by rw [hnorm]; exact (le_div_iff₀ hu).mpr hx
  have hbe : ‖u⁻¹ • x‖ ≤ beta := by rw [hnorm]; exact (div_le_iff₀ hu).mpr hxb
  obtain ⟨v,hv,hxv⟩ := hC (u⁻¹ • x) hal hbe
  refine ⟨u • v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,?_⟩
  have hid : x-u • v = u • (u⁻¹ • x-v) := by rw [smul_sub,smul_smul,mul_inv_cancel₀ hu.ne',one_smul]
  rw [hid,norm_smul,Real.norm_of_nonneg hu.le,localCellRadius_smul hu.le]
  exact mul_lt_mul_of_pos_left hxv hu

lemma rawAnnularCount_le_cover {N : ℕ} (x : Configuration N) (a b : ℝ)
    (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, a ≤ ‖z‖ → ‖z‖ ≤ b → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawAnnularCount a b x ≤ ∑ v ∈ T, rawBallCount v (r v) x := by
  classical
  unfold rawAnnularCount rawBallCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : a ≤ ‖x i‖ ∧ ‖x i‖ ≤ b
  · rw [ite_eq_left hx]
    obtain ⟨v,hv,hiv⟩ := hcover (x i) hx.1 hx.2
    have hh := Finset.single_le_sum (f := fun w => if ‖x i-w‖ < r w then (1:ℝ) else 0)
      (fun _ _ => by split_ifs <;> norm_num) hv
    simpa only [ite_eq_left hiv] using hh
  · rw [ite_eq_right hx]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

 def rawAnnularMoment {N : ℕ} (psi : FormVector N) (a b : ℝ) : ℝ :=
    rawFormPair psi (fun x => rawAnnularCount a b x^2)
lemma rawAnnularMoment_nonneg {N : ℕ} (psi : FormVector N) (a b : ℝ) : 0 ≤ rawAnnularMoment psi a b := by
  unfold rawAnnularMoment rawFormPair
  positivity

lemma rawAnnularMoment_le_cover {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    (a b : ℝ) (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, a ≤ ‖z‖ → ‖z‖ ≤ b → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawAnnularMoment psi a b ≤ (T.card:ℝ)*∑ v ∈ T, rawCountMoment psi v (r v) := by
  classical
  have hb (z : Space) (q : ℝ) (s : Spins N) :
      Integrable (fun x => rawBallCount z q x^2*‖psi.value s x‖^2) :=
    rawFormPair_integrable hpsi ((rawBallCount_measurable z q).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s
  have ha (s : Spins N) : Integrable (fun x => rawAnnularCount a b x^2*‖psi.value s x‖^2) :=
    rawFormPair_integrable hpsi ((rawAnnularCount_measurable a b).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le _ _ _)) s
  have hpoint (x : Configuration N) : rawAnnularCount a b x^2 ≤
      (T.card:ℝ)*∑ v ∈ T, rawBallCount v (r v) x^2 := by
    calc _ ≤ (∑ v ∈ T, rawBallCount v (r v) x)^2 :=
           pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le_cover x a b T r hcover) 2
         _ ≤ _ := sq_sum_le_card_mul_sum_sq
  unfold rawAnnularMoment rawCountMoment rawFormPair
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ ∫ x, (T.card:ℝ)*(∑ v ∈ T, rawBallCount v (r v) x^2)*‖psi.value s x‖^2 := by
      apply integral_mono (ha s)
      · simp only [mul_assoc,Finset.sum_mul]
        exact (integrable_finsetSum _ (fun v _ => hb v (r v) s)).const_mul _
      · intro x
        exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
    _ = _ := by
      simp only [mul_assoc,Finset.sum_mul,integral_const_mul]
      rw [integral_finsetSum _ (fun v _ => hb v (r v) s)]

end Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric

def annularOffsetMass (D u : ℝ) : ℝ := max (1/u^3) 1+Real.sqrt (D*u)
lemma annularOffsetMass_one_le (D u : ℝ) : 1 ≤ annularOffsetMass D u := by
  unfold annularOffsetMass
  linarith [le_max_right (1/u^3) 1,Real.sqrt_nonneg (D*u)]

def annularCellScaleConstant (alpha beta : ℝ) : ℝ :=
    max ((100000/alpha)^3) 1+Real.sqrt (beta/100000)
lemma annularCellScaleConstant_one_le (alpha beta : ℝ) : 1 ≤ annularCellScaleConstant alpha beta := by
  unfold annularCellScaleConstant
  linarith [le_max_right ((100000/alpha)^3) 1,Real.sqrt_nonneg (beta/100000)]

lemma localOffsetMass_annular_bound {alpha beta u D : ℝ} (ha : 0 < alpha) (hu : 0 < u)
    (hD : 0 ≤ D) {v : Space} (hv : alpha ≤ ‖v‖) (hvb : ‖v‖ ≤ beta) :
    localOffsetMass D (u • v) ≤ annularCellScaleConstant alpha beta*annularOffsetMass D u := by
  let a := localCellRadius (u • v)
  let c := (100000/alpha)^3
  let K := max c 1
  let Q := max (1/u^3) 1
  let k := Real.sqrt (beta/100000)
  have hb : 0 < beta := lt_of_lt_of_le (ha.trans_le hv) hvb
  have had : u*(alpha/100000) ≤ a := by
    dsimp [a]
    rw [localCellRadius_smul hu.le]
    unfold localCellRadius
    gcongr
  have hadp : 0 < u*(alpha/100000) := by positivity
  have hap : 0 < a := hadp.trans_le had
  have hab : a ≤ (beta/100000)*u := by
    dsimp [a]
    rw [localCellRadius_smul hu.le]
    unfold localCellRadius
    nlinarith [mul_le_mul_of_nonneg_left hvb hu.le]
  have hinv : 1/a^3 ≤ c*(1/u^3) := by
    calc _ ≤ 1/(u*(alpha/100000))^3 :=
          one_div_le_one_div_of_le (pow_pos hadp 3) (pow_le_pow_left₀ hadp.le had 3)
         _ = _ := by dsimp [c]; field_simp
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hmax : max (1/a^3) 1 ≤ K*Q := by
    apply max_le
    · exact hinv.trans (mul_le_mul (le_max_left _ _) (le_max_left _ _) (by positivity) hK0)
    · exact (one_le_mul_of_one_le_of_one_le hK hQ)
  have hroot : Real.sqrt (D*a) ≤ k*Real.sqrt (D*u) := by
    have hh : D*a ≤ (beta/100000)*(D*u) := by nlinarith [mul_le_mul_of_nonneg_left hab hD]
    calc _ ≤ Real.sqrt ((beta/100000)*(D*u)) := Real.sqrt_le_sqrt hh
         _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ beta/100000)]
  have hcross1 : 0 ≤ K*Real.sqrt (D*u) := mul_nonneg hK0 (Real.sqrt_nonneg _)
  have hcross2 : 0 ≤ k*Q := mul_nonneg (Real.sqrt_nonneg _) hQ0
  change max (1/a^3) 1+Real.sqrt (D*a) ≤ (K+k)*(Q+Real.sqrt (D*u))
  nlinarith only [hmax,hroot,hcross1,hcross2]

end CoulombAtom

end

end OAI
