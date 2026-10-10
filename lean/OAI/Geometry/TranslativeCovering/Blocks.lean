import OAI.Geometry.TranslativeCovering.BlockWeightMeasure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace Blocks
universe u₁ u₂
open Finset MeasureTheory BlockGeometry BlockSets
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

lemma first_budget_point {lam : ℝ} (hpos : 0 < lam) (hsmall : lam ≤ 1/2) :
    Real.log (1+lam⁻¹) ≤ 2*(-Real.log lam) := by
  have hq : Real.log 2 ≤ -Real.log lam := by
    have hh := Real.log_le_log hpos hsmall
    rw [Real.log_div one_ne_zero (by norm_num),Real.log_one] at hh
    linarith
  have hi : 1 ≤ lam⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hpos]
    linarith
  have hp : 0 < 1+lam⁻¹ := by positivity
  have hh := Real.log_le_log hp (show 1+lam⁻¹ ≤ 2*lam⁻¹ by linarith)
  rw [Real.log_mul (by norm_num) (inv_ne_zero hpos.ne'),Real.log_inv] at hh
  linarith

lemma loss_bound [Fintype I] {L B u : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hu : 1 ≤ u)
    (hcard : (Fintype.card I:ℝ) ≤ Real.exp (2*u)) (d : I → I → ℝ)
    (S : Finset I) (hS : S.Nonempty) (hr : radius d S ≤ B*u) :
    loss L d S ≤ (L*(B+3))*u := by
  have hm : 0 < (S.card:ℝ) := by exact_mod_cast card_pos.mpr hS
  have hsize : (S.card:ℝ) ≤ Fintype.card I := by exact_mod_cast S.card_le_univ
  have hsc : (S.card:ℝ) ≤ Real.exp (2*u) := hsize.trans hcard
  have hslog := (Real.log_le_iff_le_exp hm).mpr hsc
  unfold loss
  split_ifs
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hr hL, mul_le_mul_of_nonneg_left hslog hL,
      mul_le_mul_of_nonneg_left hu hL]

lemma anchors [Nonempty I] [Fintype I] [DecidableEq I] (c : I → ℝ)
    (P : Finpartition (univ : Finset I)) :
    ∃ a : Finset I → I, ∀ S ∈ P.parts, a S ∈ S ∧ ∀ i ∈ S, c (a S) ≤ c i := by
  classical
  have hex (S : Finset I) : ∃ i : I, S ∈ P.parts → i ∈ S ∧ ∀ j ∈ S, c i ≤ c j := by
    by_cases hS : S ∈ P.parts
    · obtain ⟨i,hi,hmin⟩ := S.exists_min_image c (P.nonempty_of_mem_parts hS)
      exact ⟨i,fun _ => ⟨hi,hmin⟩⟩
    · exact ⟨Classical.arbitrary I, fun h => (hS h).elim⟩
  choose a ha using hex
  exact ⟨a,ha⟩

noncomputable def weight (μ : Measure Ω) (E F : Set Ω) : ℝ :=
  μ.real (E ∩ F)/Real.sqrt (μ.real E*(1+μ.real E)*μ.real F*(1+μ.real F))

theorem block_estimates {L C0 c0 : ℝ} (hL : 1 ≤ L) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) :
    ∃ B K C : ℝ, 0 < B ∧ 0 < K ∧ 0 < C ∧
    ∀ (Ω : Type u₁) (I : Type u₂) [MeasurableSpace Ω] [StandardBorelSpace Ω]
      [Fintype I] [Nonempty I] [DecidableEq I] (μ : Measure Ω)
      [IsFiniteMeasure μ] [NullSingletonClass μ],
    ∀ (u : ℝ), 1 ≤ u → (Fintype.card I:ℝ) ≤ Real.exp (2*u) →
    ∀ (caps : I → Set Ω), (∀ i, MeasurableSet (caps i)) → (∀ i, 0 < μ.real (caps i)) →
    ∀ (d : I → I → ℝ), (∀ i j, 0 ≤ d i j) → (∀ i, d i i = 0) →
      (∀ i j, d i j = d j i) → (∀ i j k, d i k ≤ d i j+d j k) →
    (∀ i j, μ.real (caps i ∩ caps j)/Real.sqrt (clipped μ caps i*clipped μ caps j) ≤
      C0*Real.exp (-c0*d i j^2)) →
    (∀ S : Finset I, S.Nonempty → radius d S ≤ B*u →
      ∀ a ∈ S, (∀ i ∈ S, μ.real (caps a) ≤ μ.real (caps i)) →
      Real.exp (-L*(1+radius d S+Real.log S.card))*clipped μ caps a ≤ μ.real (common caps S)) →
    ∃ (P : Finpartition (univ : Finset I)) (a : Finset I → I) (E : Finset I → Set Ω),
      (∀ S ∈ P.parts, a S ∈ S ∧ (∀ i ∈ S, μ.real (caps (a S)) ≤ μ.real (caps i)) ∧
        MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        Real.exp (-K*u)*clipped μ caps (a S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      (∑ S ∈ P.parts, -Real.log (μ.real (E S))) ≤ ∑ i, cost μ caps i+(Fintype.card I:ℝ)/10 ∧
      (∑ S ∈ P.parts, Real.log (1+(μ.real (E S))⁻¹)) ≤ C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) ∧
      (∑ S ∈ P.parts, Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T))) ≤
        C*((Fintype.card I:ℝ)+∑ i,cost μ caps i) := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hζ : (0:ℝ) < 1/10 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := (Real.log C0+2)/c0
  let B := (8*A+16/L)*(2+3/Real.log 2)
  have hAp : 0 < A := div_pos (by linarith [Real.log_nonneg hC0]) hc0
  have hBp : 0 < B := by dsimp [B]; positivity
  obtain ⟨N0,hN02,hN0log⟩ := BlockCount.log_absorption hLp hζ
  let Cbin := (N0:ℝ)+(2*L/(1/10))*(1+8*A+16/L)
  let Crow := max (2*Cbin+(1+4*Cbin)/Real.log 2) 3
  let C := max 2 Crow
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨B,L*(B+3),C,hBp,by positivity,hCp,?_⟩
  intro Ω I _ _ _ _ _ μ _ _ u hu hcard caps hmeas hpos d hn hd hs htri haff hlens
  obtain ⟨P,hprops,hterm⟩ := BlockGeometry.exists_terminal (L := L) (R := B*u)
    (mul_nonneg hBp.le (show 0 ≤ u by linarith)) hζ.le d hd
  obtain ⟨a,ha⟩ := anchors (fun i => μ.real (caps i)) P
  obtain ⟨E,hE⟩ := choose_sets μ caps hmeas hpos d P a (fun S hS => (ha S hS).1)
    (fun S hS => (hprops S hS).1) (fun S hS hr =>
      hlens S (P.nonempty_of_mem_parts hS) hr (a S) (ha S hS).1 (ha S hS).2)
  let q := fun S => -Real.log (μ.real (E S))
  have hi (S : Finset I) (hS : S ∈ P.parts) :
      0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2 ∧ q S = cost μ caps (a S)+loss L d S := by
    dsimp only [q,cost]
    rw [(hE S hS).2.2]
    exact intensity_cost (loss_nonneg hLp.le d S) (clipped_pos μ caps hpos _) (min_le_right _ _)
  have hqeq (S : Finset I) (hS : S ∈ P.parts) :
      q S = cost μ caps (a S)+loss L d S := (hi S hS).2.2
  have hqge (S : Finset I) (hS : S ∈ P.parts) : Real.log 2 ≤ q S := by
    rw [hqeq S hS]
    linarith [cost_ge μ caps hpos (a S),loss_nonneg hLp.le d S]
  have hqsum : ∑ S ∈ P.parts,q S ≤ ∑ i,cost μ caps i + (Fintype.card I:ℝ)/10 := by
    simp_rw [sum_congr rfl (fun S hS => hqeq S hS)]
    convert sum_cost μ caps hpos d P a (fun S hS => (ha S hS).1)
      (fun S hS => (hprops S hS).2) using 1
    ring
  have hqtotal : ∑ S ∈ P.parts,q S ≤ (Fintype.card I:ℝ)+∑ i,cost μ caps i := by
    have hm : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
    linarith
  have hrow (S : Finset I) (hS : S ∈ P.parts) :
      Real.log (1+∑ T ∈ P.parts.erase S,weight μ (E S) (E T)) ≤ Crow*q S := by
    apply BlockDimension.uniform_row hLp hζ hC0 hc0 hlog2 hu hcard d hn hd hs htri P
      hterm N0 hN02 hN0log a (fun T hT => (ha T hT).1) q
      (fun T hT => by rw [hqeq T hT]; linarith [cost_ge μ caps hpos (a T)]) S hS (hqge S hS)
    · intro T _; exact div_nonneg measureReal_nonneg (Real.sqrt_nonneg _)
    · intro T hT
      apply (BlockWeightMeasure.measure_trivial μ (hi S hS).1 (hi T (mem_of_mem_erase hT)).1).trans
      exact Real.exp_le_one_iff.mpr (by have := abs_nonneg (q S-q T); linarith)
    · intro T hT
      exact BlockWeightMeasure.measure_trivial μ (hi S hS).1 (hi T (mem_of_mem_erase hT)).1
    · intro T hT
      have hTP := mem_of_mem_erase hT
      have hsub : E S ∩ E T ⊆ caps (a S) ∩ caps (a T) :=
        Set.inter_subset_inter ((hE S hS).2.1.trans (common_subset caps (ha S hS).1))
          ((hE T hTP).2.1.trans (common_subset caps (ha T hTP).1))
      have hinter := measureReal_mono (μ := μ) hsub
      have hbasic : μ.real (E S ∩ E T)/Real.sqrt (clipped μ caps (a S)*clipped μ caps (a T)) ≤
          C0*Real.exp (-c0*d (a S) (a T)^2) :=
        (div_le_div_of_nonneg_right hinter (Real.sqrt_nonneg _)).trans (haff _ _)
      have hh := BlockWeightMeasure.affine_bound (ell := loss L d S) (ell' := loss L d T)
        measureReal_nonneg (clipped_pos μ caps hpos _) (clipped_pos μ caps hpos _) hbasic
      simpa only [weight,(hE S hS).2.2,(hE T hTP).2.2] using hh
  refine ⟨P,a,E,?_,hqsum,?_,?_⟩
  · intro S hS
    refine ⟨(ha S hS).1,(ha S hS).2,(hE S hS).1,(hE S hS).2.1,?_,(hi S hS).1,(hi S hS).2.1⟩
    rw [(hE S hS).2.2]
    apply mul_le_mul_of_nonneg_right _ (clipped_pos μ caps hpos _).le
    apply Real.exp_le_exp.mpr
    have hh := loss_bound hLp.le hBp.le hu hcard d S (P.nonempty_of_mem_parts hS) (hprops S hS).1
    linarith
  · calc
      _ ≤ ∑ S ∈ P.parts,2*q S := sum_le_sum (fun S hS => first_budget_point (hi S hS).1 (hi S hS).2.1)
      _ = 2*∑ S ∈ P.parts,q S := by rw [mul_sum]
      _ ≤ C*∑ S ∈ P.parts,q S := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (sum_nonneg (fun S hS => hlog2.le.trans (hqge S hS)))
      _ ≤ _ := mul_le_mul_of_nonneg_left hqtotal hCp.le
  · calc
      _ ≤ ∑ S ∈ P.parts,Crow*q S := sum_le_sum hrow
      _ = Crow*∑ S ∈ P.parts,q S := by rw [mul_sum]
      _ ≤ C*∑ S ∈ P.parts,q S := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (sum_nonneg (fun S hS => hlog2.le.trans (hqge S hS)))
      _ ≤ _ := mul_le_mul_of_nonneg_left hqtotal hCp.le

end Blocks

end OAI
