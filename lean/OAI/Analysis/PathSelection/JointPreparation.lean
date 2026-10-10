import Mathlib
import OAI.Analysis.PathSelection.ContourPreparation
import OAI.Analysis.PathSelection.ParameterIntegrals

namespace OAI

/-! Jointly analytic fixed-contour preparation and division. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open PathSelection.Preparation PathSelection.ParameterPreparation
namespace PathSelection.JointPreparation

lemma deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {a : E} {z : ℂ} (hF : AnalyticAt ℂ F (a,z)) :
    deriv (fun w => F (a,w)) z = fderiv ℂ F (a,z) (0,1) := by
  have hi : HasDerivAt (fun w : ℂ => (a,w)) (0,1) z :=
    (hasDerivAt_const z a).prodMk (hasDerivAt_id z)
  exact (hF.differentiableAt.hasFDerivAt.comp_hasDerivAt z hi).deriv

lemma analyticOnNhd_deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {S : Set (E × ℂ)} (hF : AnalyticOnNhd ℂ F S) :
    AnalyticOnNhd ℂ (fun p => deriv (fun w => F (p.1,w)) p.2) S := by
  intro p hp
  have hh := ((ContinuousLinearMap.apply ℂ ℂ ((0,1) : E × ℂ)).analyticAt _).comp (hF p hp).fderiv
  apply hh.congr
  filter_upwards [(hF p hp).eventually_analyticAt] with q hq
  exact (deriv_slice hq).symm

lemma analyticOnNhd_contourPowerSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : E × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r))
    (hnz : ∀ p∈U ×ˢ sphere (0:ℂ) r, F p≠0) (l : ℕ) :
    AnalyticOnNhd ℂ (fun a => contourPowerSum (fun z => F (a,z)) r l) U := by
  have hd := analyticOnNhd_deriv_slice hF
  have hi := analyticOnNhd_circleIntegral hU hr
    ((analyticOnNhd_snd.pow l).mul hd |>.div hF hnz)
  exact analyticOnNhd_const.mul hi

lemma analyticAt_newtonEsymm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {s : E → ℕ → ℂ} {a : E}
    (hs : ∀ l, AnalyticAt ℂ (fun x => s x l) a) (n : ℕ) :
    AnalyticAt ℂ (fun x => newtonEsymm (s x) n) a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [show (fun x => newtonEsymm (s x) n) =
      (fun x => if n=0 then 1 else (n:ℂ)⁻¹ * (-1)^(n+1) *
        ∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1<n),
          if h : t.1<n then (-1)^t.1 * newtonEsymm (s x) t.1 * s x t.2 else 0) by
      funext x; rw [newtonEsymm]]
    split_ifs with hn
    · exact analyticAt_const
    · apply AnalyticAt.mul analyticAt_const
      apply Finset.analyticAt_fun_sum
      intro t ht
      split_ifs with ht'
      · exact (analyticAt_const.mul (ih t.1 ht')).mul (hs t.2)
      · exact analyticAt_const

lemma analyticOnNhd_preparation_eval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : E × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r))
    (hnz : ∀ p∈U ×ˢ sphere (0:ℂ) r, F p≠0) (d : ℕ) :
    AnalyticOnNhd ℂ (fun p : E × ℂ =>
      (preparationPolynomial (fun z => F (p.1,z)) r d).eval p.2) (U ×ˢ univ) := by
  intro p hp
  have hpoly : (fun q : E × ℂ => (preparationPolynomial (fun z => F (q.1,z)) r d).eval q.2) =
    fun q => ∑ k ∈ Finset.range (d+1),
      (-1)^(d-k) * newtonEsymm (contourPowerSum (fun z => F (q.1,z)) r) (d-k) * q.2^k := by
    funext q
    simp [preparationPolynomial,Polynomial.eval_finsetSum]
  rw [hpoly]
  apply Finset.analyticAt_fun_sum
  intro k hk
  apply AnalyticAt.mul _ (analyticAt_snd.pow k)
  apply AnalyticAt.mul analyticAt_const
  exact (analyticAt_newtonEsymm (fun l =>
    analyticOnNhd_contourPowerSum hU hr hF hnz l p.1 hp.1) (d-k)).comp analyticAt_fst

lemma analyticOnNhd_divisionQuotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {G : E × ℂ → ℂ} {P : E → ℂ[X]} {r : ℝ}
    (hU : IsOpen U) (hr : 0<r) (hG : AnalyticOnNhd ℂ G (U ×ˢ sphere 0 r))
    (hP : AnalyticOnNhd ℂ (fun p : E × ℂ => (P p.1).eval p.2) (U ×ˢ sphere 0 r))
    (hnz : ∀ a∈U, ∀ z∈sphere (0:ℂ) r, (P a).eval z≠0) :
    AnalyticOnNhd ℂ (fun p : E × ℂ => divisionQuotient (fun z => G (p.1,z)) (P p.1) r p.2)
      (U ×ˢ ball 0 r) := by
  have hi : AnalyticOnNhd ℂ
      (fun q : (E × ℂ) × ℂ => G (q.1.1,q.2) /
        ((P q.1.1).eval q.2 * (q.2-q.1.2))) ((U ×ˢ ball 0 r) ×ˢ sphere 0 r) := by
    intro q hq
    have hc : AnalyticAt ℂ (fun x : (E × ℂ) × ℂ => (x.1.1,x.2)) q :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    have hn : q.2-q.1.2≠0 := by
      intro he
      have hz := sub_eq_zero.mp he
      have hball := hq.1.2
      rw [← hz] at hball
      exact (ne_of_lt (mem_ball_zero_iff.mp hball)) (mem_sphere_zero_iff_norm.mp hq.2)
    exact ((hG (q.1.1,q.2) ⟨hq.1.1,hq.2⟩).comp (f := fun x : (E × ℂ) × ℂ => (x.1.1,x.2)) hc).div
      (((hP (q.1.1,q.2) ⟨hq.1.1,hq.2⟩).comp (f := fun x : (E × ℂ) × ℂ => (x.1.1,x.2)) hc).mul
        (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)))
      (mul_ne_zero (hnz q.1.1 hq.1.1 q.2 hq.2) hn)
  exact analyticOnNhd_const.mul
    (analyticOnNhd_circleIntegral (hU.prod isOpen_ball) hr.le hi)

lemma analyticOnNhd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {U : Set E} {S : Set ℂ}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ S)) {a : E} (ha : a∈U) :
    AnalyticOnNhd ℂ (fun z => F (a,z)) S := by
  intro z hz
  exact (hF (a,z) ⟨ha,hz⟩).comp (analyticAt_const.prod analyticAt_id)

lemma zero_count_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {U : Set E} {r : ℝ} (hU : IsOpen U) (hcU : IsPreconnected U)
    (hr : 0<r) (hF : AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r))
    (hnz : ∀ p∈U ×ˢ sphere (0:ℂ) r, F p≠0)
    {a b : E} (ha : a∈U) (hb : b∈U) :
    contourPowerSum (fun z => F (a,z)) r 0 = contourPowerSum (fun z => F (b,z)) r 0 := by
  have hi := (analyticOnNhd_contourPowerSum hU hr.le
    (hF.mono (prod_mono Subset.rfl sphere_subset_closedBall)) hnz 0).continuousOn
  have hc : (range (fun n : ℕ => (n:ℂ))).Countable := countable_range _
  have hs : (fun a => contourPowerSum (fun z => F (a,z)) r 0) '' U ⊆
      range (fun n : ℕ => (n:ℂ)) := by
    rintro _ ⟨a,ha,rfl⟩
    exact contour_zero_count_nat hr (analyticOnNhd_slice hF ha) (fun z hz => hnz (a,z) ⟨ha,hz⟩)
  exact hc.isTotallyDisconnected _ hs (hcU.image _ hi)
    (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

 

theorem joint_fixed_contour_preparation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : E × ℂ → ℂ} {U : Set E} {r : ℝ} {a₀ : E} {d : ℕ}
    (hU : IsOpen U) (hcU : IsPreconnected U) (ha₀ : a₀∈U) (hr : 0<r)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r))
    (hnz : ∀ p∈U ×ˢ sphere (0:ℂ) r, F p≠0)
    (hcount : contourPowerSum (fun z => F (a₀,z)) r 0 = (d:ℂ)) :
    let W := fun a => preparationPolynomial (fun z => F (a,z)) r d
    let u := fun p : E × ℂ => divisionQuotient (fun z => F (p.1,z)) (W p.1) r p.2
    (∀ a∈U, (W a).Monic ∧ (W a).natDegree=d ∧
      ∀ z, (W a).eval z=0 → z∈ball 0 r) ∧
    AnalyticOnNhd ℂ (fun p : E × ℂ => (W p.1).eval p.2) (U ×ˢ univ) ∧
    AnalyticOnNhd ℂ u (U ×ˢ ball 0 r) ∧
    (∀ p∈U ×ˢ ball (0:ℂ) r, u p≠0) ∧
    EqOn F (fun p => (W p.1).eval p.2 * u p) (U ×ˢ ball 0 r) := by
  dsimp only
  let W := fun a => preparationPolynomial (fun z => F (a,z)) r d
  have hcount' (a : E) (ha : a∈U) : contourPowerSum (fun z => F (a,z)) r 0 = (d:ℂ) :=
    (zero_count_constant hU hcU hr hF hnz ha ha₀).trans hcount
  have hp (a : E) (ha : a∈U) := fixed_contour_preparation_of_count hr
    (analyticOnNhd_slice hF ha) (fun z hz => hnz (a,z) ⟨ha,hz⟩) (hcount' a ha)
  have hroot' : ∀ a∈U, ∀ z∈sphere (0:ℂ) r, (W a).eval z ≠0 := by
    intro a ha z hz he
    exact (ne_of_lt (mem_ball_zero_iff.mp ((hp a ha).2.2.1 z he)))
      (mem_sphere_zero_iff_norm.mp hz)
  have hW := analyticOnNhd_preparation_eval hU hr.le
    (hF.mono (prod_mono Subset.rfl sphere_subset_closedBall)) hnz d
  refine ⟨fun a ha => ⟨(hp a ha).1,(hp a ha).2.1,(hp a ha).2.2.1⟩,hW,?_,?_,?_⟩
  · exact analyticOnNhd_divisionQuotient (P := W) (G := F) hU hr
      (hF.mono (prod_mono Subset.rfl sphere_subset_closedBall))
      (hW.mono (prod_mono Subset.rfl (subset_univ _))) hroot'
  · intro p hp'
    exact (hp p.1 hp'.1).2.2.2.2.1 p.2 hp'.2
  · intro p hp'
    exact (hp p.1 hp'.1).2.2.2.2.2 hp'.2

lemma analyticOnNhd_preparation_coeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : E × ℂ → ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0≤r) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r))
    (hnz : ∀ p∈U ×ˢ sphere (0:ℂ) r, F p≠0) (d n : ℕ) :
    AnalyticOnNhd ℂ (fun a => (preparationPolynomial (fun z => F (a,z)) r d).coeff n) U := by
  classical
  simp only [preparationPolynomial,finsetSum_coeff,coeff_C_mul_X_pow]
  intro a ha
  apply Finset.analyticAt_fun_sum
  intro k hk
  split_ifs with hnk
  · exact analyticAt_const.mul (analyticAt_newtonEsymm
      (fun l => analyticOnNhd_contourPowerSum hU hr hF hnz l a ha) (d-k))
  · exact analyticAt_const

lemma analyticOnNhd_divisionRemainder_coeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {G : E × ℂ → ℂ} {P : E → ℂ[X]} {r : ℝ} {d : ℕ}
    (hU : IsOpen U) (hr : 0≤r) (hG : AnalyticOnNhd ℂ G (U ×ˢ sphere 0 r))
    (hP : AnalyticOnNhd ℂ (fun p : E × ℂ => (P p.1).eval p.2) (U ×ˢ sphere 0 r))
    (hPc : ∀ n, AnalyticOnNhd ℂ (fun a => (P a).coeff n) U)
    (hdeg : ∀ a∈U, (P a).natDegree=d)
    (hnz : ∀ a∈U, ∀ z∈sphere (0:ℂ) r, (P a).eval z≠0) (m : ℕ) :
    AnalyticOnNhd ℂ (fun a => (divisionRemainder (fun z => G (a,z)) (P a) r).coeff m) U := by
  classical
  let c := fun n k a => (2*Real.pi*Complex.I)⁻¹ * ∮ w in C(0,r),
    G (a,w)/(P a).eval w*((P a).coeff n*w^(n-1-k))
  have hc (n k : ℕ) : AnalyticOnNhd ℂ (c n k) U := by
    apply analyticOnNhd_const.mul
    apply analyticOnNhd_circleIntegral (F := fun p : E × ℂ =>
      G p / (P p.1).eval p.2 * ((P p.1).coeff n * p.2^(n-1-k))) hU hr
    intro p hp
    exact ((hG p hp).div (hP p hp) (hnz p.1 hp.1 p.2 hp.2)).mul
      (((hPc n p.1 hp.1).comp (f := fun p : E × ℂ => p.1) analyticAt_fst).mul
        (analyticAt_snd.pow _))
  have hs : AnalyticOnNhd ℂ
      (fun a => ∑ n ∈ Finset.range (d+1), ∑ k ∈ Finset.range n,
        if m=k then c n k a else 0) U := by
    intro a ha
    apply Finset.analyticAt_fun_sum
    intro n hn
    apply Finset.analyticAt_fun_sum
    intro k hk
    split_ifs
    · exact hc n k a ha
    · exact analyticAt_const
  intro a ha
  apply (hs a ha).congr
  filter_upwards [hU.mem_nhds ha] with x hx
  simp only [divisionRemainder,finsetSum_coeff,coeff_C_mul_X_pow,hdeg x hx]
  rfl

 

theorem joint_fixed_contour_division {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {G : E × ℂ → ℂ} {P : E → ℂ[X]} {r : ℝ} {d : ℕ}
    (hU : IsOpen U) (hr : 0<r) (hG : AnalyticOnNhd ℂ G (U ×ˢ closedBall 0 r))
    (hP : AnalyticOnNhd ℂ (fun p : E × ℂ => (P p.1).eval p.2) (U ×ˢ sphere 0 r))
    (hPc : ∀ n, AnalyticOnNhd ℂ (fun a => (P a).coeff n) U)
    (hdeg : ∀ a∈U, (P a).natDegree=d)
    (hnz : ∀ a∈U, ∀ z∈sphere (0:ℂ) r, (P a).eval z≠0) :
    let Q := fun p : E × ℂ => divisionQuotient (fun z => G (p.1,z)) (P p.1) r p.2
    let R := fun a => divisionRemainder (fun z => G (a,z)) (P a) r
    AnalyticOnNhd ℂ Q (U ×ˢ ball 0 r) ∧
    (∀ n, AnalyticOnNhd ℂ (fun a => (R a).coeff n) U) ∧
    (∀ a∈U, (R a).degree < d) ∧
    EqOn G (fun p => (P p.1).eval p.2 * Q p + (R p.1).eval p.2) (U ×ˢ ball 0 r) := by
  dsimp only
  have hG' := hG.mono (prod_mono Subset.rfl sphere_subset_closedBall)
  refine ⟨analyticOnNhd_divisionQuotient hU hr hG' hP hnz,
    analyticOnNhd_divisionRemainder_coeff hU hr.le hG' hP hPc hdeg hnz,?_,?_⟩
  · intro a ha
    rw [← hdeg a ha]
    exact divisionRemainder_degree _ _ _
  · intro p hp
    exact (fixed_disc_division hr (analyticOnNhd_slice hG hp.1) (hnz p.1 hp.1)).2.2 hp.2

end PathSelection.JointPreparation
end

end OAI
