import Mathlib
import OAI.Analysis.PathSelection.CompactProfiles
import OAI.Analysis.PathSelection.ContourDivision

namespace OAI

/-! Constant root counts and joint preparation of fixed root clusters. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace DegeneratingTrees
open Set Metric Filter Topology Complex

theorem contour_rootCount_constant {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {U : Set A} (hU : IsOpen U) (hUc : IsPreconnected U)
    {r : ℝ} (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r))
    (hn : ∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, F (q,z) ≠ 0)
    {q₀ : A} (hq₀ : q₀ ∈ U) :
    ∀ q ∈ U, contourMoment (fun y => F (q,y)) r 0 =
      contourMoment (fun y => F (q₀,y)) r 0 := by
  let M : A → ℂ := fun q => contourMoment (fun y => F (q,y)) r 0
  have hM : AnalyticOnNhd ℂ M U := analytic_contourMoment_general hU hr
    (hF.mono (fun x hx => ⟨hx.1,sphere_subset_closedBall hx.2⟩)) hn 0
  have hnat (q : A) (hq : q ∈ U) : ∃ n : ℕ, M q = (n : ℂ) := by
    have hf : AnalyticOnNhd ℂ (fun y => F (q,y)) (closedBall 0 r) := by
      intro y hy
      exact (hF (q,y) ⟨hq,hy⟩).comp (analyticAt_const.prod analyticAt_id)
    obtain ⟨n,_,he,_⟩ := contour_fiber_factorization hr hf (hn q hq)
    exact ⟨n,he⟩
  obtain ⟨n,hn0⟩ := hnat q₀ hq₀
  have hev : M =ᶠ[𝓝 q₀] fun _ => M q₀ := by
    have hd := (hM q₀ hq₀).continuousAt.preimage_mem_nhds
      (ball_mem_nhds (M q₀) (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hU.mem_nhds hq₀,hd] with q hq hdq
    obtain ⟨m,hm⟩ := hnat q hq
    have he : m = n := by
      have hdist : dist (m : ℂ) (n : ℂ) < 1 := by simpa [hm,hn0] using hdq
      have hcast : ((m : ℂ) - n) = (((m : ℤ) - n : ℤ) : ℂ) := by push_cast; rfl
      rw [dist_eq_norm,hcast,Complex.norm_intCast] at hdist
      have hint : |((m : ℤ) - n : ℤ)| < 1 := by exact_mod_cast hdist
      have hzero := Int.abs_lt_one_iff.mp hint
      omega
    rw [hm,hn0,he]
  exact hM.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hq₀ hev

 

theorem contour_rootCount_eq_of_close {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hn : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0)
    (hc : ∀ z ∈ sphere (0 : ℂ) r, ‖g z-f z‖ < ‖f z‖ / 2) :
    contourMoment g r 0 = contourMoment f r 0 := by
  let H : ℂ × ℂ → ℂ := fun x => f x.2 + x.1 * (g x.2-f x.2)
  have hH : AnalyticOnNhd ℂ H (ball 0 2 ×ˢ closedBall 0 r) := by
    intro x hx
    have hfa := (hf x.2 hx.2).comp analyticAt_snd
    have hga := (hg x.2 hx.2).comp analyticAt_snd
    exact hfa.add (analyticAt_fst.mul (hga.sub hfa))
  have hHn : ∀ t ∈ ball (0 : ℂ) 2, ∀ z ∈ sphere (0 : ℂ) r, H (t,z) ≠ 0 := by
    intro t ht z hz
    have ht' : ‖t‖ < 2 := by simpa using ht
    have hd : ‖t * (g z-f z)‖ < ‖f z‖ := by
      rw [norm_mul]
      calc
        ‖t‖ * ‖g z-f z‖ ≤ ‖t‖ * (‖f z‖ / 2) :=
          mul_le_mul_of_nonneg_left (hc z hz).le (norm_nonneg _)
        _ < 2 * (‖f z‖ / 2) :=
          mul_lt_mul_of_pos_right ht' (half_pos (norm_pos_iff.mpr (hn z hz)))
        _ = ‖f z‖ := by ring
    intro he
    have he' : f z = -(t * (g z-f z)) := eq_neg_of_add_eq_zero_left he
    have heN : ‖f z‖ = ‖t * (g z-f z)‖ := by
      calc
        ‖f z‖ = ‖-(t * (g z-f z))‖ := congrArg norm he'
        _ = _ := norm_neg _
    exact (lt_irrefl _ (hd.trans_eq heN))
  have he := contour_rootCount_constant isOpen_ball (convex_ball (0 : ℂ) 2).isPreconnected
    hr hH hHn (show (0 : ℂ) ∈ ball 0 2 by simp) 1 (by simp)
  simpa [H] using he

end DegeneratingTrees

namespace DegeneratingTrees
open Set Metric Filter Topology Complex

 

theorem fixed_contour_preparation_general {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {U : Set A} (hU : IsOpen U) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (hFA : AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r))
    (hnB : ∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, F (q,z) ≠ 0)
    (hm0 : ∀ q ∈ U, contourMoment (fun y => F (q,y)) r 0 = (d : ℂ)) :
    ∃ g : A × ℂ → ℂ,
      AnalyticOnNhd ℂ g (U ×ˢ ball 0 r) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r, g (q,y) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q,y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q,y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q,y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r,
        F (q,y) = (contourPolynomial (fun y => F (q,y)) r d).eval y * g (q,y)) := by
  classical
  let h : C(sphere (0 : ℂ) r,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  let φ := compactProfile h F
  have hφ : AnalyticOnNhd ℂ φ U := analytic_compactProfile h hU
    (fun q hq t => hFA _ ⟨hq,sphere_subset_closedBall t.property⟩)
  have hφe (q : A) (hq : q ∈ U) (t : sphere (0 : ℂ) r) : φ q t = F (q,t) := by
    apply compactProfile_apply
    exact hFA.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨hq,sphere_subset_closedBall t.property⟩)
  have hfB (q : A) (hq : q ∈ U) : AnalyticOnNhd ℂ (fun y => F (q,y)) (closedBall 0 r) := by
    intro y hy
    exact (hFA (q,y) ⟨hq,hy⟩).comp (analyticAt_const.prod analyticAt_id)
  have hm (k : ℕ) : AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q,y)) r k) U :=
    analytic_contourMoment_general hU hr
      (hFA.mono (fun x hx => ⟨hx.1,sphere_subset_closedBall hx.2⟩)) hnB k
  have hfac (q : A) (hq : q ∈ U) :
      ∃ g : ℂ → ℂ, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d ∧
        AnalyticOnNhd ℂ g (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
        EqOn (fun y => F (q, y))
          (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * g y) (closedBall 0 r) := by
    obtain ⟨N, g, hN, hM, hD, hg, hgn, hfg⟩ := contour_fiber_factorization hr (hfB q hq) (hnB q hq)
    have hNd : N = d := by exact_mod_cast hN.symm.trans (hm0 q hq)
    subst N
    exact ⟨g, hM, hD, hg, hgn, hfg⟩
  have hpU (q : A) (hq : q ∈ U) : IsUnit (contourPolynomialProfile F r d q) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro z
    rw [contourPolynomialProfile_apply]
    obtain ⟨g, _, _, _, _, hfg⟩ := hfac q hq
    have he := hfg (sphere_subset_closedBall z.property)
    dsimp only at he
    exact left_ne_zero_of_mul (by rw [← he]; exact hnB q hq z z.property)
  let κ : A → C(sphere (0 : ℂ) r, ℂ) := fun q => φ q * Ring.inverse (contourPolynomialProfile F r d q)
  have hκ : AnalyticOnNhd ℂ κ U := by
    intro q hq
    exact (hφ q hq).mul ((analyticOnNhd_inverse _ (hpU q hq)).comp
      (analytic_contourPolynomialProfile hm d q hq))
  let g : A × ℂ → ℂ := cauchyTransformProfile r hr κ
  have hgFiber (q : A) (hq : q ∈ U) (v : ℂ → ℂ)
      (hv : AnalyticOnNhd ℂ v (closedBall 0 r))
      (hfv : EqOn (fun y => F (q, y))
        (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * v y) (closedBall 0 r))
      (y : ℂ) (hy : y ∈ ball (0 : ℂ) r) : g (q, y) = v y := by
    apply cauchyTransformProfile_eq hr hv _ hy
    intro z
    dsimp only [κ]
    rw [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ (hpU q hq),
      hφe q hq, contourPolynomialProfile_apply]
    have he := hfv (sphere_subset_closedBall z.property)
    dsimp only at he
    rw [he]
    have hn : (contourPolynomial (fun y => F (q, y)) r d).eval (z : ℂ) ≠ 0 := by
      rw [← contourPolynomialProfile_apply]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hpU q hq) z
    field_simp
  refine ⟨g, analytic_cauchyTransformProfile hr hκ, ?_, ?_,
    fun k => analytic_contourPolynomial_coeff hm d k, ?_⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, hvn, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hvn y (ball_subset_closedBall hy)
  · intro q hq
    obtain ⟨_, hM, hD, _⟩ := hfac q hq
    exact ⟨hM, hD⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, _, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hfv (ball_subset_closedBall hy)

end DegeneratingTrees

namespace DegeneratingTrees
open Set Metric Filter Topology Complex

 

theorem fixed_contour_preparation_of_close {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {f : ℂ → ℂ} {U : Set A} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    {d : ℕ} (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hfn : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0)
    (hfm : contourMoment f r 0 = (d : ℂ))
    (hF : AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r))
    (hc : ∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, ‖F (q,z)-f z‖ < ‖f z‖ / 2) :
    ∃ g : A × ℂ → ℂ,
      AnalyticOnNhd ℂ g (U ×ˢ ball 0 r) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r, g (q,y) ≠ 0) ∧
      (∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, F (q,z) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q,y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q,y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q,y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r,
        F (q,y) = (contourPolynomial (fun y => F (q,y)) r d).eval y * g (q,y)) := by
  have hn : ∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, F (q,z) ≠ 0 := by
    intro q hq z hz he
    have ht := hc q hq z hz
    rw [he,zero_sub,norm_neg] at ht
    linarith [norm_nonneg (f z)]
  have hm : ∀ q ∈ U, contourMoment (fun y => F (q,y)) r 0 = (d : ℂ) := by
    intro q hq
    exact (contour_rootCount_eq_of_close (g := fun y => F (q,y)) hr hf (fun z hz =>
      (hF (q,z) ⟨hq,hz⟩).comp (analyticAt_const.prod analyticAt_id)) hfn (hc q hq)).trans hfm
  obtain ⟨g,hg,hgn,hP,hcP,he⟩ := fixed_contour_preparation_general hU hr hF hn hm
  exact ⟨g,hg,hgn,hn,hP,hcP,he⟩

 

theorem prepared_unit_all_orders {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {g : A × ℂ → ℂ} {U : Set A} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (U ×ˢ ball 0 r)) :
    ∀ n, AnalyticOnNhd ℂ (iteratedFDeriv ℂ n g) (U ×ˢ ball 0 r) :=
  fun n => hg.iteratedFDeriv n

end DegeneratingTrees

namespace DegeneratingTrees
open Set Metric Filter Topology Complex
open scoped BigOperators Polynomial

 

theorem contourPolynomial_dvd {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hn : ∀ z ∈ sphere (0 : ℂ) r, P.eval z ≠ 0) {d : ℕ}
    (hd : contourMoment P.eval r 0 = (d : ℂ)) :
    contourPolynomial P.eval r d ∣ P := by
  classical
  have hP0 : P ≠ 0 := by
    intro he
    apply hn (r : ℂ) (by simp [abs_of_pos hr])
    simp [he]
  let s := P.roots.toFinset.filter (fun a => ‖a‖ < r)
  let t := P.roots.toFinset.filter (fun a => ¬ ‖a‖ < r)
  let m : ℂ → ℕ := fun a => P.roots.count a
  let Q : ℂ[X] := ∏ a ∈ s, (Polynomial.X-Polynomial.C a) ^ m a
  let R : ℂ[X] := Polynomial.C P.leadingCoeff *
    ∏ a ∈ t, (Polynomial.X-Polynomial.C a) ^ m a
  have hPQ : P = Q * R := by
    rw [(IsAlgClosed.splits P).eq_prod_roots, Finset.prod_multiset_map_count]
    dsimp only [Q,R,m,s,t]
    rw [← Finset.prod_filter_mul_prod_filter_not (p := fun a : ℂ => ‖a‖ < r)]
    ring
  have hs (a : ℂ) (ha : a ∈ s) : a ∈ ball (0 : ℂ) r := by
    simpa using (Finset.mem_filter.mp ha).2
  have ht (a : ℂ) (ha : a ∈ t) : r < ‖a‖ := by
    have hae : P.eval a = 0 := Polynomial.mem_roots hP0 |>.mp
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp ha).1)
    have hal : r ≤ ‖a‖ := le_of_not_gt (Finset.mem_filter.mp ha).2
    apply lt_of_le_of_ne hal
    intro he
    exact hn a (by simpa [mem_sphere_zero_iff_norm] using he.symm) hae
  have hR : ∀ z ∈ closedBall (0 : ℂ) r, R.eval z ≠ 0 := by
    intro z hz
    simp only [R,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,
      Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X]
    apply mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP0)
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply pow_ne_zero
    intro he
    have hza := sub_eq_zero.mp he
    have hzn : ‖z‖ ≤ r := by simpa using hz
    rw [hza] at hzn
    exact (not_lt_of_ge hzn (ht a ha))
  have hf : AnalyticOnNhd ℂ P.eval (closedBall 0 r) := fun z _ => AnalyticOnNhd.eval_polynomial P z (Set.mem_univ z)
  have hg : AnalyticOnNhd ℂ R.eval (closedBall 0 r) := fun z _ => AnalyticOnNhd.eval_polynomial R z (Set.mem_univ z)
  have heq : EqOn P.eval (fun z => (∏ a ∈ s, (z-a)^m a) * R.eval z) (closedBall 0 r) := by
    intro z hz
    change P.eval z = _
    rw [hPQ,Polynomial.eval_mul]
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  let ι := Σ a : s, Fin (m a)
  let x : ι → ℂ := fun i => i.1
  have hm (k : ℕ) : contourMoment P.eval r k = ∑ i : ι, x i ^ k := by
    rw [contourMoment_eq_sum hr hf s m hs hg hR heq k]
    simpa [ι,x,Fintype.sum_sigma] using
      (Finset.sum_attach s (fun a => (m a : ℂ) * a ^ k)).symm
  have hcard : Fintype.card ι = d := by
    have hc : (Fintype.card ι : ℂ) = (d : ℂ) := by simpa using (hm 0).symm.trans hd
    exact_mod_cast hc
  have hcp : contourPolynomial P.eval r d = Q := by
    rw [← hcard,contourPolynomial_eq_prod x hm]
    dsimp only [Q]
    simpa [ι,x,Fintype.prod_sigma] using
      (Finset.prod_attach s (fun a => (Polynomial.X-Polynomial.C a)^m a))
  rw [hcp]
  exact ⟨R,hPQ⟩

end DegeneratingTrees
end

end OAI
