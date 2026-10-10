import Mathlib
import OAI.Analysis.SymmetricDomains.DifferentiableCauchyTransform

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


theorem bounded_removable_finite
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U E : Set ℂ} (hU : IsOpen U) (hE : E.Finite)
    (f : ℂ → F) (hf : DifferentiableOn ℂ f (U \ E))
    {B : ℝ} (hb : ∀ z ∈ U \ E, ‖f z‖ ≤ B) :
    ∃ g : ℂ → F, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U \ E, g z = f z) ∧ (∀ z ∈ U, ‖g z‖ ≤ B) := by
  classical
  let g : ℂ → F := fun z => if z ∈ E then limUnder (𝓝[≠] z) f else f z
  have heq : ∀ z ∈ U \ E, g z = f z := fun z hz => ite_eq_right hz.2
  have hreg : ∀ z ∈ U \ E, AnalyticAt ℂ g z := by
    intro z hz
    have hh : ∀ᶠ w in 𝓝 z, g w = f w := by
      filter_upwards [(hU.sdiff hE.isClosed).mem_nhds hz] with w hw
      exact heq w hw
    exact (hf.analyticAt ((hU.sdiff hE.isClosed).mem_nhds hz)).congr (Filter.EventuallyEq.symm hh)
  have hpunct : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∈ U \ E := by
    intro z hz
    have hv : U \ (E \ {z}) ∈ 𝓝 z :=
      (hU.sdiff (hE.subset (Set.sdiff_subset : E \ {z} ⊆ E)).isClosed).mem_nhds ⟨hz, by simp⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hv] with w hw hw'
    refine ⟨hw'.1, ?_⟩
    intro hwE
    exact hw'.2 ⟨hwE, hw⟩
  have hlim : ∀ z ∈ U, z ∈ E → Tendsto f (𝓝[≠] z) (𝓝 (g z)) := by
    intro z hz hzE
    change Tendsto f (𝓝[≠] z) (𝓝 (if z ∈ E then _ else _))
    rw [ite_eq_left hzE]
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    · filter_upwards [hpunct z hz] with w hw
      exact hf.differentiableAt ((hU.sdiff hE.isClosed).mem_nhds hw)
    · refine ⟨B + ‖f z‖, ?_⟩
      change ∀ᶠ w in 𝓝[≠] z, ‖f w - f z‖ ≤ B + ‖f z‖
      filter_upwards [hpunct z hz] with w hw
      exact (norm_sub_le _ _).trans (add_le_add (hb w hw) le_rfl)
  refine ⟨g, ?_, heq, ?_⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · have hc : ContinuousAt g z := by
        rw [← continuousWithinAt_compl_self]
        apply (hlim z hz hzE).congr'
        filter_upwards [hpunct z hz] with w hw
        exact (heq w hw).symm
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
      filter_upwards [hpunct z hz] with w hw
      exact (hreg w hw).differentiableAt
    · exact hreg z ⟨hz, hzE⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · exact le_of_tendsto (hlim z hz hzE).norm
        ((hpunct z hz).mono fun w hw => hb w hw)
    · rw [heq z ⟨hz, hzE⟩]
      exact hb z ⟨hz, hzE⟩

theorem bounded_removable_finite_fibers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {c : ℂ} {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (Z : Set (E × ℂ)) (hfinite : ∀ a ∈ A, {z | (a, z) ∈ Z}.Finite)
    (hboundary : ∀ a ∈ A, ∀ z ∈ sphere c R, (a, z) ∉ Z)
    (f : E × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f ((A ×ˢ ball c S) \ Z))
    {B : ℝ} (hb : ∀ p ∈ (A ×ˢ ball c S) \ Z, ‖f p‖ ≤ B) :
    ∃ g : E × ℂ → ℂ, DifferentiableOn ℂ g (A ×ˢ ball c R) ∧
      EqOn g f ((A ×ˢ ball c R) \ Z) ∧ (∀ p ∈ A ×ˢ ball c R, ‖g p‖ ≤ B) := by
  let g : E × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), (w - p.2)⁻¹ * f (p.1, w)
  have hfb : AnalyticOnNhd ℂ f (A ×ˢ sphere c R) := by
    intro p hp
    exact hf p ⟨⟨hp.1, sphere_subset_ball hRS hp.2⟩, hboundary p.1 hp.1 p.2 hp.2⟩
  have hproperties : ∀ a ∈ A, ∃ ga : ℂ → ℂ,
      (∀ z ∈ ball c R, g (a, z) = ga z) ∧
      (∀ z ∈ ball c S \ {z | (a, z) ∈ Z}, ga z = f (a, z)) ∧
      (∀ z ∈ ball c S, ‖ga z‖ ≤ B) := by
    intro a ha
    have hd : DifferentiableOn ℂ (fun z => f (a, z)) (ball c S \ {z | (a, z) ∈ Z}) := by
      intro z hz
      exact ((hf (a, z) ⟨⟨ha, hz.1⟩, hz.2⟩).differentiableAt.comp z
        ((differentiableAt_const a).prodMk differentiableAt_id)).differentiableWithinAt
    obtain ⟨ga, hga, heq, hbound⟩ := bounded_removable_finite isOpen_ball (hfinite a ha)
      (fun z => f (a, z)) hd (fun z hz => hb (a, z) ⟨⟨ha, hz.1⟩, hz.2⟩)
    refine ⟨ga, ?_, heq, hbound⟩
    intro z hz
    have hcauchy : (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(c, R), (w - z)⁻¹ * ga w) = ga z := by
      simpa only [smul_eq_mul] using
        Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := ∅) Set.countable_empty hz
          (hga.continuousOn.mono (closedBall_subset_ball hRS))
          (fun w hw => (hga w ((ball_subset_ball hRS.le) hw.1)).differentiableAt)
    change (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(c, R), (w - z)⁻¹ * f (a, w)) = ga z
    rw [← hcauchy]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro w hw
    dsimp only
    rw [heq w ⟨sphere_subset_ball hRS hw, hboundary a ha w hw⟩]
  refine ⟨g, differentiableOn_cauchyTransform hA hR f hfb, ?_, ?_⟩
  · intro p hp
    obtain ⟨ga, heq, heqf, _⟩ := hproperties p.1 hp.1.1
    exact (heq p.2 hp.1.2).trans (heqf p.2 ⟨ball_subset_ball hRS.le hp.1.2, hp.2⟩)
  · intro p hp
    obtain ⟨ga, heq, _, hbound⟩ := hproperties p.1 hp.1
    rw [heq p.2 hp.2]
    exact hbound p.2 (ball_subset_ball hRS.le hp.2)

noncomputable def linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (x v : Fin n → ℂ) :
    Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) P

theorem eval_linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x v : Fin n → ℂ) (z : ℂ) :
    (linePolynomial P x v).eval z = MvPolynomial.eval (x + z • v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [linePolynomial]
  | add p q hp hq => simpa [linePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    change Polynomial.eval z ((MvPolynomial.eval₂Hom Polynomial.C
      (fun j => Polynomial.C (x j) + Polynomial.X * Polynomial.C (v j)))
      (p * MvPolynomial.X i)) = _
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun w => w * (x i + z * v i)) hp

theorem exists_eval_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ x : Fin n → ℂ, MvPolynomial.eval x P ≠ 0 := by
  by_contra! h
  exact hP (MvPolynomial.funext (fun x => by simpa using h x))

theorem polynomial_eventually_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, p.eval w ≠ 0 := by
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  have hclosed : IsClosed ({w | p.IsRoot w} \ {z}) :=
    (hfin.subset sdiff_subset).isClosed
  have hn : ({w | p.IsRoot w} \ {z})ᶜ ∈ 𝓝 z := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with w hw hwz
  exact fun heq => hw ⟨heq, hwz⟩

theorem exists_polynomial_root_free_sphere {p : Polynomial ℂ} (hp : p ≠ 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ R : ℝ, 0 < R ∧ R < T ∧ ∀ z ∈ sphere (0 : ℂ) R, p.eval z ≠ 0 := by
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  have hclosed : IsClosed ({w | p.IsRoot w} \ {0}) :=
    (hfin.subset sdiff_subset).isClosed
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds (show (0 : ℂ) ∉ {w | p.IsRoot w} \ {0} by simp))
  let R := min T ε / 2
  have hR : 0 < R := half_pos (lt_min hT hε)
  have hRT : R < T := (half_lt_self (lt_min hT hε)).trans_le (min_le_left _ _)
  have hRε : R < ε := (half_lt_self (lt_min hT hε)).trans_le (min_le_right _ _)
  refine ⟨R, hR, hRT, ?_⟩
  intro z hz heq
  have hnorm : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro h
    have hh : 0 = R := by simpa [h] using hnorm
    exact hR.ne' hh.symm
  exact hsub (show z ∈ ball 0 ε by simpa only [mem_ball, dist_zero_right, hnorm] using hRε)
    ⟨heq, hz0⟩

theorem dense_polynomial_nonzero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    Dense {x | MvPolynomial.eval x P ≠ 0} := by
  obtain ⟨q, hq⟩ := exists_eval_ne_zero P hP
  intro x
  let v := q - x
  have hp : linePolynomial P x v ≠ 0 := by
    intro h
    have hh := eval_linePolynomial P x v 1
    simp only [h, Polynomial.eval_zero, one_smul] at hh
    exact hq (by simpa [v] using hh.symm)
  have hc : Continuous (fun z : ℂ => x + z • v) := continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun z : ℂ => x + z • v) (𝓝[≠] 0) (𝓝 x) := by
    simpa using hc.continuousAt.tendsto.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact mem_closure_of_tendsto ht ((polynomial_eventually_ne_zero hp 0).mono fun z hz => by
    simpa only [eval_linePolynomial, Set.mem_ofPred_eq] using hz)

theorem finite_polynomial_line_roots {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (h : ∀ z ∈ sphere (0 : ℂ) R, MvPolynomial.eval (x + z • v) P ≠ 0) :
    {z : ℂ | MvPolynomial.eval (x + z • v) P = 0}.Finite := by
  have hpnz : linePolynomial P x v ≠ 0 := by
    intro he
    have hz : (R : ℂ) ∈ sphere 0 R := by
      simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hn := h (R : ℂ) hz
    rw [← eval_linePolynomial, he, Polynomial.eval_zero] at hn
    exact hn rfl
  simpa only [Polynomial.IsRoot.def, eval_linePolynomial] using
    (Polynomial.finite_setOfPred_isRoot hpnz)

theorem bounded_polynomial_removable_local {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {x | MvPolynomial.eval x P = 0}))
    {B : ℝ} (hb : ∀ x ∈ U \ {x | MvPolynomial.eval x P = 0}, ‖f x‖ ≤ B)
    {a : Fin n → ℂ} (ha : a ∈ U) :
    ∃ A : Set (Fin n → ℂ), IsOpen A ∧ a ∈ A ∧ A ⊆ U ∧
      ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g A ∧
        EqOn g f (A \ {x | MvPolynomial.eval x P = 0}) ∧
        ∀ x ∈ A, ‖g x‖ ≤ B := by
  obtain ⟨q, hq⟩ := exists_eval_ne_zero P hP
  let v := q - a
  let L : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.fst ℂ _ _ + (ContinuousLinearMap.snd ℂ _ _).smulRight v
  have hLv : ∀ p, L p = p.1 + p.2 • v := fun _ => rfl
  have hp : linePolynomial P a v ≠ 0 := by
    intro h
    have hh := eval_linePolynomial P a v 1
    simp only [h, Polynomial.eval_zero, one_smul] at hh
    exact hq (by simpa [v] using hh.symm)
  have hc : Continuous (fun z : ℂ => a + z • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨S, hS, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hU.preimage hc).mem_nhds (show (0 : ℂ) ∈ (fun z => a + z • v) ⁻¹' U by simpa using ha))
  obtain ⟨R, hR, hRS, hRf⟩ := exists_polynomial_root_free_sphere hp hS
  obtain ⟨A₁, V₁, hA₁, _, ha₁, hV₁, hprod₁⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := a)) (isCompact_closedBall (0 : ℂ) S)
      (hU.preimage L.continuous) (by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        have hx' : x = a := mem_singleton_iff.mp hx
        subst x
        exact hsub hz)
  obtain ⟨A₂, V₂, hA₂, _, ha₂, hV₂, hprod₂⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := a)) (isCompact_sphere (0 : ℂ) R)
      (isOpen_ne_fun (P.continuous_eval.comp L.continuous) continuous_const) (by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        have hx' : x = a := mem_singleton_iff.mp hx
        subst x
        change MvPolynomial.eval (a + z • v) P ≠ 0
        rw [← eval_linePolynomial]
        exact hRf z hz)
  let A := A₁ ∩ A₂
  have hA : IsOpen A := hA₁.inter hA₂
  have haA : a ∈ A := ⟨ha₁ (mem_singleton a), ha₂ (mem_singleton a)⟩
  have hmap : MapsTo L (A ×ˢ ball (0 : ℂ) S) U := by
    intro p hp
    exact hprod₁ ⟨hp.1.1, hV₁ (ball_subset_closedBall hp.2)⟩
  let Z : Set ((Fin n → ℂ) × ℂ) := {p | MvPolynomial.eval (L p) P = 0}
  have havoid : ∀ x ∈ A, ∀ z ∈ sphere (0 : ℂ) R, (x, z) ∉ Z := by
    intro x hx z hz
    exact hprod₂ ⟨hx.2, hV₂ hz⟩
  have hfinite : ∀ x ∈ A, {z | (x, z) ∈ Z}.Finite := by
    intro x hx
    exact finite_polynomial_line_roots P x v hR (havoid x hx)
  have hfl : AnalyticOnNhd ℂ (f ∘ L) ((A ×ˢ ball (0 : ℂ) S) \ Z) :=
    hf.comp (fun p _ => L.analyticAt p) (fun p hp => ⟨hmap hp.1, hp.2⟩)
  obtain ⟨g, hg, heq, hbound⟩ := bounded_removable_finite_fibers hA hR hRS Z hfinite havoid
    (f ∘ L) hfl (fun p hp => hb (L p) ⟨hmap hp.1, hp.2⟩)
  refine ⟨A, hA, haA, ?_, (fun x => g (x, 0)), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hLv, zero_smul, add_zero] using hmap (show (x, 0) ∈ A ×ˢ ball 0 S from
      ⟨hx, mem_ball_self hS⟩)
  · intro x hx
    have hgx := hg.differentiableAt ((hA.prod isOpen_ball).mem_nhds
      (show (x, (0 : ℂ)) ∈ A ×ˢ ball 0 R from ⟨hx, mem_ball_self hR⟩))
    exact (hgx.comp x (differentiableAt_id.prodMk (differentiableAt_const 0))).differentiableWithinAt
  · intro x hx
    have hz : (x, (0 : ℂ)) ∉ Z := by simpa only [Z, mem_ofPred_eq, hLv, zero_smul, add_zero] using hx.2
    simpa only [Function.comp_apply, hLv, zero_smul, add_zero] using heq
      (show (x, (0 : ℂ)) ∈ (A ×ˢ ball 0 R) \ Z from ⟨⟨hx.1, mem_ball_self hR⟩, hz⟩)
  · intro x hx
    exact hbound (x, 0) ⟨hx, mem_ball_self hR⟩

end Release061

end OAI
