import OAI.Geometry.RCD.Sobolev.DirichletMaximum

namespace OAI

/-!
# Weak maximum principle with nonnegative Lipschitz boundary data

The negative part is placed in the genuine Dirichlet space by bounded-energy
approximation of the Lipschitz core. This is the boundary comparison needed
for the boundedness of the Poisson replacement.
-/

open Set MeasureTheory Filter
open scoped NNReal InnerProductSpace Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem energyForm_add_right (f g h : SobolevSpace μ hQ) :
    energyForm μ hQ f (g + h) = energyForm μ hQ f g + energyForm μ hQ f h := by
  rw [energyForm_comm μ hQ f (g + h), energyForm_add_left,
    energyForm_comm μ hQ g f, energyForm_comm μ hQ h f]

/-- Adding nonpositive Lipschitz boundary data does not obstruct the
Dirichlet membership of the positive part. -/
theorem positivePart_mem_dirichlet_of_boundary_nonpos (Ω : Set X)
    (q : SobolevSpace μ hQ) (Q : X → ℝ) {C : ℝ≥0} (hQlip : LipschitzWith C Q)
    (hQnonpos : ∀ x, Q x ≤ 0) (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ] Q)
    (v : SobolevSpace.dirichlet μ hQ Ω) :
    SobolevSpace.compContraction μ hQ
      ((LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).max_const 0)
      (max_self 0) (q + v.val) ∈ SobolevSpace.dirichlet μ hQ Ω := by
  let pos : ℝ → ℝ := fun t => max t 0
  have hp : LipschitzWith 1 pos :=
    (LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).max_const 0
  have hp0 : pos 0 = 0 := max_self 0
  obtain ⟨fs, hfs, hlim⟩ := mem_closure_iff_seq_limit.mp v.property
  have hlim' : Tendsto (fun i => q + fs i) atTop (𝓝 (q + v.val)) :=
    tendsto_const_nhds.add hlim
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ hlim').exists_norm_le
  let Ts := fun i => SobolevSpace.compContraction μ hQ hp hp0 (q + fs i)
  apply SobolevSpace.mem_dirichlet_of_bounded_L2_limit μ hQ Ω (fs := Ts) (C := D)
  · intro i
    apply (SobolevSpace.dirichletCore μ hQ Ω).le_topologicalClosure
    obtain ⟨g, B, hg, hgc, hgs, hfg⟩ := hfs i
    let w := fun x => max (Q x + g x) 0
    have hw : LipschitzWith (C + B) w := (hQlip.add hg).max_const 0
    have hsupport : Function.support w ⊆ tsupport g := by
      intro x hx
      by_contra hnot
      have hz : g x = 0 := image_eq_zero_of_notMem_tsupport hnot
      have hwz : w x = 0 := by
        simp only [w, hz, add_zero, max_eq_right (hQnonpos x)]
      exact hx hwz
    have hws : tsupport w ⊆ tsupport g := closure_minimal hsupport isClosed_closure
    have hwc : HasCompactSupport w := hgc.of_isClosed_subset isClosed_closure hws
    refine ⟨w, C + B, hw, hwc, hws.trans hgs, ?_⟩
    have hpco := hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ (q + fs i))
    filter_upwards [hpco, Lp.coeFn_add (SobolevSpace.toLp μ hQ q)
      (SobolevSpace.toLp μ hQ (fs i)), hq, hfg] with x hx ha hqx hfx
    change SobolevSpace.toLp μ hQ (Ts i) x = w x
    change (hp.compLp hp0 (SobolevSpace.toLp μ hQ (q + fs i))) x = w x
    rw [hx]
    change max (SobolevSpace.toLp μ hQ (q + fs i) x) 0 = _
    rw [map_add, ha, Pi.add_apply, hqx, hfx]
  · intro i
    exact (SobolevSpace.norm_compContraction_le μ hQ hp hp0 (q + fs i)).trans
      (hD (q + fs i) (mem_range_self i))
  · exact (hp.continuous_compLp hp0).continuousAt.tendsto.comp
      ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hlim')

/-- A weakly harmonic function with nonnegative Lipschitz boundary values
is nonnegative. The Poincare bound is on the actual closed Dirichlet space. -/
theorem harmonic_nonneg_of_boundary (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val)
    (f q : SobolevSpace μ hQ) (Q : X → ℝ) {C : ℝ≥0}
    (hQlip : LipschitzWith C Q) (hQnonneg : ∀ x, 0 ≤ Q x)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ] Q)
    (hfq : f - q ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hf : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, energyForm μ hQ f φ.val = 0) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f x := by
  let pos : ℝ → ℝ := fun t => max t 0
  have hp : LipschitzWith 1 pos :=
    (LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).max_const 0
  have hp0 : pos 0 = 0 := max_self 0
  let N := SobolevSpace.compContraction μ hQ hp hp0 (-f)
  have hnmem : N ∈ SobolevSpace.dirichlet μ hQ Ω := by
    let v : SobolevSpace.dirichlet μ hQ Ω :=
      ⟨q - f, by simpa only [neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem hfq⟩
    have hq' : SobolevSpace.toLp μ hQ (-q) =ᵐ[μ] fun x => -Q x := by
      rw [map_neg]
      exact (Lp.coeFn_neg _).trans (hq.fun_comp Neg.neg)
    have he := positivePart_mem_dirichlet_of_boundary_nonpos μ hQ Ω (-q)
      (fun x => -Q x) hQlip.neg (fun x => neg_nonpos.mpr (hQnonneg x)) hq' v
    have hident : -q + v.val = -f := by dsimp [v]; module
    simpa only [hident] using he
  let U := SobolevSpace.compContraction μ hQ hp hp0 f
  have hU : U = f + N := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ f),
      hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ (-f)),
      Lp.coeFn_add (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ N),
      Lp.coeFn_neg (SobolevSpace.toLp μ hQ f)] with x hu hn ha hneg
    change (SobolevSpace.toLp μ hQ U) x = (SobolevSpace.toLp μ hQ (f + N)) x
    rw [map_add, ha]
    change (hp.compLp hp0 (SobolevSpace.toLp μ hQ f)) x =
      SobolevSpace.toLp μ hQ f x + SobolevSpace.toLp μ hQ N x
    rw [hu]
    change max (SobolevSpace.toLp μ hQ f x) 0 =
      SobolevSpace.toLp μ hQ f x + (hp.compLp hp0 (SobolevSpace.toLp μ hQ (-f))) x
    rw [hn, map_neg]
    simp only [Function.comp_apply, pos]
    rw [hneg]
    change max (SobolevSpace.toLp μ hQ f x) 0 =
      SobolevSpace.toLp μ hQ f x + max (-SobolevSpace.toLp μ hQ f x) 0
    by_cases hx : 0 ≤ SobolevSpace.toLp μ hQ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring
  have henergy : energyForm μ hQ U U ≤ energyForm μ hQ f f := by
    rw [energyForm_self, energyForm_self]
    exact mul_le_mul_of_nonneg_left (SobolevSpace.energy_compContraction_le μ hQ hp hp0 f) (by norm_num)
  have hfN := hf ⟨N, hnmem⟩
  have hNenergy : energyForm μ hQ N N ≤ 0 := by
    rw [hU, energyForm_add_left, energyForm_add_right, energyForm_add_right,
      energyForm_comm μ hQ N f] at henergy
    linarith
  have hnzero : SobolevSpace.toLp μ hQ N = 0 := by
    have hn := (hbound ⟨N, hnmem⟩).trans (mul_nonpos_of_nonneg_of_nonpos hP hNenergy)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hn (sq_nonneg _)))
  have hnco : SobolevSpace.toLp μ hQ N =ᵐ[μ] fun _ => 0 := by
    rw [hnzero]
    exact Lp.coeFn_zero ℝ 2 μ
  filter_upwards [hnco, hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ (-f)),
    Lp.coeFn_neg (SobolevSpace.toLp μ hQ f)] with x hz hn hneg
  change (hp.compLp hp0 (SobolevSpace.toLp μ hQ (-f))) x = 0 at hz
  rw [hn, map_neg] at hz
  simp only [Function.comp_apply, pos] at hz
  rw [hneg] at hz
  change max (-SobolevSpace.toLp μ hQ f x) 0 = 0 at hz
  have hb := le_max_left (-SobolevSpace.toLp μ hQ f x) 0
  linarith

end RegularPointCoordinates

end

end OAI
