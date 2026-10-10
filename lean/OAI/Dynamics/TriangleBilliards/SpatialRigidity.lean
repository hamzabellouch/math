import OAI.Dynamics.TriangleBilliards.SmoothingLimits

namespace OAI

universe uE

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma smoothing_weak_limit (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0))
    {u : ℕ → DoubleL2 Q} {H : ℝ} (hu : ∀ n, ‖u n‖ ≤ H)
    {g : DoubleL2 Q} (hg : WeaklyTendsto u atTop g) :
    WeaklyTendsto (fun n => smoothingLp Q (hε n) (u n)) atTop g := by
  apply weaklyTendsto_of_inner
  intro v
  have hh := (smoothing_variable_pairing Q hε he hu v).add (hg.inner_right v)
  simpa only [inner_sub_right,sub_add_cancel,zero_add] using hh

noncomputable def clearanceCost (Q : Triangle) : ℝ :=
  ((volume Q.table).toReal)⁻¹ * (3*(2*(Q.safetyFactor+1)+4)^2*Real.pi)

lemma clearanceCost_nonneg (Q : Triangle) : 0 ≤ clearanceCost Q := by
  unfold clearanceCost
  positivity

/-- The genuine fixed-s weak limit. The ε-dependent mode energy is allowed
to grow as s goes to zero; no s-independent bound is used at this stage. -/
lemma clearance_first_limit (Q : Triangle) {H s : ℝ} (hH : 0 ≤ H) (hs : 0 < s)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {U B : DoubleL2 Q}
    (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    ∃ g a b : DoubleL2 Q,
      (∀ᵐ z ∂doubleMeasure Q, ‖g z‖ ≤ H) ∧
      (geodesicHilbertFlow Q).HasGenerator g 0 ∧
      ‖g-f‖ ≤ H * (3*clearanceCost Q*s)^(1/2:ℝ) ∧
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j g) a b ∧ inner ℂ B b = 0 := by
  let K := Q.safetyFactor+1
  let L := 2*K+3
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 ∧ ε^2 < s := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    have hd : Continuous (fun ε : ℝ => ε^2) := by fun_prop
    have hc₀ : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
      simpa using hc.continuousAt.eventually (gt_mem_nhds (by simp only [mul_zero,zero_mul]; norm_num))
    have hd₀ : ∀ᶠ ε : ℝ in 𝓝 0, ε^2 < s := by
      simpa using hd.continuousAt.eventually (gt_mem_nhds (by simpa using hs))
    exact hc₀.and hd₀
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,he⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 ∧ (ε n)^2 < s := hball
    (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  have hT (n : ℕ) : 0 < s/ε n := div_pos hs (hpos n)
  have hR (n : ℕ) : Q.safetyFactor*ε n < K*ε n := by dsimp [K]; nlinarith [hpos n]
  have hL (n : ℕ) : 2*(K*ε n)+2*ε n ≤ L*ε n := by dsimp [L]; nlinarith [hpos n]
  have hd (n : ℕ) := exists_clearance_data Q (L:=L) (hpos n) (hT n) hH (hR n)
    (hsmall n).1 (hL n) hf hinv j hUB hB
  choose g w p a b hgb hclose hgp hpb hw hwb hcr hab hbb hpair using hd
  have hgn (n : ℕ) : ‖g n‖ ≤ H := doubleL2_norm_le_of_ae_bound Q hH (hgb n)
  have hpn : Tendsto p atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (show Tendsto (fun n => (2*H/s)*ε n) atTop (𝓝 0) by
      simpa only [mul_zero] using he.const_mul (2*H/s))
    intro n
    exact (hpb n).trans_eq (by field_simp)
  have hcost (n : ℕ) : (doubleMeasure Q (goodMesh Q L (ε n) (s/ε n))ᶜ).toReal ≤
      3*clearanceCost Q*s := by
    have hl : 0 ≤ L+1 := by dsimp [L]; linarith
    have hh := badMesh_real_bound Q hl (hpos n) (hT n).le
    have hC : ((volume Q.table).toReal)⁻¹*(3*(L+1)^2*Real.pi) = clearanceCost Q := by
      dsimp [clearanceCost,L]; congr 3; dsimp [K]; ring
    rw [hC,div_mul_cancel₀ _ (hpos n).ne'] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsmall n).2.le (clearanceCost_nonneg Q)])
  have hclosen (n : ℕ) : ‖g n-f‖ ≤ H*(3*clearanceCost Q*s)^(1/2:ℝ) := by
    apply (hclose n).trans
    gcongr
    exact hcost n
  let M := Real.sqrt (32*derivativeMass*H^2/s)
  have hM₀ : 0 ≤ 32*derivativeMass*H^2/s := by
    have := derivativeMass_nonneg
    positivity
  have hnorm {x : ℝ} {n : ℕ} (hx : x^2 ≤ 32*derivativeMass*H^2/((s/ε n)*ε n)) : x ≤ M := by
    rw [div_mul_cancel₀ _ (hpos n).ne'] at hx
    have hh := Real.sq_sqrt hM₀
    have hh' := Real.sqrt_nonneg (32*derivativeMass*H^2/s)
    dsimp [M]
    nlinarith
  have han (n : ℕ) : ‖a n‖ ≤ M := hnorm (hab n)
  have hbn (n : ℕ) : ‖b n‖ ≤ M := hnorm (hbb n)
  have hpair0 : Tendsto (fun n => inner ℂ B (b n)) atTop (𝓝 0) := by
    have hy := scaled_smoothingY_norm_tendsto Q U hpos he
    have hlim := (he.const_mul (4*‖B‖*H/s)).add (hy.const_mul (H/s))
    simp only [mul_zero,add_zero] at hlim
    apply squeeze_zero_norm _ hlim
    intro n
    exact (hpair n).trans_eq (by field_simp)
  let : InnerProductSpace ℝ (DoubleL2 Q) := InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨g₀,_,φ,hφ,hg₀⟩ := exists_weak_subsequence_unrestricted g hgn
  obtain ⟨a₀,_,ψ,hψ,ha₀⟩ := exists_weak_subsequence_unrestricted (a ∘ φ) (fun n => han (φ n))
  obtain ⟨b₀,_,χ,hχ,hb₀⟩ := exists_weak_subsequence_unrestricted (b ∘ φ ∘ ψ) (fun n => hbn (φ (ψ n)))
  let κ := φ ∘ ψ ∘ χ
  have hκ : Tendsto κ atTop atTop := hφ.tendsto_atTop.comp (hψ.tendsto_atTop.comp hχ.tendsto_atTop)
  have hgl : WeaklyTendsto (g ∘ κ) atTop g₀ := hg₀.comp (hψ.tendsto_atTop.comp hχ.tendsto_atTop)
  have hal : WeaklyTendsto (a ∘ κ) atTop a₀ := ha₀.comp hχ.tendsto_atTop
  have hbl : WeaklyTendsto (b ∘ κ) atTop b₀ := hb₀
  have hwl : WeaklyTendsto (w ∘ κ) atTop g₀ := by
    have hh := smoothing_weak_limit Q (fun n => hpos (κ n)) (he.comp hκ) (fun n => hgn (κ n)) hgl
    convert hh using 1
    funext n
    exact hw (κ n)
  refine ⟨g₀,a₀,b₀,?_,?_,?_,?_,?_⟩
  · exact hgl.mem_of_closed_convex (isClosed_ae_bounded H) (convex_ae_bounded H)
      (Eventually.of_forall fun n => hgb (κ n))
  · exact HilbertFlow.HasGenerator.weak_limit (geodesicHilbertFlow Q) hgl
      (weaklyTendsto_of_tendsto (hpn.comp hκ)) (Eventually.of_forall fun n => hgp (κ n))
  · exact (hgl.sub_const f).norm_le (Eventually.of_forall fun n => hclosen (κ n))
  · exact RotationalCR.weak_limit (hwl.map (((angularCircleAction Q).projection j).restrictScalars ℝ))
      hal hbl (fun n => hcr (κ n))
  · exact tendsto_nhds_unique (hbl.inner_right B) (hpair0.comp hκ)

end TriangularBilliards

namespace TriangularBilliards.Analysis
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma HilbertFlow.HasGenerator.invariant {W : HilbertFlow E} {u : E}
    (h : W.HasGenerator u 0) (t : ℝ) : W.act t u = u := by
  have hh := h t
  rw [map_zero,sub_eq_zero] at hh
  exact hh

omit [CompleteSpace E] in
lemma HilbertFlow.hasGenerator_zero_iff (W : HilbertFlow E) (u : E) :
    W.HasGenerator u 0 ↔ ∀ t, W.act t u = u := by
  refine ⟨fun h => h.invariant, fun h t => ?_⟩
  rw [h t,sub_self,map_zero]

lemma RotationalCR.unique_pair {T : ℝ} [Fact (0 < T)]
    {X Y : HilbertFlow E} {V : CircleAction E T} {u a b c d : E}
    (h : RotationalCR X Y V u a b) (h' : RotationalCR X Y V u c d) : a=c ∧ b=d :=
  CR_components_eq (X.generator_unique h.generators.1 h'.generators.1)
    (Y.generator_unique h.generators.2 h'.generators.2)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma exists_bounded_representative (Q : Triangle) {u : DoubleL2 Q} {H : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∃ f : DoublePhase → ℂ, StronglyMeasurable f ∧
      (∀ z, ‖f z‖ ≤ H) ∧ f =ᵐ[doubleMeasure Q] u := by
  classical
  let E := {z : DoublePhase | ‖u z‖ ≤ H}
  have hE : MeasurableSet E :=
    measurableSet_le (Lp.stronglyMeasurable u).measurable.norm measurable_const
  refine ⟨E.indicator u,(Lp.stronglyMeasurable u).indicator hE,?_,?_⟩
  · intro z
    by_cases hz : z ∈ E
    · simpa only [indicator_of_mem hz] using (show ‖u z‖ ≤ H from hz)
    · simpa only [indicator_of_notMem hz,norm_zero] using hH
  · filter_upwards [hu] with z hz
    exact indicator_of_mem (show z ∈ E from hz) _

lemma bounded_invariant_CR_ae (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} (_hH : 0 ≤ H) {f : DoubleL2 Q}
      (_hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator f 0) (j : ℤ),
      ∃ a b : DoubleL2 Q,
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
          (angularCircleAction Q) ((angularCircleAction Q).projection j f) a b ∧
        ‖a‖ ≤ C*H ∧ ‖b‖ ≤ C*H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR Q
  refine ⟨C,hC,?_⟩
  intro H hH f hf hfi j
  obtain ⟨f₀,hm,hb,he⟩ := exists_bounded_representative Q hH hf
  have hp : MemLp f₀ 2 (doubleMeasure Q) := (Lp.memLp f).ae_eq he.symm
  have hpeq : hp.toLp f₀ = f := Lp.ext (hp.coeFn_toLp.trans he)
  rw [← hpeq] at hfi ⊢
  exact hbound hm hp hb hfi j

/-- The second limit invokes the *exact invariant* uniform mode bound,
not the fixed-s bound used before. -/
lemma clearance_second_limit (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {a b U : DoubleL2 Q}
    (hcr : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((angularCircleAction Q).projection j f) a b)
    (hUb : (geodesicHilbertFlow Q).HasGenerator U b) : b=0 := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR_ae Q
  obtain ⟨s,_,hs,he⟩ := exists_seq_strictAnti_tendsto' (by norm_num : (0:ℝ)<1)
  have hpos (n : ℕ) : 0 < s n := (hs n).1
  have hmode := (hcr.mode_components ((angularCircleAction Q).projection_eigen j f)).2
  have hd n := clearance_first_limit Q hH (hpos n) hf hinv j hUb hmode
  choose g a' b' hgb hgi hclose hcr' hpair using hd
  have hbounded (n : ℕ) : ‖a' n‖ ≤ C*H ∧ ‖b' n‖ ≤ C*H := by
    obtain ⟨a₀,b₀,hc,ha,hb⟩ := hbound hH (hgb n) (hgi n) j
    obtain ⟨rfl,rfl⟩ := (hcr' n).unique_pair hc
    exact ⟨ha,hb⟩
  have hgstrong : Tendsto g atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hzero := (he.const_mul (3*clearanceCost Q)).rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 1/2))
    have hlim : Tendsto (fun n => H*(3*clearanceCost Q*s n)^(1/2:ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero,Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0)] using hzero.const_mul H
    exact squeeze_zero (fun n => norm_nonneg _) hclose hlim
  let : InnerProductSpace ℝ (DoubleL2 Q) := InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨a₀,_,φ,hφ,ha₀⟩ := exists_weak_subsequence_unrestricted a' (fun n => (hbounded n).1)
  obtain ⟨b₀,_,ψ,hψ,hb₀⟩ := exists_weak_subsequence_unrestricted (b' ∘ φ) (fun n => (hbounded (φ n)).2)
  have hgweak := weaklyTendsto_of_tendsto (hgstrong.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  have hc := RotationalCR.weak_limit
    (hgweak.map (((angularCircleAction Q).projection j).restrictScalars ℝ))
    (ha₀.comp hψ.tendsto_atTop) hb₀ (fun n => hcr' (φ (ψ n)))
  obtain ⟨_,hh⟩ := hcr.unique_pair hc
  have hp : inner ℂ b b₀ = 0 := tendsto_nhds_unique (hb₀.inner_right b)
    (by simpa only [Function.comp_def,hpair] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))
  rw [← hh] at hp
  exact inner_self_eq_zero.mp hp

/-- Analytic rigidity, on the actual double of every nondegenerate triangle.
No irrational-angle assumption is needed for this stage. -/
theorem bounded_invariant_rigidity (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f) (j : ℤ) :
    RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((angularCircleAction Q).projection j f) 0 0 := by
  have hfi := ((geodesicHilbertFlow Q).hasGenerator_zero_iff f).mpr hinv
  obtain ⟨f₀,hm,hb,he⟩ := exists_bounded_representative Q hH hf
  have hp : MemLp f₀ 2 (doubleMeasure Q) := (Lp.memLp f).ae_eq he.symm
  have hpeq : hp.toLp f₀ = f := Lp.ext (hp.coeFn_toLp.trans he)
  obtain ⟨_,_,htail⟩ := bounded_invariant_tail_endpoint Q
  obtain ⟨a,b,hcr,_,ht⟩ := htail hm hp hb (hpeq.symm ▸ hfi)
  simp only [hpeq] at hcr ht
  have hz (m : ℤ) : b m = 0 := clearance_second_limit Q hH hf hinv m (hcr m) (ht m)
  have ha : a j = 0 := by
    have hh := invariant_CR_recurrence (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) (dense_rotationalCR_core Q) hfi a b hcr j
    simpa only [hz,add_zero] using hh
  simpa only [ha,hz] using hcr j

end TriangularBilliards

end
end
end
end
end
end
end
end
end
end

end OAI
