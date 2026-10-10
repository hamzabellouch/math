import OAI.Probability.FreeIsing.Gaussian.TreeCovariance
import OAI.Probability.FreeIsing.Trees.ResponseAutomorphism
import OAI.Probability.FreeIsing.Trees.ResponseLeaf

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance (gaussianContraction gaussianContraction_pos
  lintegral_gaussian_attenuation_le)

abbrev response {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) (h : TreeVertex d → ℝ) : ℝ :=
  TreePathResponse.response beta h E r v

lemma measurable_response {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) : Measurable (response beta E r v) := by
  classical
  unfold response TreePathResponse.response TreePathResponse.covariance
    TreePathResponse.mean LeafGibbs.covariance LeafGibbs.expectation GibbsLeaf.energy
  fun_prop

lemma response_congr {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) {h k : TreeVertex d → ℝ}
    (heq : ∀ x ∈ E, h x = k x) : response beta E r v h = response beta E r v k := by
  have he : (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta)) =
      (fun eta => GibbsLeaf.energy beta k E (extendFiniteSpin E eta)) := by
    funext eta
    unfold GibbsLeaf.energy
    congr 1
    exact Finset.sum_congr rfl (fun x hx => by rw [heq x hx])
  unfold response TreePathResponse.response TreePathResponse.covariance TreePathResponse.mean
  rw [he]

lemma response_erase {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r v : TreeVertex d} (beta : ℝ) (h : TreeVertex d → ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w) (hv : v ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w))) :
    response beta E r v h = response beta (E.erase w) r v
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))) :=
  TreePathResponse.response_erase beta h hw hp hedges hr hv

lemma response_leaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r : TreeVertex d} (beta : ℝ) (h : TreeVertex d → ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w))) :
    response beta E r w h =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
        response beta (E.erase w) r p
          (Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))) :=
  TreePathResponse.response_leaf beta h hw hp hedges hr

lemma measurable_response_sq {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) (h : TreeVertex d → ℝ) :
    Measurable (fun x : TreeVertex d → ℝ => ENNReal.ofReal
      (response beta E r v (fun u => h u + x u) ^ 2)) := by
  exact (((measurable_response beta E r v).comp
    (Measurable.of_eval (fun u => measurable_const.add (measurable_pi_apply u)))).pow_const 2).ennreal_ofReal

lemma response_updated_fields {d : ℕ} {E : Finset (TreeVertex d)}
    {w p : TreeVertex d} (beta : ℝ) (r v : TreeVertex d)
    (hp : p ∈ E.erase w) (h x : TreeVertex d → ℝ) (z : ℝ)
    (y : E.erase w → ℝ) :
    response beta (E.erase w) r v
      (Function.update (fun u => h u + Function.updateFinset (Function.update x w z) (E.erase w) y u)
        p (h p + Function.updateFinset (Function.update x w z) (E.erase w) y p +
          cavityMessage (Real.tanh beta)
            (h w + Function.updateFinset (Function.update x w z) (E.erase w) y w))) =
    response beta (E.erase w) r v
      (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u +
        Function.updateFinset x (E.erase w) y u) := by
  classical
  apply response_congr
  intro u hu
  by_cases hup : u = p
  · subst u
    simp only [Function.update_self, Function.updateFinset, dite_eq_left hp,
      Finset.notMem_erase, dite_false, Function.update_self]
    ring
  · simp only [Function.update_of_ne hup, Function.updateFinset, dite_eq_left hu]

lemma lmarginal_leaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r : TreeVertex d} (beta : ℝ) (h x : TreeVertex d → ℝ) (z : ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w)))
    (μ : TreeVertex d → Measure ℝ) :
    lmarginal μ (E.erase w)
      (fun y => ENNReal.ofReal (response beta E r w (fun u => h u + y u) ^ 2))
      (Function.update x w z) =
    ENNReal.ofReal (Real.tanh beta ^ 2 * responseAttenuation (Real.tanh beta) (h w + z) ^ 2) *
      lmarginal μ (E.erase w)
        (fun y => ENNReal.ofReal (response beta (E.erase w) r p
          (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u + y u) ^ 2)) x := by
  classical
  unfold lmarginal
  rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro y
  dsimp only
  rw [response_leaf beta _ hw hp hr hedges, response_updated_fields beta r p hp h x z y]
  simp only [Function.updateFinset, Finset.notMem_erase, dite_false, Function.update_self,
    mul_pow, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

lemma lmarginal_nonleaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r v : TreeVertex d} (beta : ℝ) (h x : TreeVertex d → ℝ) (z : ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w) (hv : v ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w)))
    (μ : TreeVertex d → Measure ℝ) :
    lmarginal μ (E.erase w)
      (fun y => ENNReal.ofReal (response beta E r v (fun u => h u + y u) ^ 2))
      (Function.update x w z) =
      lmarginal μ (E.erase w)
        (fun y => ENNReal.ofReal (response beta (E.erase w) r v
          (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u + y u) ^ 2)) x := by
  classical
  unfold lmarginal
  apply lintegral_congr
  intro y
  dsimp only
  rw [response_erase beta _ hw hp hr hv hedges, response_updated_fields beta r v hp h x z y]

theorem lmarginal_response_sq_le
    {d : ℕ} {beta : ℝ} (_hb : 0 ≤ beta)
    (μ : TreeVertex d → Measure ℝ) [∀ u, IsProbabilityMeasure (μ u)]
    (q : ℝ≥0∞)
    (hq : ∀ (u : TreeVertex d) (a : ℝ),
      (∫⁻ z, ENNReal.ofReal (responseAttenuation (Real.tanh beta) (a + z) ^ 2) ∂μ u) ≤ q)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    lmarginal μ E (fun y => ENNReal.ofReal
      (response beta E r v (fun u => h u + y u) ^ 2)) x ≤
      (ENNReal.ofReal (Real.tanh beta ^ 2) * q) ^ (v.1.length - r.1.length) := by
  classical
  revert hE hr hmin h x v
  refine Finset.strongInductionOn E ?_
  intro E ih hE hr hmin h x v hv
  by_cases hvr : v = r
  · subst v
    simp only [Nat.sub_self, pow_zero]
    unfold lmarginal
    calc
      _ ≤ ∫⁻ _ : E → ℝ, (1 : ℝ≥0∞) ∂Measure.pi (fun u : E => μ u) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_one.mpr
        change TreePathResponse.response beta
          (fun u => h u + Function.updateFinset x E y u) E r r ^ 2 ≤ 1
        rw [TreePathResponse.response_self beta _ hr]
        norm_num
      _ = 1 := by simp
  have hsub : ({r} : Finset (TreeVertex d)) ⊆ E := Finset.singleton_subset_iff.mpr hr
  have hne : ({r} : Finset (TreeVertex d)) ≠ E := by
    intro heq
    exact hvr (Finset.mem_singleton.mp (heq.symm ▸ hv))
  obtain ⟨w, p, hwE, _, hpE, hpw, hEr, hsubr, hedges⟩ :=
    (connectedFinset_singleton r).exists_prunable_vertex_of_shared_min
      hE hsub (Finset.mem_singleton_self r) hmin hne
  have hrEr : r ∈ E.erase w := hsubr (Finset.mem_singleton_self r)
  have hpEr : p ∈ E.erase w := Finset.mem_erase.mpr ⟨hpw, hpE⟩
  have hErE : E.erase w ⊆ E := Finset.erase_subset _ _
  have hmin' : ∀ u ∈ E.erase w, r.1.length ≤ u.1.length :=
    fun u hu => hmin u (hErE hu)
  rw [lmarginal_erase _ (measurable_response_sq beta E r v h) hwE x]
  by_cases hvw : v = w
  · subst v
    have hedge : (p, w) ∈ inducedEdges E := by
      rw [hedges]
      exact Finset.mem_insert_self _ _
    have hdata := Finset.mem_filter.mp hedge
    have hadj : treeAdj p w := hdata.2.1
    have hlower : p.1.length < w.1.length := hdata.2.2
    have hlen := treeAdj_length hadj
    have hdist : w.1.length - r.1.length = (p.1.length - r.1.length) + 1 := by
      have := hmin p hpE
      omega
    let B := ENNReal.ofReal (Real.tanh beta ^ 2) * q
    have hm : Measurable (fun z : ℝ => ENNReal.ofReal
        (responseAttenuation (Real.tanh beta) (h w + z) ^ 2)) := by
      simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
      fun_prop
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.tanh beta ^ 2 *
          responseAttenuation (Real.tanh beta) (h w + z) ^ 2) *
          B ^ (p.1.length - r.1.length) ∂μ w := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [lmarginal_leaf beta h x z hwE hpEr hrEr hedges]
        exact mul_le_mul_right (ih (E.erase w) (Finset.erase_ssubset hwE)
          hEr hrEr hmin' _ x p hpEr) _
      _ = ENNReal.ofReal (Real.tanh beta ^ 2) *
          (∫⁻ z, ENNReal.ofReal (responseAttenuation (Real.tanh beta) (h w + z) ^ 2) ∂μ w) *
          B ^ (p.1.length - r.1.length) := by
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (Real.tanh beta))]
        have hcm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.tanh beta ^ 2) *
            ENNReal.ofReal (responseAttenuation (Real.tanh beta) (h w + z) ^ 2)) :=
          measurable_const.mul hm
        rw [lintegral_mul_const _ hcm, lintegral_const_mul _ hm]
      _ ≤ ENNReal.ofReal (Real.tanh beta ^ 2) * q * B ^ (p.1.length - r.1.length) := by
        gcongr
        exact hq w (h w)
      _ = _ := by
        rw [hdist]
        change B * B ^ (p.1.length - r.1.length) = B ^ ((p.1.length - r.1.length) + 1)
        exact (pow_succ' B _).symm
  · have hvEr : v ∈ E.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
    calc
      _ ≤ ∫⁻ _ : ℝ, (ENNReal.ofReal (Real.tanh beta ^ 2) * q) ^
          (v.1.length - r.1.length) ∂μ w := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [lmarginal_nonleaf beta h x z hwE hpEr hrEr hvEr hedges]
        exact ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' _ x v hvEr
      _ = _ := by simp

theorem lintegral_gaussian_response_sq_le
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    (∫⁻ y : E → ℝ, ENNReal.ofReal (response beta E r v
      (fun u => h u + Function.updateFinset x E y u) ^ 2)
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    ENNReal.ofReal ((Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
      (v.1.length - r.1.length)) := by
  have he := lmarginal_response_sq_le hb (fun u => gaussianReal (m u) (t u))
    (ENNReal.ofReal (gaussianContraction beta δ))
    (fun u a => lintegral_gaussian_attenuation_le beta (m u) a hδ (ht u))
    hE hr hmin h x v hv
  simpa only [lmarginal, ← ENNReal.ofReal_mul (sq_nonneg (Real.tanh beta)),
    ← ENNReal.ofReal_pow (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)] using he

lemma integrable_response_sq {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (_hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    Integrable (fun ω => response beta E r v (fun u => h u + X ω u) ^ 2) P := by
  have hm : Measurable (fun ω => response beta E r v (fun u => h u + X ω u) ^ 2) :=
    ((measurable_response beta E r v).comp
      (Measurable.of_eval (fun u => measurable_const.add
        ((measurable_pi_apply u).comp hX)))).pow_const 2
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hc := TreePathResponse.response_mem_Icc hb
    (fun u => h u + X ω u) hE ⟨r, hr⟩ ⟨v, hv⟩
  have ht := tanh_nonneg_of_beta_nonneg hb
  have hp : Real.tanh beta ^ reducedWordDistance r.1 v.1 ≤ 1 :=
    pow_le_one₀ ht (Real.tanh_lt_one beta).le
  change 0 ≤ response beta E r v (fun u => h u + X ω u) ∧
    response beta E r v (fun u => h u + X ω u) ≤
      Real.tanh beta ^ reducedWordDistance r.1 v.1 at hc
  nlinarith

theorem integral_gaussian_response_sq_le
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    (∫ y : E → ℝ, response beta E r v
      (fun u => h u + Function.updateFinset x E y u) ^ 2
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
      (v.1.length - r.1.length) := by
  apply (ENNReal.ofReal_le_ofReal_iff
    (pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _)).mp
  have hint := integrable_response_sq hb
    (P := Measure.pi (fun u : E => gaussianReal (m u) (t u)))
    (X := fun y => Function.updateFinset x E y) (by fun_prop)
    hE hr hmin h v hv
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_gaussian_response_sq_le hb m t hδ ht hE hr hmin h x v hv

end Problem367.GaussianTreeResponse

end

end OAI
