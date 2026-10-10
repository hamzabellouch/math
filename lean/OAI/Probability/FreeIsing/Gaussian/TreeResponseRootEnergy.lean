import OAI.Probability.FreeIsing.Gaussian.TreeResponseEnergy
import OAI.Probability.FreeIsing.Gaussian.TreeResponseNaturality

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponseNaturality

open GaussianTreeResponse

theorem finiteRow_fieldEquiv {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ) (h x : TreeVertex d → ℝ)
    (y : D → ℝ) (u : D) (v : TreeVertex d) :
    finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
      (relabel g h) (relabel g x) (g.toEquiv v) (fieldEquiv g D y) =
    finiteRow beta D u h x v y := by
  classical
  by_cases hv : v ∈ D
  · have hgv : g.toEquiv v ∈ D.image g.toEquiv := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    simp only [finiteRow, ite_eq_left hv, ite_eq_left hgv]
    exact response_fieldEquiv g D beta h x y u ⟨v, hv⟩
  · have hgv : g.toEquiv v ∉ D.image g.toEquiv := by
      simpa only [Finset.mem_image, EmbeddingLike.apply_eq_iff_eq,
        exists_eq_right] using hv
    simp only [finiteRow, ite_eq_right hv, ite_eq_right hgv]

theorem tsum_finiteRow_sq_fieldEquiv {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ) (h x : TreeVertex d → ℝ)
    (y : D → ℝ) (u : D) :
    (∑' v, finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
      (relabel g h) (relabel g x) v (fieldEquiv g D y) ^ 2) =
    ∑' v, finiteRow beta D u h x v y ^ 2 := by
  rw [← g.toEquiv.tsum_eq (fun v => finiteRow beta (D.image g.toEquiv)
    (g.toEquiv u) (relabel g h) (relabel g x) v (fieldEquiv g D y) ^ 2)]
  exact tsum_congr fun v => by rw [finiteRow_fieldEquiv]

theorem integral_finiteRow_energy_relabel {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ)
    (m h x : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0) (u : D) :
    (∫ y : D.image g.toEquiv → ℝ, ∑' v,
      finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
        (relabel g h) (relabel g x) v y ^ 2
      ∂Measure.pi (fun a : D.image g.toEquiv =>
        gaussianReal (relabel g m a) (relabel g t a))) =
    ∫ y : D → ℝ, ∑' v, finiteRow beta D u h x v y ^ 2
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a)) := by
  rw [← (measurePreserving_fieldEquiv g D m t).integral_comp']
  exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
    tsum_finiteRow_sq_fieldEquiv g D beta h x y u)

theorem integral_finiteRow_tail_relabel {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (beta : ℝ)
    (m h x : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0) (u : D)
    (hd : ∀ v : TreeVertex d, (g.toEquiv v).1.length = reducedWordDistance u.1.1 v.1)
    (L : ℕ) :
    (∫ y : D.image g.toEquiv → ℝ, ∑' v : TreeVertex d,
      if L < v.1.length then finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
        (relabel g h) (relabel g x) v y ^ 2 else 0
      ∂Measure.pi (fun a : D.image g.toEquiv =>
        gaussianReal (relabel g m a) (relabel g t a))) =
    ∫ y : D → ℝ, ∑' v : TreeVertex d,
      if L < reducedWordDistance u.1.1 v.1 then finiteRow beta D u h x v y ^ 2 else 0
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a)) := by
  rw [← (measurePreserving_fieldEquiv g D m t).integral_comp']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [← g.toEquiv.tsum_eq (fun v : TreeVertex d =>
    if L < v.1.length then finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
      (relabel g h) (relabel g x) v (fieldEquiv g D y) ^ 2 else 0)]
  exact tsum_congr fun v => by rw [hd, finiteRow_fieldEquiv]

theorem integrable_finiteRow_sq_anyroot
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (u : D) (v : TreeVertex d) :
    Integrable (fun y : D → ℝ => finiteRow beta D u h x v y ^ 2)
      (Measure.pi (fun a : D => gaussianReal (m a) (t a))) := by
  obtain ⟨g, hg, _⟩ := exists_treeAut_to_root_distance u.1
  have hnil : (g.toEquiv u).1 = [] := congrArg Subtype.val hg
  have hi : Integrable
      (fun y : D.image g.toEquiv → ℝ =>
        finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
          (relabel g h) (relabel g x) (g.toEquiv v) y ^ 2)
      (Measure.pi (fun a : D.image g.toEquiv =>
        gaussianReal (relabel g m a) (relabel g t a))) :=
    integrable_finiteRow_sq hb (relabel g m) (relabel g t) (hD.image g)
      (TreeGibbsAut.vertexEquiv g D u).property hnil
      (relabel g h) (relabel g x) (g.toEquiv v)
  have hp := (measurePreserving_fieldEquiv g D m t).integrable_comp_of_integrable hi
  simpa only [Function.comp_def, finiteRow_fieldEquiv] using hp

theorem integral_finiteRow_energy_le_anyroot
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ a, δ ≤ t a)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (u : D) :
    (∫ y : D → ℝ, ∑' v, finiteRow beta D u h x v y ^ 2
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a))) ≤
    1 + (d : ℝ) * (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ) /
      (1 - ((d - 1 : ℕ) : ℝ) *
        (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ)) := by
  obtain ⟨g, hg, _⟩ := exists_treeAut_to_root_distance u.1
  have hnil : (g.toEquiv u).1 = [] := congrArg Subtype.val hg
  have he := integral_finiteRow_energy_le hb (relabel g m) (relabel g t)
    hδ (fun a => ht (g.toEquiv.symm a)) hcrit (hD.image g)
    (TreeGibbsAut.vertexEquiv g D u).property hnil (relabel g h) (relabel g x)
  change (∫ y : D.image g.toEquiv → ℝ, ∑' v,
    finiteRow beta (D.image g.toEquiv) (g.toEquiv u) (relabel g h) (relabel g x) v y ^ 2
    ∂Measure.pi (fun a : D.image g.toEquiv =>
      gaussianReal (relabel g m a) (relabel g t a))) ≤ _ at he
  rw [integral_finiteRow_energy_relabel] at he
  exact he

theorem integral_finiteRow_energy_tail_le_anyroot
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ a, δ ≤ t a)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (u : D) (L : ℕ) :
    (∫ y : D → ℝ, ∑' v : TreeVertex d,
      if L < reducedWordDistance u.1.1 v.1 then finiteRow beta D u h x v y ^ 2 else 0
      ∂Measure.pi (fun a : D => gaussianReal (m a) (t a))) ≤
    (d : ℝ) * (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ) *
      (((d - 1 : ℕ) : ℝ) *
        (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ)) ^ L /
      (1 - ((d - 1 : ℕ) : ℝ) *
        (Real.tanh beta ^ 2 * GaussianTreeCovariance.gaussianContraction beta δ)) := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  have hnil : (g.toEquiv u).1 = [] := congrArg Subtype.val hg
  have he := integral_finiteRow_energy_tail_le hb (relabel g m) (relabel g t)
    hδ (fun a => ht (g.toEquiv.symm a)) hcrit (hD.image g)
    (TreeGibbsAut.vertexEquiv g D u).property hnil (relabel g h) (relabel g x) L
  change (∫ y : D.image g.toEquiv → ℝ, ∑' v : TreeVertex d,
    if L < v.1.length then finiteRow beta (D.image g.toEquiv) (g.toEquiv u)
      (relabel g h) (relabel g x) v y ^ 2 else 0
    ∂Measure.pi (fun a : D.image g.toEquiv =>
      gaussianReal (relabel g m a) (relabel g t a))) ≤ _ at he
  rw [integral_finiteRow_tail_relabel g D beta m h x t u hd L] at he
  exact he

theorem norm_finiteRow_le_distance {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (y : D → ℝ) (u : D) (v : TreeVertex d) :
    ‖finiteRow beta D u h x v y‖ ≤ Real.tanh beta ^ reducedWordDistance u.1.1 v.1 := by
  classical
  by_cases hv : v ∈ D
  · have he := TreePathResponse.response_mem_Icc hb
      (fun a => h a + Function.updateFinset x D y a) hD u ⟨v, hv⟩
    simp only [finiteRow, ite_eq_left hv, Real.norm_eq_abs]
    rw [abs_of_nonneg he.1]
    exact he.2
  · simp only [finiteRow, ite_eq_right hv, norm_zero]
    exact pow_nonneg (tanh_nonneg_of_beta_nonneg hb) _

theorem finiteRow_energy_le_of_strict {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (y : D → ℝ) (u : D) :
    (∑' v, finiteRow beta D u h x v y ^ 2) ≤
      1 + (d : ℝ) * Real.tanh beta ^ 2 /
        (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance u.1
  have hdist (v : TreeVertex d) :
      reducedWordDistance u.1.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have he := tsum_norm_sq_le_of_radial_bound d hstrict
    (fun v => finiteRow beta D u h x (g.toEquiv.symm v) y)
    (fun v => by simpa only [hdist] using norm_finiteRow_le_distance hb hD h x y u (g.toEquiv.symm v))
  simp only [Real.norm_eq_abs, sq_abs] at he
  rw [g.toEquiv.symm.tsum_eq (fun v => finiteRow beta D u h x v y ^ 2)] at he
  exact he

theorem finiteRow_energy_tail_le_of_strict {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (y : D → ℝ) (u : D) (L : ℕ) :
    (∑' v : TreeVertex d, if L < reducedWordDistance u.1.1 v.1
      then finiteRow beta D u h x v y ^ 2 else 0) ≤
    (d : ℝ) * Real.tanh beta ^ 2 *
      (((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) ^ L /
      (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance u.1
  have hdist (v : TreeVertex d) :
      reducedWordDistance u.1.1 (g.toEquiv.symm v).1 = v.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm v)).symm
  have hbound (v : TreeVertex d) : finiteRow beta D u h x (g.toEquiv.symm v) y ^ 2 ≤
      1 * (Real.tanh beta ^ 2) ^ v.1.length := by
    have he := pow_le_pow_left₀ (norm_nonneg _) (norm_finiteRow_le_distance hb hD h x y u
      (g.toEquiv.symm v)) 2
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs, hdist, one_mul,
      ← pow_mul, Nat.mul_comm] using he
  have he := tsum_cutoff_le_of_tree_radial_le
    (fun v => sq_nonneg (finiteRow beta D u h x (g.toEquiv.symm v) y))
    hbound (sq_nonneg (Real.tanh beta)) hstrict L
  rw [← g.toEquiv.symm.tsum_eq (fun v : TreeVertex d =>
    if L < reducedWordDistance u.1.1 v.1 then finiteRow beta D u h x v y ^ 2 else 0)]
  simpa only [hdist, one_mul] using he

theorem integrable_finiteRow_energy_of_strict
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (h x : TreeVertex d → ℝ) (u : D) {Y : Ω → D → ℝ} (hY : Measurable Y) :
    Integrable (fun ω => ∑' v, finiteRow beta D u h x v (Y ω) ^ 2) P := by
  classical
  have hm (v : TreeVertex d) :
      Measurable (fun ω => finiteRow beta D u h x v (Y ω) ^ 2) := by
    by_cases hv : v ∈ D
    · simp only [finiteRow, ite_eq_left hv]
      apply Measurable.pow_const
      apply (GaussianTreeResponse.measurable_response beta D u v).comp
      fun_prop
    · simp only [finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
      exact measurable_const
  apply (integrable_const (1 + (d : ℝ) * Real.tanh beta ^ 2 /
    (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2))).mono'
    (Measurable.tsum hm).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
  exact finiteRow_energy_le_of_strict hb hstrict hD h x (Y ω) u

end Problem367.GaussianTreeResponseNaturality

end

end OAI
