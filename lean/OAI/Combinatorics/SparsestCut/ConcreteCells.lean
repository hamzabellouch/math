import OAI.Combinatorics.SparsestCut.EuclideanCells

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ConcreteCells
open MeasureTheory Set Filter CoordinateSplit EuclideanCells
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def domain : Set (ℝ × Z) := split.symm ⁻¹' RoundedCharts.cube 2

def labels (τ : ℝ) : Finset ℤ := Finset.Icc (-⌈4*Real.sqrt (m+1:ℕ)/τ+1⌉) ⌈4*Real.sqrt (m+1:ℕ)/τ+1⌉

lemma domain_open : IsOpen (domain (m := m)) := by
  apply IsOpen.preimage split.symm.continuous
  change IsOpen {θ : E | ∀ j, |θ j|<2}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (by fun_prop) continuous_const

lemma ell_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (x : ℝ × Z) (i : Fin N) :
    ProductSlice.ell (B u) (pivot u) i x=inner ℝ (u i) (split.symm x) := by
  have h := normalized_form (u i) (hu i) (split.symm x)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  change pivot u i*ProductSlice.form (B u i) x=_
  change u i 0*(x.1-slope (u i) x.2)=_
  rw [← h]
  field_simp [hu i]

lemma regular_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (x : ℝ × Z) :
    CellInterface.regular (ProductSlice.ell (B u) (pivot u)) τ x ↔
      RoundedCharts.regular u τ (split.symm x) := by
  simp only [CellInterface.regular,RoundedCharts.regular,ell_eq u hu]
lemma label_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (x : ℝ × Z) :
    CellInterface.label (ProductSlice.ell (B u) (pivot u)) τ x =
      RoundedCharts.integerLabel u τ (split.symm x) := by
  ext i
  simp only [CellInterface.label,RoundedCharts.integerLabel,ell_eq u hu]

lemma labels_bound (u : Fin N → E) (hu : ∀ i, u i 0≠0) {τ : ℝ} (hτ : 0<τ)
    (hn : ∀ i, ‖u i‖≤2) (x : ℝ × Z) (hx : x∈domain)
    (_hr : CellInterface.regular (ProductSlice.ell (B u) (pivot u)) τ x) (i : Fin N) :
    CellInterface.label (ProductSlice.ell (B u) (pivot u)) τ x i∈labels (m := m) τ := by
  rw [label_eq u hu]
  have hb := (RoundedCharts.integerLabel_bound u hτ hn hx i).trans
    (Int.le_ceil (4*Real.sqrt (m+1:ℕ)/τ+1))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp hb).1
  · exact_mod_cast (abs_le.mp hb).2

def mapVertex (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ) (s : Fin S)
    (v : CellInterface.LabelVertex (ProductSlice.ell (B (u s)) (pivot (u s))) τ domain) : RoundedCharts.Vertex u τ :=
  ⟨(s,v.val),by
    obtain ⟨x,hx,hr,hl⟩ := v.property
    refine ⟨split.symm x,hx,(regular_eq (u s) (hu s) τ x).mp hr,?_⟩
    exact (label_eq (u s) (hu s) τ x).symm.trans hl⟩

def function (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) (s : Fin S) (a : A) : E → ℝ :=
  chartFunction (u s) τ (labels (m := m) τ) domain (fun v => F (mapVertex u hu τ s v)) a

omit [Fintype A] in
lemma function_eq (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) {τ : ℝ}
    (hτ : 0<τ) (hn : ∀ s i, ‖u s i‖≤2) (F : RoundedCharts.Vertex u τ → A → ℝ)
    (s : Fin S) (x : E) (hx : x∈RoundedCharts.cube 2) (hr : RoundedCharts.regular (u s) τ x) (a : A) :
    function u hu τ F s a x=F ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩ a := by
  have hx' : split x∈domain := by simpa only [domain,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hx
  have hr' : CellInterface.regular (ProductSlice.ell (B (u s)) (pivot (u s))) τ (split x) := by
    rw [regular_eq (u s) (hu s)]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr
  rw [function,chartFunction_eq (u s) (hu s) hτ _ _ (labels_bound (u s) (hu s) hτ (hn s)) _ x hx' hr']
  congr 1
  apply Subtype.ext
  change (s,CellInterface.label (ProductSlice.ell (B (u s)) (pivot (u s))) τ (split x))=(s,RoundedCharts.integerLabel (u s) τ x)
  congr 1
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using label_eq (u s) (hu s) τ (split x)

omit [Fintype A] in
lemma function_measurable (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) (s : Fin S) (a : A) : Measurable (function u hu τ F s a) :=
  chartFunction_measurable _ _ _ _ _ _
omit [Fintype A] in
lemma function_bounded (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hF : ∀ v a, |F v a|≤M)
    (s : Fin S) (a : A) (x : E) : |function u hu τ F s a x|≤M := by
  exact CellInterface.extension_bounded (ProductSlice.ell (B (u s)) (pivot (u s))) (pivot (u s)) τ (labels (m := m) τ) domain (fun v => F (mapVertex u hu τ s v)) hM (fun v a => hF _ a) _ a
omit [Fintype A] in
lemma function_integrable (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hF : ∀ v a, |F v a|≤M)
    (s : Fin S) (a : A) : LocallyIntegrable (function u hu τ F s a) :=
  chartFunction_integrable _ _ _ _ _ hM (fun _v a => hF _ a) a

lemma support_domain {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (θ : E)
    (hθ : ∀ j, |θ j|≤1) :
    ∀ᵐ z ∂ProductSlice.law (ProductMollifier.kernel (m := m) (ProductMollifier.density lam)) volume,
      ∀ t : ℝ, |t|<lam → split θ-(t,z)∈domain := by
  apply (ae_withDensity_iff ((ProductMollifier.kernel_smooth (m := m) _ (ProductMollifier.density_smooth lam)).continuous.measurable.ennreal_ofReal)).mpr
  filter_upwards with z hz t ht
  have hψ : ProductMollifier.kernel (ProductMollifier.density lam) z≠0 := by
    intro he
    exact hz (by simp [he])
  have hz' (j : Fin m) : |z j|<lam := by
    apply ProductMollifier.density_support hlam
    intro he
    exact hψ (Finset.prod_eq_zero (Finset.mem_univ j) he)
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · change |θ 0-t|<2
    exact (abs_sub _ _).trans_lt (by linarith [hθ 0])
  · change |θ i.succ-z i|<2
    exact (abs_sub _ _).trans_lt (by linarith [hθ i.succ,hz' i])

lemma normal_coefficients (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M J : ℝ} (hM : 0≤M) (hJ : 0≤J)
    (hbound : ∀ v a, |F v a|≤M)
    (hF : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) →
      ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *(lam⁻¹*(∫ t, |deriv ProductMollifier.rho t|))≤1)
    (s : Fin S) (θ : E) (hθ : ∀ j, |θ j|≤1) :
    ∃ β : Fin N → A → ℝ,
      (∀ a, HasFDerivAt (convolution (ProductMollifier.kernel (m := m+1) (ProductMollifier.density lam))
          (function u hu τ F s a) (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, β i a • InnerProductSpace.toDual ℝ E (u s i)) θ) ∧
      (∀ i, ∑ a, |β i a|≤2*J/τ) := by
  exact EuclideanCells.coefficients (u s) (hu s) (hnp s) hτ hlam _ domain_open
    (labels_bound (u s) (hu s) hτ (hn s)) (fun v => F (mapVertex u hu τ s v))
    hM hJ (fun v a => hbound _ a)
    (fun vp vm i hi hj => hF _ _ i rfl hi hj) θ (support_domain hlam hlam1 θ hθ) (hsmall s)

lemma regular_sub (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (θ : E) :
    ∀ᵐ z : E, RoundedCharts.regular u τ (θ-z) := by
  have hh := RoundedCharts.ae_regular u τ (fun i h => hu i (by rw [h]; rfl))
  have hmp := (measurePreserving_add_left volume θ).comp (Measure.measurePreserving_neg (volume : Measure E))
  simpa only [Function.comp_apply, sub_eq_add_neg] using hmp.quasiMeasurePreserving.ae hh

end
end UniformSparsestCut.ConcreteCells

end

end OAI
