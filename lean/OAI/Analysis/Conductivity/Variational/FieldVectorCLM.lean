import Mathlib
import OAI.Analysis.Conductivity.Flux.SmoothFluxIntegrable
import OAI.Analysis.Conductivity.Variational.FieldVector
import OAI.Analysis.Conductivity.Sobolev.LpEllipticBounds

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

noncomputable def fieldVectorCLM : Matrix (Fin 3) (Fin 2) ℝ →L[ℝ] FieldVector :=
  ({ toFun := fieldVector
     map_add' := fieldVector_add
     map_smul' := fieldVector_smul } : Matrix (Fin 3) (Fin 2) ℝ →ₗ[ℝ] FieldVector).toContinuousLinearMap

noncomputable def gradientVectorCLM : (Coord3 →L[ℝ] (Fin 2 → ℝ)) →L[ℝ] FieldVector :=
  ({ toFun := fun D => fieldVector (gradientColumns D)
     map_add' := by intro D E; ext ij; simp [fieldVector,gradientColumns,LinearMap.toMatrix']
     map_smul' := by intro c D; ext ij; simp [fieldVector,gradientColumns,LinearMap.toMatrix'] } :
     (Coord3 →L[ℝ] (Fin 2 → ℝ)) →ₗ[ℝ] FieldVector).toContinuousLinearMap

noncomputable def voltageGradient (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : FieldVector :=
  gradientVectorCLM (fderiv ℝ u x)

noncomputable def voltageFlux (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (x : Coord3) : FieldVector :=
  fieldVector (conductivityFlux u A x)

lemma voltageGradient_add {u v : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    voltageGradient (fun y => u y+v y) x = voltageGradient u x+voltageGradient v x := by
  change gradientVectorCLM (fderiv ℝ (u+v) x) = _
  rw [fderiv_add hu hv,map_add]
  rfl

lemma continuous_voltageGradient {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) : Continuous (voltageGradient u) :=
  gradientVectorCLM.continuous.comp (hu.continuous_fderiv (by simp))

lemma compact_voltageGradient {u : Coord3 → Fin 2 → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (voltageGradient u) :=
  (hc.fderiv ℝ).comp_left (map_zero gradientVectorCLM)

lemma tsupport_voltageGradient {u : Coord3 → Fin 2 → ℝ} :
    tsupport (voltageGradient u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  exact hx (by simp only [voltageGradient,fderiv_of_notMem_tsupport ℝ hn,map_zero])

lemma memLp_voltageGradient_smooth_compact
    (μ : Measure Coord3) [IsFiniteMeasureOnCompacts μ]
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hc : HasCompactSupport u) :
    MemLp (voltageGradient u) 2 μ :=
  (continuous_voltageGradient hu).memLp_of_hasCompactSupport (compact_voltageGradient hc)

lemma regularRegion_differentiable {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x : Coord3} (hx : x ∈ regularRegion u A U) : DifferentiableAt ℝ u x := by
  obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx
  exact (hV.2.1.differentiableOn (by simp) x hxV).differentiableAt (hV.1.mem_nhds hxV)

lemma voltageGradient_pairing (u : Coord3 → Fin 2 → ℝ)
    (hu : Differentiable ℝ u) (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) (x : Coord3) :
    inner ℝ (voltageGradient u x) (fieldVector (F x)) =
      ∑ j, fderiv ℝ (fun y => u y j) x ((F x).col j) := by
  rw [show voltageGradient u x = fieldVector (gradientColumns (fderiv ℝ u x)) by rfl,
    fieldVector_inner]
  apply Finset.sum_congr rfl
  intro j _
  have hf : fderiv ℝ (fun y => u y j) x = (ContinuousLinearMap.proj j).comp (fderiv ℝ u x) :=
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x (hu x).hasFDerivAt).fderiv
  rw [hf]
  change ((gradientColumns (fderiv ℝ u x))ᵀ *ᵥ (F x).col j) j = fderiv ℝ u x ((F x).col j) j
  rw [gradientColumns_apply]

lemma CompactGlobalUpdate.gradient_pairing_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    (∫ x, inner ℝ (voltageGradient R.du x)
      (voltageFlux (fun y => u y+R.du y) R.tensor x) ∂μ) = 0 := by
  obtain ⟨hni,hnd⟩ := R.preserves_harmonic μ hint hdiv
  have hcomp : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => R.du x j) :=
    fun j => (contDiff_apply ℝ ℝ j).comp R.smooth_du
  have hc : ∀ j, HasCompactSupport (fun x => R.du x j) :=
    fun j => R.compact_du.comp_left (g := fun v : Fin 2 → ℝ => v j) rfl
  have hs : ∀ j, tsupport (fun x => R.du x j) ⊆ U := by
    intro j
    exact (tsupport_comp_subset (g := fun v : Fin 2 → ℝ => v j) rfl R.du).trans R.support_du
  simp_rw [voltageFlux,voltageGradient_pairing R.du (R.smooth_du.differentiable (by simp))]
  rw [integral_finsetSum _ (fun j _ => hni j _ (hcomp j) (hc j) (hs j))]
  simp only [hnd _ _ (hcomp _) (hc _) (hs _),Finset.sum_const_zero]

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma CompactGlobalUpdate.gradient_add_ae
    (μ : Measure Coord3) {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0) :
    voltageGradient (fun x => u x+R.du x) =ᵐ[μ.restrict U]
      (fun x => voltageGradient u x+voltageGradient R.du x) := by
  apply (ae_restrict_iff' hUm).mpr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hreg] with x hx hxU
  exact voltageGradient_add (regularRegion_differentiable (show x ∈ regularRegion u A U from by by_contra hn; exact hx ⟨hxU,hn⟩))
    (R.smooth_du.differentiable (by simp) x)

lemma CompactGlobalUpdate.fields_memLp
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U) ∧
      MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U) := by
  constructor
  · exact (hE.add ((memLp_voltageGradient_smooth_compact μ R.smooth_du R.compact_du).restrict U)).ae_eq
      (R.gradient_add_ae μ hUm hreg).symm
  · have hdF : MemLp (fun x => fieldVector (R.dF x)) 2 (μ.restrict U) :=
      ((R.smooth_dF.continuous.memLp_of_hasCompactSupport R.compact_dF).continuousLinearMap_comp fieldVectorCLM).restrict U
    apply (hF.add hdF).ae_eq
    exact Eventually.of_forall fun x => by
      simp only [Pi.add_apply,voltageFlux,R.constitutive x,fieldVector_add]

lemma CompactGlobalUpdate.Lp_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖hE'.toLp _‖ ≤ (b/a)*‖hE.toLp _‖ ∧ ‖hF'.toLp _‖ ≤ (b^2/a)*‖hE.toLp _‖ := by
  let E := hE'.toLp _
  let F := hF'.toLp _
  let E₀ := hE.toLp _
  have hg : ∀ᵐ x ∂μ.restrict U, R.tensor x ∈ matrixFiniteLaminate a b :=
    (ae_restrict_iff' hUm).mpr hgraph
  have hpoint : ∀ᵐ x ∂μ.restrict U, a * ‖E x‖^2 ≤ inner ℝ (E x) (F x) ∧
      ‖F x‖^2 ≤ b^2 * ‖E x‖^2 := by
    filter_upwards [hE'.coeFn_toLp,hF'.coeFn_toLp,hg] with x hxE hxF hxg
    change a * ‖hE'.toLp _ x‖^2 ≤ _ ∧ _
    rw [hxE,hxF]
    exact ⟨(fieldVector_quadratic_bounds ha hxg _).1,fieldVector_flux_bound ha hxg _⟩
  obtain ⟨hell,hflux⟩ := Lp_elliptic_bounds (μ.restrict U) E F ha (ha.le.trans hab.le) hpoint
  apply elliptic_energy_bound E F E₀ ha (ha.le.trans hab.le) hell hflux
  rw [L2.inner_def]
  have heq : (fun x => inner ℝ ((E-E₀) x) (F x)) =ᵐ[μ.restrict U]
      (fun x => inner ℝ (voltageGradient R.du x) (voltageFlux (fun y => u y+R.du y) R.tensor x)) := by
    filter_upwards [Lp.coeFn_sub E E₀,hE'.coeFn_toLp,hE.coeFn_toLp,hF'.coeFn_toLp,
      R.gradient_add_ae μ hUm hreg] with x hx hxE hxE₀ hxF hadd
    rw [hx]
    change inner ℝ (E x-E₀ x) (F x) = _
    rw [hxE,hxE₀,hxF,hadd,add_sub_cancel_left]
  rw [integral_congr_ae heq,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact R.gradient_pairing_zero μ hint hdiv
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (R.support_du (tsupport_voltageGradient hh))),inner_zero_left]

end ScalarConductivity

end

end OAI
