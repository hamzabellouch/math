import Mathlib
import OAI.Geometry.BallPacking.Forms.HorizontalCoupling

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_sub {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (x : M) : manifoldExteriorOneForm (α-β) x=
      manifoldExteriorOneForm α x-manifoldExteriorOneForm β x := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have he : chartOneForm (α-β) x=chartOneForm α x-chartOneForm β x :=
    funext (chartOneForm_sub α β x)
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he,
    fderiv_sub ((hα x).contDiffAt hn |>.differentiableAt (by simp))
      ((hβ x).contDiffAt hn |>.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.bilinearComp_apply,sub_apply,
    ContinuousLinearMap.flip_apply]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_smul (a : ℝ) {α : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (x : M) : manifoldExteriorOneForm (a • α) x=a • manifoldExteriorOneForm α x := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have he : chartOneForm (a • α) x=a • chartOneForm α x := funext (chartOneForm_smul a α x)
  simp only [manifoldExteriorOneForm,he,euclideanExteriorOneForm_smul a
    ((hα x).contDiffAt hn |>.differentiableAt (by simp))]
  rfl

theorem manifold_closed_exact_normalization {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hclosed : ∀ x,manifoldExteriorOneForm β x=0)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ F) (a : ℝ) (x : M) :
    manifoldExteriorOneForm (α-a • β-manifoldScalarDifferential F) x=
      manifoldExteriorOneForm α x := by
  have hb : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (a • β) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    simpa only [show chartOneForm (a • β) c=fun y => a • chartOneForm β c y
      from funext (chartOneForm_smul a β c)] using (hβ c).const_smul a
  have hab : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (α-a • β) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    exact ((hα c).sub (hb c)).congr (fun y _ => chartOneForm_sub α (a • β) c y)
  rw [manifoldExteriorOneForm_sub hab (manifoldScalarDifferential_smooth hF),
    manifoldScalarDifferential_closed hF,manifoldExteriorOneForm_sub hα hb,
    manifoldExteriorOneForm_smul a hβ,hclosed]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_manifold_cutoff {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ (∀ x, χ x ∈ Icc (0:ℝ) 1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKD
  have hs : tsupport (χ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hχ0 x hn)) hD.isClosed
  exact ⟨χ,χ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport χ).trans hs),hs.trans hDU,hχ1,hχ⟩


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_local_potential_smooth {A : Set M} (hA : IsOpen A)
    {F ζ : M → ℝ} (hF : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ F A)
    (hζ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ζ) (hs : tsupport ζ ⊆ A) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun x => ζ x*F x) := by
  intro x
  by_cases hx : x∈A
  · exact hζ.contMDiffAt.mul (hF.contMDiffAt (hA.mem_nhds hx))
  · have ht : x∉tsupport ζ := fun ht => hx (hs ht)
    apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds ht] with y hy
    have hz : ζ y=0 := notMem_support.mp (fun hv => hy (subset_closure hv))
    simp only [hz,zero_mul]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem scalar_product_tsupport_left (F ζ : M → ℝ) :
    tsupport (fun x => ζ x*F x) ⊆ tsupport ζ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hzero
  exact hx (by simp only [hzero,zero_mul])

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_global_local_potential {K A : Set M} (hK : IsCompact K)
    (hA : IsOpen A) (hKA : K ⊆ A) {F : M → ℝ}
    (hF : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ F A) :
    ∃ G : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ A ∧
      (∀ᶠ x in 𝓝ˢ K,G x=F x) ∧
      HasCompactSupport (manifoldScalarDifferential (E := E) G) ∧
      support (manifoldScalarDifferential (E := E) G) ⊆ A ∧
      (∀ x,manifoldExteriorOneForm (manifoldScalarDifferential (E := E) G) x=0) ∧
      (∀ x ∈ K,manifoldScalarDifferential (E := E) G x=
        manifoldScalarDifferential (E := E) F x) := by
  obtain ⟨ζ,hζ,hζc,hζA,hζ1,_⟩ := exists_smooth_manifold_cutoff (E := E) hK hA hKA
  let G : M → ℝ := fun x => ζ x*F x
  have hG : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ G :=
    manifold_local_potential_smooth hA hF hζ hζA
  have hs : tsupport G ⊆ tsupport ζ := scalar_product_tsupport_left F ζ
  have hGc : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact hζc (subset_closure.trans hs)
  have hEq : ∀ᶠ x in 𝓝ˢ K,G x=F x := by
    filter_upwards [hζ1] with x hx
    simp only [G,hx,one_mul]
  have hd : support (manifoldScalarDifferential (E := E) G) ⊆ tsupport G :=
    manifoldScalarDifferential_support G
  refine ⟨G,hG,hGc,hs.trans hζA,hEq,
    HasCompactSupport.of_support_subset_isCompact hGc hd,hd.trans (hs.trans hζA),
    manifoldScalarDifferential_closed hG,?_⟩
  intro x hx
  have he : G =ᶠ[𝓝 x] F := hEq.filter_mono (nhds_le_nhdsSet hx)
  exact he.mfderiv_eq


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem manifoldFamily_local_potential_smoothOn {V : Set P} {A : Set M}
    (hV : IsOpen V) (hA : IsOpen A) {F : P × M → ℝ} {ζ : M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hζ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ζ) (hs : tsupport ζ ⊆ A) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => ζ q.2*F q) (V ×ˢ univ) := by
  intro q hq
  by_cases hy : q.2∈A
  · exact ((hζ.comp contMDiff_snd).contMDiffAt.mul
      (hF.contMDiffAt ((hV.prod hA).mem_nhds ⟨hq.1,hy⟩))).contMDiffWithinAt
  · have ht : q.2∉tsupport ζ := fun ht => hy (hs ht)
    have he : (fun y : P × M => ζ y.2*F y) =ᶠ[𝓝 q] (fun _ => (0:ℝ)) := by
      have hn := (continuous_snd.continuousAt : ContinuousAt (Prod.snd : P × M → M) q)
      filter_upwards [hn (isClosed_closure.isOpen_compl.mem_nhds ht)] with y hy
      have hz : ζ y.2=0 := notMem_support.mp (fun hv => hy (subset_closure hv))
      simp only [hz,zero_mul]
    exact ((contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq he).contMDiffWithinAt

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_joint_global_local_potential {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {F : P × M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A)) :
    ∃ (G : P × M → ℝ) (L : Set M), IsCompact L ∧ L ⊆ A ∧
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ) ∧
      (∀ p,tsupport (fun y => G (p,y)) ⊆ L) ∧
      (∀ᶠ y in 𝓝ˢ K,∀ p,G (p,y)=F (p,y)) ∧
      (∀ p,support (manifoldScalarDifferential (E := E) (fun y => G (p,y))) ⊆ L) ∧
      (∀ p ∈ V,∀ y,manifoldExteriorOneForm
        (manifoldScalarDifferential (E := E) (fun z => G (p,z))) y=0) ∧
      (∀ p,∀ y ∈ K,manifoldScalarDifferential (E := E) (fun z => G (p,z)) y=
        manifoldScalarDifferential (E := E) (fun z => F (p,z)) y) := by
  obtain ⟨ζ,hζ,hζc,hζA,hζ1,_⟩ := exists_smooth_manifold_cutoff (E := E) hK hA hKA
  let G : P × M → ℝ := fun q => ζ q.2*F q
  have hG := manifoldFamily_local_potential_smoothOn hV hA hF hζ hζA
  have hs : ∀ p,tsupport (fun y => G (p,y)) ⊆ tsupport ζ :=
    fun p => scalar_product_tsupport_left (fun y => F (p,y)) ζ
  have he : ∀ᶠ y in 𝓝ˢ K,∀ p,G (p,y)=F (p,y) := by
    filter_upwards [hζ1] with y hy p
    simp only [G,hy,one_mul]
  refine ⟨G,tsupport ζ,hζc,hζA,hG,hs,he,?_,?_,?_⟩
  · intro p
    exact (manifoldScalarDifferential_support (fun y => G (p,y))).trans (hs p)
  · intro p hp y
    have hfib : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => G (p,z)) := by
      intro z
      exact (hG.contMDiffAt (((hV.prod isOpen_univ)).mem_nhds ⟨hp,mem_univ z⟩)).comp z
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact manifoldScalarDifferential_closed hfib y
  · intro p y hy
    have he' : (fun z => G (p,z)) =ᶠ[𝓝 y] (fun z => F (p,z)) := by
      filter_upwards [he.filter_mono (nhds_le_nhdsSet hy)] with z hz
      exact hz p
    exact he'.mfderiv_eq


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldFamily_scalar_fiber_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    {p : P} (hp : p∈V) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => G (p,z)) := by
  intro z
  exact (hG.contMDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ z⟩)).comp z
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt

theorem manifoldFamily_scalar_chart_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => G (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2))
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  intro q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hq.2)
  have hfst : ContMDiffAt 𝓘(ℝ,P × E) 𝓘(ℝ,P) ∞ (Prod.fst : P × E → P) q :=
    contDiff_fst.contMDiff.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ,P × E) 𝓘(ℝ,E) ∞ (Prod.snd : P × E → E) q :=
    contDiff_snd.contMDiff.contMDiffAt
  have hinc := hfst.prodMk (hi.comp q hsnd)
  have hh := (hG.contMDiffAt ((hV.prod isOpen_univ).mem_nhds
    (show (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)∈V ×ˢ univ from ⟨hq.1,mem_univ _⟩))).comp q hinc
  exact hh.contDiffAt.contDiffWithinAt

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem joint_scalar_fderiv_slice {F : P × E → ℝ} {q : P × E}
    (hF : DifferentiableAt ℝ F q) :
    fderiv ℝ (fun y => F (q.1,y)) q.2=
      (fderiv ℝ F q).comp ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) := by
  have hi : HasFDerivAt (fun y : E => (q.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  exact (hF.hasFDerivAt.comp q.2 hi).fderiv

theorem manifoldFamilyScalarDifferential_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm
        (manifoldScalarDifferential (E := E) (fun z => G (q.1,z))) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  let F : P × E → ℝ := fun q => G (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)
  have hF : ContDiffOn ℝ ∞ F (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    manifoldFamily_scalar_chart_smooth hV hG c
  intro q hq
  have hn := (hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hq
  have hdf : ContDiffAt ℝ ∞ (fun z => fderiv ℝ F z) q :=
    (hF.contDiffAt hn).fderiv_right (by simp)
  have hd := hdf.clm_comp
    (contDiffAt_const (c := ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E))))
  apply (hd.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with z hz
  rw [manifoldScalarDifferential_chart (manifoldFamily_scalar_fiber_smooth hV hG hz.1) hz.2]
  exact joint_scalar_fderiv_slice ((hF.contDiffAt
    ((hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hz)).differentiableAt (by simp))




def normalizedManifoldPrimitive (Γ : P → ManifoldOneForm E M)
    (β : ManifoldOneForm E M) (a : P → ℝ) (G : P × M → ℝ) (p : P) :
    ManifoldOneForm E M := Γ p-a p • β-manifoldScalarDifferential (fun y => G (p,y))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem normalizedManifoldPrimitive_chart
    (Γ : P → ManifoldOneForm E M) (β : ManifoldOneForm E M)
    (a : P → ℝ) (G : P × M → ℝ) (p : P) (c : M) (y : E) :
    chartOneForm (normalizedManifoldPrimitive Γ β a G p) c y=
      chartOneForm (Γ p) c y-a p • chartOneForm β c y-
        chartOneForm (manifoldScalarDifferential (fun z => G (p,z))) c y := by
  simp only [normalizedManifoldPrimitive,chartOneForm_sub,chartOneForm_smul]

theorem normalizedManifoldPrimitive_smooth {V : Set P} (hV : IsOpen V)
    {Γ : P → ManifoldOneForm E M} {β : ManifoldOneForm E M} {a : P → ℝ}
    {G : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (ha : ContDiffOn ℝ ∞ a V)
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm (normalizedManifoldPrimitive Γ β a G q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have hma : ContDiffOn ℝ ∞ (fun q : P × E => a q.1)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ha.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  have hmb : ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm β c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    (hβ c).comp contDiff_snd.contDiffOn (fun _ hx => hx.2)
  exact (((hΓ c).sub (hma.smul hmb)).sub
    (manifoldFamilyScalarDifferential_smooth hV hG c)).congr
      (fun q _ => normalizedManifoldPrimitive_chart Γ β a G q.1 c q.2)

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_normalized_manifold_primitive {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {Γ N : P → ManifoldOneForm E M} {β : ManifoldOneForm E M}
    {a : P → ℝ} {F : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβclosed : ∀ x,manifoldExteriorOneForm β x=0)
    (hβcompact : HasCompactSupport β) (ha : ContDiffOn ℝ ∞ a V)
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hFd : ∀ p ∈ V,∀ x ∈ A,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        Γ p x-N p x-a p • β x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L : Set M), IsCompact L ∧ L ⊆ A ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p ∈ V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p ∈ V,∀ x ∈ K,Γ₁ p x=N p x) := by
  obtain ⟨G,L,hLc,hLA,hG,_,_,hGs,_,hGd⟩ :=
    exists_joint_global_local_potential hV hK hA hKA hF
  let Γ₁ := normalizedManifoldPrimitive Γ β a G
  have hs : ∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L := by
    intro p x hx
    by_contra hout
    have hβz : β x=0 := notMem_support.mp (fun hv => hout (Or.inl (subset_closure hv)))
    have hdz : manifoldScalarDifferential (E := E) (fun y => G (p,y)) x=0 :=
      notMem_support.mp (fun hv => hout (Or.inr (hGs p hv)))
    apply hx
    apply ContinuousLinearMap.ext
    intro v
    change Γ p x v-a p*β x v-manifoldScalarDifferential (E := E) (fun y => G (p,y)) x v-
      Γ p x v=0
    rw [hβz,hdz]
    simp
  refine ⟨Γ₁,L,hLc,hLA,normalizedManifoldPrimitive_smooth hV hΓ hβ ha hG,hs,
    (fun p => HasCompactSupport.of_support_subset_isCompact (hβcompact.union hLc) (hs p)),?_,?_⟩
  · intro p hp x
    have hΓp : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (Γ p) c)
        (extChartAt 𝓘(ℝ,E) c).target := by
      intro c
      exact (hΓ c).comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
        (fun y hy => ⟨hp,hy⟩)
    exact manifold_closed_exact_normalization hΓp hβ hβclosed
      (manifoldFamily_scalar_fiber_smooth hV hG hp) (a p) x
  · intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    change Γ p x v-a p*β x v-manifoldScalarDifferential (E := E) (fun y => G (p,y)) x v=N p x v
    rw [hGd p x hx,hFd p hp x (hKA hx)]
    simp only [sub_apply,smul_apply,smul_eq_mul]
    ring

theorem exists_normalized_manifold_primitive_neighborhood {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {Γ N : P → ManifoldOneForm E M} {β : ManifoldOneForm E M}
    {a : P → ℝ} {F : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβclosed : ∀ x,manifoldExteriorOneForm β x=0)
    (hβcompact : HasCompactSupport β) (ha : ContDiffOn ℝ ∞ a V)
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hFd : ∀ p ∈ V,∀ x ∈ A,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        Γ p x-N p x-a p • β x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L ⊆ A ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ A ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p ∈ V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p ∈ V,∀ x ∈ W,Γ₁ p x=N p x) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDA⟩ := exists_compact_between hK hA hKA
  obtain ⟨Γ₁,L,hL,hLA,hs,hsp,hcp,hd,he⟩ :=
    exists_normalized_manifold_primitive hV hD hA hDA hΓ hβ hβclosed hβcompact ha hF hFd
  exact ⟨Γ₁,L,interior D,hL,hLA,isOpen_interior,hKD,interior_subset.trans hDA,
    hs,hsp,hcp,hd,fun p hp x hx => he p hp x (interior_subset hx)⟩


end


open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def handlePushforwardOneForm (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (α : ManifoldOneForm E M) : ManifoldOneForm F N :=
  extendManifoldOneForm e.target (manifoldPullbackOneForm (fun _ => α) e.symm 0)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handlePushforwardOneForm_zero
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M}
    (hz : ∀ x, x ∉ K → α x=0) {y : N} (hy : y ∉ e '' K) :
    handlePushforwardOneForm e α y=0 := by
  by_cases ht : y∈e.target
  · have hk : e.symm y∉K := by
      intro hk
      exact hy ⟨e.symm y,hk,e.right_inv ht⟩
    rw [handlePushforwardOneForm,extendManifoldOneForm_inside ht]
    simp only [manifoldPullbackOneForm,hz _ hk,ContinuousLinearMap.zero_comp]
  · exact extendManifoldOneForm_outside ht

theorem handlePushforwardOneForm_smooth [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hz : ∀ x, x∉K → α x=0) :
    SmoothOneFormFamily (fun _ : ℝ => handlePushforwardOneForm e α) := by
  have hKi : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hKs)
  change SmoothOneFormFamily (fun p : ℝ => extendManifoldOneForm e.target
    (manifoldPullbackOneForm (fun _ : ℝ => α) e.symm p))
  apply extendManifoldOneForm_smooth e.open_target hKi.isClosed
  · rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKs hx)
  · exact manifoldPullbackOneForm_smooth_on (α := fun _ : ℝ => α)
      e.open_target e.symm.contMDiffOn
      (fun c => (hα c).comp contDiffOn_snd (fun _ hp => hp.2))
  · intro p y hyt hy
    have hk : e.symm y∉K := by
      intro hk
      exact hy ⟨e.symm y,hk,e.right_inv hyt⟩
    simp only [manifoldPullbackOneForm,hz _ hk,ContinuousLinearMap.zero_comp]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem handlePushforwardOneForm_tsupport [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hz : ∀ x, x∉K → α x=0) :
    tsupport (handlePushforwardOneForm e α) ⊆ e '' K := by
  apply closure_minimal _ (hK.image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono hKs)).isClosed
  intro y hy
  by_contra hn
  exact hy (handlePushforwardOneForm_zero e hz hn)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem handlePushforwardOneForm_compact [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hz : ∀ x, x∉K → α x=0) : HasCompactSupport (handlePushforwardOneForm e α) := by
  apply HasCompactSupport.intro (hK.image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono hKs))
  exact fun _ hy => handlePushforwardOneForm_zero e hz hy

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_zero (x : M) :
    manifoldExteriorOneForm (0 : ManifoldOneForm E M) x=0 := by
  unfold manifoldExteriorOneForm
  have hz : chartOneForm (0 : ManifoldOneForm E M) x = fun _ => 0 :=
    funext fun y => chartOneForm_zero x y
  simp only [hz,euclideanExteriorOneForm,fderiv_const_apply,
    ContinuousLinearMap.flip_zero]
  ext u v
  change (0 : ℝ)-0=0
  ring

theorem handlePushforwardOneForm_closed [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hz : ∀ x, x∉K → α x=0) (hd : ∀ x, manifoldExteriorOneForm α x=0) (y : N) :
    manifoldExteriorOneForm (handlePushforwardOneForm e α) y=0 := by
  by_cases hy : y∈e.target
  · rw [handlePushforwardOneForm,extendManifoldOneForm_exterior_inside e.open_target _ hy,
      manifold_pullback_exterior_on hα e.open_target e.symm.contMDiffOn hy]
    simp only [manifoldPullbackTwoForm,hd]
    rfl
  · have hn : y∉e '' K := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hKs hx))
    have hKi := hK.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hKs)
    have he : handlePushforwardOneForm e α =ᶠ[𝓝 y] 0 := by
      filter_upwards [hKi.isClosed.isOpen_compl.mem_nhds hn] with z hzK
      exact handlePushforwardOneForm_zero e hz hzK
    rw [manifoldExteriorOneForm_congr_of_eventuallyEq he,manifoldExteriorOneForm_zero]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handle_mfderiv_symm_comp
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞) {x : M} (hx : x∈e.source) :
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e x)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e x) = ContinuousLinearMap.id ℝ E := by
  have he : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hd := mfderiv_comp x (e.symm.mdifferentiableAt (by simp) (e.map_source hx))
    (e.mdifferentiableAt (by simp) hx)
  rw [← hd,he.mfderiv_eq,mfderiv_id]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handlePushforwardOneForm_pullback
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (α : ManifoldOneForm E M) {x : M} (hx : x∈e.source) :
    manifoldPullbackOneForm (fun _ => handlePushforwardOneForm e α) e 0 x=α x := by
  have hd := handle_mfderiv_symm_comp e hx
  change (extendManifoldOneForm e.target
    (manifoldPullbackOneForm (fun _ => α) e.symm 0) (e x)).comp _ = _
  rw [extendManifoldOneForm_inside (e.map_source hx)]
  ext v
  change α (e.symm (e x))
    ((manifoldMapDifferential (E := E) (F := F) e.symm (e x))
      ((manifoldMapDifferential (E := F) (F := E) e x) v)) = α x v
  have hαx : α (e.symm (e x))=α x := congrArg α (e.left_inv hx)
  rw [hαx]
  exact congrArg (α x) (congrArg (fun D : E →L[ℝ] E => D v) hd)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
