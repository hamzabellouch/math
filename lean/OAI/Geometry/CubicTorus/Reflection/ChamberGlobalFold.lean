import Mathlib
import OAI.Geometry.CubicTorus.Reflection.CoordinateChamber

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma abs_shortestLift_coordinate (a : Torus) (i : Fin 3) : |shortestLift a i|≤1/2 := by
  have hh := compactCell_coordinates (cubeRepresentative (a+quotientMap cubeCenter)) i
  change 0≤representative (a+quotientMap cubeCenter) i ∧ representative (a+quotientMap cubeCenter) i≤1 at hh
  change |representative (a+quotientMap cubeCenter) i-1/2|≤1/2
  exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩

def chamberFoldLift (s : Fin 3 → Bool) (a : Torus) : Cover :=
  localChamberFold s (chamberCorner s)
    (shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s)

lemma chamberFoldLift_apply (s : Fin 3 → Bool) (a : Torus) (i : Fin 3) :
    chamberFoldLift s a i=chamberCorner s i+|shortestLift (a-quotientMap (chamberCorner s)) i| := by
  simp only [chamberFoldLift,localChamberFold_apply,ite_true,PiLp.add_apply,add_sub_cancel_right]

lemma chamberFoldLift_mem (s : Fin 3 → Bool) (a : Torus) :
    chamberFoldLift s a∈closedHalfBox (chamberCorner s) := by
  intro i
  rw [chamberFoldLift_apply]
  exact ⟨le_add_of_nonneg_right (abs_nonneg _),by linarith [abs_shortestLift_coordinate (a-quotientMap (chamberCorner s)) i]⟩

lemma chamberFoldLift_mem_iff {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) (s : Fin 3 → Bool) (a : Torus) :
    quotientMap (chamberFoldLift s a)∈F ↔ a∈F := by
  rw [chamberFoldLift,localChamberFold_mem_iff hs,quotientMap_add,quotientMap_shortestLift,sub_add_cancel]

def chamberVertex (s b : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i => chamberCorner s i+if b i then (1/2 : ℝ) else 0)

lemma chamberVertex_mem (s b : Fin 3 → Bool) : chamberVertex s b∈closedHalfBox (chamberCorner s) := by
  intro i
  change chamberCorner s i≤chamberCorner s i+(if b i then 1/2 else 0) ∧
    chamberCorner s i+(if b i then 1/2 else 0)≤chamberCorner s i+1/2
  cases b i <;> norm_num

lemma chamberVertex_sine_zero (s b : Fin 3 → Bool) (i : Fin 3) :
    coordinateSine i (representative (quotientMap (chamberVertex s b)))=0 := by
  rw [periodic_representative (coordinateSine_periodic i)]
  cases hs : s i <;> cases hb : b i <;>
    simp [coordinateSine,chamberVertex,chamberCorner,hs,hb] <;> ring_nf <;> first | exact Real.sin_pi | exact Real.sin_two_pi | simpa [mul_comm] using Real.sin_two_pi

lemma chamberVertex_mono (s : Fin 3 → Bool) {b d : Fin 3 → Bool} (hbd : b≤d) :
    ∀ i,chamberVertex s b i≤chamberVertex s d i := by
  intro i
  have hh := hbd i
  cases hb : b i <;> cases hd : d i <;> simp_all [chamberVertex]
  exact ((by decide : ¬(true : Bool)≤false) hh).elim

lemma chamberVertex_bottom (s : Fin 3 → Bool) : chamberVertex s (fun _ => false)=chamberCorner s := by
  ext i; simp [chamberVertex]

lemma chamberVertex_bottom_le (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) : ∀ i,chamberVertex s (fun _ => false) i≤y i := by
  rw [chamberVertex_bottom]
  exact fun i => (hy i).1

lemma chamberVertex_le_top (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) : ∀ i,y i≤chamberVertex s (fun _ => true) i :=
  fun i => (hy i).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_openRepresentative_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    (openRepresentative E).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro he
  have hh := (measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmE)).trans hmE.2.1
  rw [he,measure_empty] at hh
  exact (ENNReal.ofReal_pos.mpr hV.1).ne' hh.symm

lemma isMinimizerAt_vacant_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    (closure (openRepresentative E))ᶜ.Nonempty := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmEc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmE
  have he : (closure (openRepresentative E))ᶜ=openRepresentative Eᶜ := by
    rw [isMinimizerAt_closure_openRepresentative hV hE hmE,openRepresentative,compl_compl]
  rw [he]
  exact isMinimizerAt_openRepresentative_nonempty hVc hE.compl hmEc

lemma mem_open_of_mem_closure_not_frontier {α : Type*} [TopologicalSpace α]
    {F : Set α} (hF : IsOpen F) {a : α} (hc : a∈closure F) (hn : a∉frontier F) : a∈F := by
  by_contra ha
  apply hn
  rw [frontier,hF.interior_eq]
  exact ⟨hc,ha⟩

theorem isMinimizerAt_chamber_vertex_order {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    quotientMap (chamberVertex s (fun _ => false))∈openRepresentative E ∧
    quotientMap (chamberVertex s (fun _ => true))∉closure (openRepresentative E) ∧
    ∀ b d : Fin 3 → Bool,b≤d → quotientMap (chamberVertex s d)∈openRepresentative E →
      quotientMap (chamberVertex s b)∈openRepresentative E := by
  have hsF := fun i => openRepresentative_reflection_invariant hE i (hs i)
  constructor
  · obtain ⟨a,ha⟩ := isMinimizerAt_openRepresentative_nonempty hV hE hmE
    exact isMinimizerAt_chamber_open_downset hV hE hmE hμ hae hsg hs
      (chamberVertex_mem s _) (chamberFoldLift_mem s a)
      (chamberVertex_bottom_le s (chamberFoldLift_mem s a))
      ((chamberFoldLift_mem_iff hsF s a).mpr ha)
  constructor
  · intro htop
    obtain ⟨a,ha⟩ := isMinimizerAt_vacant_nonempty hV hE hmE
    have hfold := isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs
      (chamberFoldLift_mem s a) (chamberVertex_mem s _)
      (chamberVertex_le_top s (chamberFoldLift_mem s a)) htop
    exact ha ((chamberFoldLift_mem_iff (reflection_invariant_closure hsF) s a).mp hfold)
  · intro b d hbd hd
    exact isMinimizerAt_chamber_open_downset hV hE hmE hμ hae hsg hs
      (chamberVertex_mem s _) (chamberVertex_mem s _) (chamberVertex_mono s hbd) hd

theorem isMinimizerAt_vacant_face {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E))
    {x : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hxi : x i=chamberCorner s i+1/2) : quotientMap x∉closure (openRepresentative E) := by
  intro hxE
  apply hv
  apply isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs
    (chamberVertex_mem s _) hx ?_ hxE
  intro j
  by_cases hj : j=i
  · subst j
    change chamberCorner s i+(if decide (i=i) then 1/2 else 0)≤x i
    simp only [decide_true,ite_true,hxi]
    exact le_rfl
  · simpa [chamberVertex,hj] using (hx j).1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_exists_positive_sides {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (hsg : ∀ i : Fin 3,
      (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
      (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0)) :
    ∃ s : Fin 3 → Bool,∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
      0<N x i := by
  classical
  have hg : ∀ i : Fin 3,∃ b : Bool,∀ a∈frontier (openRepresentative E)∩coordinateHalf i (if b then 0 else 1/2),
      0<N (representative a) i := by
    intro i
    rcases hsg i with hi|hi
    · exact ⟨true,hi⟩
    · exact ⟨false,isMinimizerAt_normal_positive_opposite_half hV hE hmE hμ hN hp hae i (hs i) hi⟩
  choose s hs' using hg
  refine ⟨s,?_⟩
  intro x i hx
  have hh := hs' i (quotientMap x) hx
  rwa [periodic_representative hp] at hh

lemma isCompact_closedHalfBox (c : Cover) : IsCompact (closedHalfBox c) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have he : closedHalfBox c=e ⁻¹' (univ.pi fun i => Icc (c i) (c i+1/2)) := by
    ext x
    change (∀ i,c i≤x i ∧ x i≤c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Icc (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Icc]
  rw [he]
  exact e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi fun _ => isCompact_Icc)

theorem isMinimizerAt_chamber_face_gap {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈closedHalfBox (chamberCorner s),
      quotientMap x∈closure (openRepresentative E) → x i≤chamberCorner s i+1/2-δ := by
  let K := closedHalfBox (chamberCorner s) ∩ quotientMap ⁻¹' closure (openRepresentative E)
  have hK : IsCompact K := (isCompact_closedHalfBox _).inter_right
    (isClosed_closure.preimage continuous_quotientMap)
  by_cases hn : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hn (PiLp.continuous_apply _ _ i).continuousOn
    have hlt : x i<chamberCorner s i+1/2 := lt_of_le_of_ne (hx.1 i).2 (by
      intro he
      exact isMinimizerAt_vacant_face hV hE hmE hμ hae hsg hs i hv hx.1 he hx.2)
    refine ⟨chamberCorner s i+1/2-x i,sub_pos.mpr hlt,?_⟩
    intro y hy hyE
    have hh := hmax ⟨hy,hyE⟩
    dsimp at hh
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro x hx hxE
    exact (hn ⟨x,hx,hxE⟩).elim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_tangent_graph_cover {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph (N x) f (normalPlaneCoordinates (N x) v)=v := by
  obtain ⟨m,g,σ,hm,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmE hμ hN hp hae x hx
  have hn : ‖N x‖=1 := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae x hx
  have hcenter : N x=σ • graphSlopeNormal m (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  have ht (v : Plane) : ⟪N x,fderiv ℝ (normalGraph m g) 0 v⟫=0 := by
    rw [hcenter,real_inner_smul_left,normalGraph_derivative_tangent hm hg,mul_zero]
  obtain ⟨f,hf,hf0,hforward,hback⟩ := normalGraph_regraph hm hn hg hg0 ht
  have hnewcov := normalGraph_regraph_cover hf hg hf0 hg0 hforward hback
  refine ⟨f,hf,hf0,?_⟩
  filter_upwards [hcover,hnewcov] with v hv hvc
  exact hv.trans hvc

theorem isMinimizerAt_normal_line_isolated {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∀ᶠ t : ℝ in 𝓝 0, quotientMap (x+t • N x)∈frontier (openRepresentative E) ↔ t=0 := by
  have hn := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae x hx
  have hn0 : N x≠0 := by intro he; simp [he] at hn
  obtain ⟨f,hf,hf0,hcov⟩ := isMinimizerAt_tangent_graph_cover hV hE hmE hμ hN hp hae hx
  have ht : Tendsto (fun t : ℝ => t • N x) (𝓝 0) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun t : ℝ => t • N x) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  filter_upwards [ht.eventually hcov] with t htt
  rw [htt,map_smul,normalPlaneCoordinates_normal hn,smul_zero,normalGraph_zero hf0]
  exact (eq_comm.trans (smul_eq_zero.trans (or_iff_left hn0)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma hasDerivAt_zero_isolated {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d≠0) (h0 : f 0=0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),f t=0 ↔ t=0 := by
  have hs : ∀ᶠ t in 𝓝[≠] (0 : ℝ),slope f 0 t≠0 :=
    hf.tendsto_slope.eventually (eventually_ne_nhds hd)
  have he := eventually_nhdsWithin_iff.mp hs
  filter_upwards [he] with t ht
  by_cases hz : t=0
  · simp [hz,h0]
  · have hh := ht (by simpa using hz)
    have hn : f t≠0 := by
      intro hf0
      apply hh
      simp [slope,h0,hf0]
    simp [hn,hz]

theorem isMinimizerAt_transverse_line_isolated {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {x v : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (hv : ⟪N x,v⟫≠0) :
    ∀ᶠ t : ℝ in 𝓝 0,quotientMap (x+t • v)∈frontier (openRepresentative E) ↔ t=0 := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hm hμ hN hp ha x hx
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  let w := normalPlaneCoordinates n v
  let f : ℝ → ℝ := fun t => g (t • w)-t*⟪n,v⟫
  have hd : HasDerivAt f (⟪gradient g 0,w⟫-⟪n,v⟫) 0 := by
    have hw : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have hh := (hg.differentiable (by simp) (0 : Plane)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hw (by simp)
    rw [inner_gradient_left]
    convert hh.sub ((hasDerivAt_id (0 : ℝ)).mul_const ⟪n,v⟫) using 1 <;> first | rfl | simp
  have hdn : ⟪gradient g 0,w⟫-⟪n,v⟫≠0 := by
    intro he
    apply hv
    rw [hc,graphSlopeNormal_weight hn,real_inner_smul_left,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
    change σ*((cmcWeight (gradient g 0))⁻¹*(⟪n,v⟫-⟪gradient g 0,w⟫))=0
    rw [sub_eq_zero.mp he]
    ring
  have hzero := hasDerivAt_zero_isolated hd hdn (by simp [f,hg0])
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  filter_upwards [ht.eventually hcover,hzero] with t htt hft
  rw [htt,normalGraph_coordinates_eq_iff hn,map_smul,inner_smul_right]
  exact (sub_eq_zero.symm.trans hft)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateHalf_pair (s : Fin 3 → Bool) (a : Torus) (i : Fin 3)
    (ha : coordinateSine i (representative a)≠0) :
    a∈coordinateHalf i (if s i then 0 else 1/2) ∨
      coordinateReflection i a∈coordinateHalf i (if s i then 0 else 1/2) := by
  have h0 : ∀ b : Torus,b∈coordinateHalf i 0 ↔ coordinateSine i (representative b)<0 := by
    intro b; rw [coordinateHalf_zero]; rfl
  have h1 : ∀ b : Torus,b∈coordinateHalf i (1/2) ↔ 0<coordinateSine i (representative b) := by
    intro b
    rw [← coordinateReflection_preimage_half]
    change coordinateReflection i b∈coordinateHalf i 0 ↔ _
    rw [h0,descent_coordinateSine_reflection]
    exact neg_lt_zero
  cases hs : s i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [h1,h1,descent_coordinateSine_reflection]
    rcases lt_or_gt_of_ne ha with h|h
    · right; linarith
    · exact Or.inl h
  · rw [h0,h0,descent_coordinateSine_reflection]
    rcases lt_or_gt_of_ne ha with h|h
    · exact Or.inl h
    · right; linarith

lemma isMinimizerAt_normal_nonzero_off_seam {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3)
    (hz : coordinateSine i x≠0) : N x i≠0 := by
  have hz' : coordinateSine i (representative (quotientMap x))≠0 := by
    rwa [periodic_representative (coordinateSine_periodic i)]
  obtain hh|hh := coordinateHalf_pair s (quotientMap x) i hz'
  · exact (hsg x i ⟨hx,hh⟩).ne'
  · have hry : quotientMap (coverCoordinateReflection i x)∈frontier (openRepresentative E) := by
      rw [quotientMap_coordinateReflection]
      change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
      rwa [frontier_reflection_invariant hE i (hs i)]
    have hn := hsg (coverCoordinateReflection i x) i
      ⟨hry,by rwa [quotientMap_coordinateReflection]⟩
    have he := congrArg (fun v : Cover => v i)
      (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
    simp only [coverCoordinateReflection_apply,ite_true] at he
    rw [he]
    exact neg_ne_zero.mpr hn.ne'

lemma countable_axial_sine_zeros (a : Cover) (i : Fin 3) :
    {t : ℝ | coordinateSine i (a+t • EuclideanSpace.single i 1)=0}.Countable := by
  apply (Set.countable_range (fun k : ℤ => (k : ℝ)/2-a i)).mono
  intro t ht
  obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp ht
  refine ⟨k,?_⟩
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply,ite_true,mul_one] at hk
  have hp := Real.pi_pos
  nlinarith

theorem isMinimizerAt_countable_axial_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (a : Cover) (i : Fin 3) :
    {t : ℝ | quotientMap (a+t • EuclideanSpace.single i 1)∈frontier (openRepresentative E)}.Countable := by
  let v : Cover := EuclideanSpace.single i 1
  let T : Set ℝ := {t | quotientMap (a+t • v)∈frontier (openRepresentative E) ∧ N (a+t • v) i≠0}
  have hdisc : IsDiscrete T := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro t ht
    have hnv : ⟪N (a+t • v),v⟫≠0 := by
      simpa only [v,EuclideanSpace.inner_single_right,one_mul,conj_trivial] using ht.2
    have hloc := isMinimizerAt_transverse_line_isolated hV hE hm hμ hN hp ha ht.1 hnv
    have hshift : Tendsto (fun u : ℝ => u-t) (𝓝 t) (𝓝 0) := by
      have hh : Continuous (fun u : ℝ => u-t) := continuous_id.sub continuous_const
      simpa only [sub_self] using hh.tendsto t
    have he : ∀ᶠ u in 𝓝 t,u∈T → u=t := by
      filter_upwards [hshift.eventually hloc] with u hu huT
      have hid : a+t • v+(u-t) • v=a+u • v := by module
      rw [hid] at hu
      exact sub_eq_zero.mp (hu.mp huT.1)
    obtain ⟨r,hr,hrf⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨Metric.ball t r,Metric.isOpen_ball,?_⟩
    ext u
    constructor
    · rintro ⟨hu,huT⟩; exact mem_singleton_iff.mpr (hrf hu huT)
    · rintro rfl; exact ⟨Metric.mem_ball_self hr,ht⟩
  have hT := (HereditarilyLindelofSpace.isLindelof T).countable_of_isDiscrete hdisc
  apply (hT.union (countable_axial_sine_zeros a i)).mono
  intro t ht
  by_cases hz : coordinateSine i (a+t • v)=0
  · exact Or.inr hz
  · exact Or.inl ⟨ht,isMinimizerAt_normal_nonzero_off_seam hV hE hm hμ hN hp ha hs hsg ht i hz⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_coordinateHalf_of_chamber_interval (s : Fin 3 → Bool) (x : Cover) (i : Fin 3)
    (hx : chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2) :
    quotientMap x∈coordinateHalf i (if s i then 0 else 1/2) := by
  rw [mem_coordinateHalf_quotient]
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hx
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hx.2]
    · nlinarith [Real.pi_pos,hx.1]
  · simp only [chamberCorner,hs,ite_true] at hx
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hr

lemma chamber_zero_normal_endpoint {E : Set Torus} {N : Cover → Cover} {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {x : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hxS : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3) (hz : N x i=0) :
    x i=chamberCorner s i ∨ x i=chamberCorner s i+1/2 := by
  by_contra hn
  push Not at hn
  have hi : chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2 :=
    ⟨lt_of_le_of_ne (hx i).1 (Ne.symm hn.1),lt_of_le_of_ne (hx i).2 hn.2⟩
  have hh := hsg x i ⟨hxS,mem_coordinateHalf_of_chamber_interval s x i hi⟩
  rw [hz] at hh
  exact lt_irrefl _ hh

def chamberAxialCritical (E : Set Torus) (N : Cover → Cover) (s : Fin 3 → Bool) (i : Fin 3) : Set Cover :=
  {x | x∈closedHalfBox (chamberCorner s) ∧ quotientMap x∈frontier (openRepresentative E) ∧
    ∀ j : Fin 3,j≠i → N x j=0}

lemma isCompact_chamberAxialCritical (E : Set Torus) {N : Cover → Cover}
    (hN : Continuous N) (s : Fin 3 → Bool) (i : Fin 3) : IsCompact (chamberAxialCritical E N s i) := by
  have hc : IsClosed {x : Cover | ∀ j : Fin 3,j≠i → N x j=0} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((PiLp.continuous_apply _ _ j).comp hN) continuous_const
  exact (isCompact_closedHalfBox _).inter_right
    ((isClosed_frontier.preimage continuous_quotientMap).inter hc)

theorem isMinimizerAt_finite_chamber_critical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : (chamberAxialCritical E N s i).Finite := by
  apply (isCompact_chamberAxialCritical E hN.continuous s i).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hnorm := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae x hx.2.1
  have hNi : N x i≠0 := by
    intro he
    have hn0 : N x=0 := by
      ext j
      by_cases hj : j=i
      · subst j; exact he
      · exact hx.2.2 j hj
    simp [hn0] at hnorm
  obtain ⟨f,hf,hf0,hcov⟩ := isMinimizerAt_tangent_graph_cover hV hE hmE hμ hN hp hae hx.2.1
  have hnear : ∀ᶠ y : Cover in 𝓝 x,∀ j : Fin 3,|y j-x j|<1/2 := by
    apply eventually_all.mpr
    intro j
    have hc : Continuous (fun y : Cover => |y j-x j|) :=
      ((PiLp.continuous_apply _ _ j).sub continuous_const).abs
    have hh : {t : ℝ | t<1/2}∈𝓝 (|x j-x j|) := by
      simp only [sub_self,abs_zero]
      exact gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)
    exact (hc.continuousAt (x := x)).eventually hh
  have ht : Tendsto (fun y : Cover => y-x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : Cover => y-x) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto x
  have hloc : ∀ᶠ y : Cover in 𝓝 x,y∈chamberAxialCritical E N s i → y=x := by
    filter_upwards [hnear,ht.eventually hcov] with y hy hcy hyK
    have hcoord : ∀ j : Fin 3,j≠i → y j=x j := by
      intro j hj
      obtain hxj|hxj := chamber_zero_normal_endpoint hsg hx.1 hx.2.1 j (hx.2.2 j hj)
      all_goals obtain hyj|hyj := chamber_zero_normal_endpoint hsg hyK.1 hyK.2.1 j (hyK.2.2 j hj)
      · rw [hxj,hyj]
      · have hh := hy j; rw [hxj,hyj] at hh; norm_num at hh
      · have hh := hy j; rw [hxj,hyj] at hh
        have he : chamberCorner s j-(chamberCorner s j+1/2)=-(1/2 : ℝ) := by ring
        rw [he] at hh; norm_num at hh
      · rw [hxj,hyj]
    have he : y-x=((y i-x i)/N x i) • N x := by
      ext j
      change y j-x j=((y i-x i)/N x i)*N x j
      by_cases hj : j=i
      · subst j; field_simp
      · rw [hx.2.2 j hj,hcoord j hj]; ring
    have hpc : normalPlaneCoordinates (N x) (y-x)=0 := by
      rw [he,map_smul,normalPlaneCoordinates_normal hnorm,smul_zero]
    have hb := hcy.mp (by simpa only [add_sub_cancel] using hyK.2.1)
    rw [hpc,normalGraph_zero hf0] at hb
    exact sub_eq_zero.mp hb.symm
  obtain ⟨r,hr,hrloc⟩ := Metric.eventually_nhds_iff.mp hloc
  refine ⟨Metric.ball x r,Metric.isOpen_ball,?_⟩
  ext y
  constructor
  · rintro ⟨hy,hyK⟩
    exact mem_singleton_iff.mpr (hrloc hy hyK)
  · intro hy
    rcases mem_singleton_iff.mp hy with rfl
    exact ⟨Metric.mem_ball_self hr,hx⟩

theorem isMinimizerAt_finite_exceptional_heights {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : ((fun x : Cover => x i) '' chamberAxialCritical E N s i).Finite :=
  (isMinimizerAt_finite_chamber_critical hV hE hmE hμ hN hp hae hsg i).image _

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

theorem monotone_path_unique_exit {X : Type*} [TopologicalSpace X]
    {F : Set X} (hF : IsOpen F) {γ : ℝ → X} (hγ : Continuous γ)
    (h0 : γ 0∈F) (h1 : γ 1∉closure F)
    (hdo : ∀ a∈Icc (0 : ℝ) 1,∀ b∈Icc (0 : ℝ) 1,a≤b → γ b∈F → γ a∈F)
    (hdc : ∀ a∈Icc (0 : ℝ) 1,∀ b∈Icc (0 : ℝ) 1,a≤b → γ b∈closure F → γ a∈closure F)
    (hiso : ∀ t∈Ioo (0 : ℝ) 1,γ t∈frontier F →
      ∀ᶠ u in 𝓝 t,γ u∈frontier F → u=t) :
    ∃ r∈Ioo (0 : ℝ) 1,γ r∈frontier F ∧
      (∀ t∈Icc (0 : ℝ) 1,γ t∈F ↔ t<r) ∧
      (∀ t∈Icc (0 : ℝ) 1,γ t∈closure F ↔ t≤r) ∧
      (∀ t∈Icc (0 : ℝ) 1,γ t∈frontier F ↔ t=r) := by
  have hfront (t : ℝ) : γ t∈frontier F ↔ γ t∈closure F ∧ γ t∉F := by
    rw [frontier,hF.interior_eq]; rfl
  have hends (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) (hb : γ t∈frontier F) : t∈Ioo (0 : ℝ) 1 := by
    have hh := (hfront t).mp hb
    constructor
    · apply lt_of_le_of_ne ht.1
      intro he; subst t; exact hh.2 h0
    · apply lt_of_le_of_ne ht.2
      intro he; subst t; exact h1 hh.1
  have hex : ∃ r∈Icc (0 : ℝ) 1,γ r∈frontier F := by
    by_contra hn
    push Not at hn
    have hcover : Icc (0 : ℝ) 1⊆(γ ⁻¹' F)∪(γ ⁻¹' (closure F)ᶜ) := by
      intro t ht
      by_cases hf : γ t∈F
      · exact Or.inl hf
      · right
        intro hc
        exact hn t ht ((hfront t).mpr ⟨hc,hf⟩)
    have hdisj : Disjoint (γ ⁻¹' F) (γ ⁻¹' (closure F)ᶜ) := by
      apply disjoint_left.mpr
      intro t ho hc
      exact hc (subset_closure ho)
    rcases isPreconnected_Icc.subset_or_subset (hF.preimage hγ)
        (isClosed_closure.isOpen_compl.preimage hγ) hdisj hcover with h|h
    · exact h1 (subset_closure (h (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1)))
    · exact h (by norm_num : (0 : ℝ)∈Icc (0 : ℝ) 1) (subset_closure h0)
  have huniq : ∀ a∈Icc (0 : ℝ) 1,∀ b∈Icc (0 : ℝ) 1,
      γ a∈frontier F → γ b∈frontier F → a=b := by
    suffices hh : ∀ a∈Icc (0 : ℝ) 1,∀ b∈Icc (0 : ℝ) 1,
        γ a∈frontier F → γ b∈frontier F → ¬a<b by
      intro a ha b hb hfa hfb
      exact le_antisymm (le_of_not_gt (hh b hb a ha hfb hfa)) (le_of_not_gt (hh a ha b hb hfa hfb))
    intro a ha b hb hfa hfb hab
    let m := (a+b)/2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m<b := by dsimp [m]; linarith
    have hm : m∈Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt ham,hmb.trans_le hb.2⟩
    have hinterval : ∀ t∈Icc a b,γ t∈frontier F := by
      intro t ht
      have ht01 : t∈Icc (0 : ℝ) 1 := ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩
      apply (hfront t).mpr
      refine ⟨hdc t ht01 b hb ht.2 ((hfront b).mp hfb).1,?_⟩
      intro htf
      exact ((hfront a).mp hfa).2 (hdo a ha t ht01 ht.1 htf)
    obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp (hiso m hm (hinterval m ⟨ham.le,hmb.le⟩))
    let u := m+min δ (b-m)/2
    have hsmall : 0 < min δ (b-m) := lt_min hδ (sub_pos.mpr hmb)
    have hmu : m<u := by dsimp [u]; linarith
    have hub : u<b := by dsimp [u]; linarith [min_le_right δ (b-m)]
    have huδ : dist u m<δ := by
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hmu)]
      dsimp [u]
      linarith [min_le_left δ (b-m)]
    have he := hlocal huδ (hinterval u ⟨ham.le.trans hmu.le,hub.le⟩)
    exact (ne_of_gt hmu) he
  obtain ⟨r,hr,hfr⟩ := hex
  have hri := hends r hr hfr
  have hrc := ((hfront r).mp hfr).1
  have hrn := ((hfront r).mp hfr).2
  refine ⟨r,hri,hfr,?_,?_,?_⟩
  · intro t ht
    constructor
    · intro htf
      by_contra hn
      exact hrn (hdo r hr t ht (le_of_not_gt hn) htf)
    · intro htr
      by_contra hn
      have htf := (hfront t).mpr ⟨hdc t ht r hr htr.le hrc,hn⟩
      exact (ne_of_lt htr) (huniq t ht r hr htf hfr)
  · intro t ht
    constructor
    · intro htc
      by_contra hn
      have hrt : r<t := lt_of_not_ge hn
      have htn : γ t∉F := fun ho => hrn (hdo r hr t ht hrt.le ho)
      exact (ne_of_gt hrt) (huniq t ht r hr ((hfront t).mpr ⟨htc,htn⟩) hfr)
    · intro htr
      exact hdc t ht r hr htr hrc
  · intro t ht
    exact ⟨fun htf => huniq t ht r hr htf hfr,fun he => he.symm ▸ hfr⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def chamberSegment (x y : Cover) (t : ℝ) : Cover := x+t • (y-x)

@[simp] lemma chamberSegment_apply (x y : Cover) (t : ℝ) (i : Fin 3) :
    chamberSegment x y t i=x i+t*(y i-x i) := rfl

lemma chamberSegment_mem {c x y : Cover} (hx : x∈closedHalfBox c)
    (hy : y∈closedHalfBox c) (hxy : ∀ i,x i≤y i) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    chamberSegment x y t∈closedHalfBox c := by
  intro i
  rw [chamberSegment_apply]
  have hlo := mul_nonneg ht.1 (sub_nonneg.mpr (hxy i))
  have hhi := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hxy i))
  constructor <;> nlinarith [(hx i).1,(hy i).2]

lemma chamberSegment_mono {x y : Cover} (hxy : ∀ i,x i≤y i) {t u : ℝ} (htu : t≤u) :
    ∀ i,chamberSegment x y t i≤chamberSegment x y u i := by
  intro i
  simp only [chamberSegment_apply]
  exact add_le_add_right (mul_le_mul_of_nonneg_right htu (sub_nonneg.mpr (hxy i))) _

theorem chamberSegment_normal_positive {E : Set Torus} {N : Cover → Cover}
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i) (hne : x≠y)
    {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1)
    (hb : quotientMap (chamberSegment x y t)∈frontier (openRepresentative E)) :
    0<⟪N (chamberSegment x y t),y-x⟫ := by
  have hterm (i : Fin 3) (hi : x i<y i) :
      0<N (chamberSegment x y t) i*(y i-x i) := by
    have hd : 0<y i-x i := sub_pos.mpr hi
    have hti : chamberCorner s i<chamberSegment x y t i ∧
        chamberSegment x y t i<chamberCorner s i+1/2 := by
      simp only [chamberSegment_apply]
      have hlo := mul_pos ht.1 hd
      have hhi := mul_pos (sub_pos.mpr ht.2) hd
      constructor <;> nlinarith [(hx i).1,(hy i).2]
    exact mul_pos (hsg _ i ⟨hb,mem_coordinateHalf_of_chamber_interval s _ i hti⟩) hd
  have hex : ∃ i : Fin 3,x i<y i := by
    by_contra hn
    push Not at hn
    apply hne
    ext i
    exact le_antisymm (hxy i) (hn i)
  obtain ⟨i,hi⟩ := hex
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,PiLp.sub_apply]
  apply Finset.sum_pos'
  · intro j _
    rcases (hxy j).eq_or_lt with he|hj
    · simp [he]
    · have hh := (hterm j hj).le
      simpa only [mul_comm] using hh
  · exact ⟨i,Finset.mem_univ i,by simpa only [mul_comm] using hterm i hi⟩

theorem isMinimizerAt_chamber_unique_ray_exit {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hxE : quotientMap x∈openRepresentative E) (hyE : quotientMap y∉closure (openRepresentative E)) :
    ∃ r∈Ioo (0 : ℝ) 1,quotientMap (chamberSegment x y r)∈frontier (openRepresentative E) ∧
      (∀ t∈Icc (0 : ℝ) 1,quotientMap (chamberSegment x y t)∈openRepresentative E ↔ t<r) ∧
      (∀ t∈Icc (0 : ℝ) 1,quotientMap (chamberSegment x y t)∈closure (openRepresentative E) ↔ t≤r) ∧
      (∀ t∈Icc (0 : ℝ) 1,quotientMap (chamberSegment x y t)∈frontier (openRepresentative E) ↔ t=r) := by
  have hne : x≠y := by intro he; subst y; exact hyE (subset_closure hxE)
  have hsgc : ∀ z : Cover,quotientMap z∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N z i := by
    intro z hz i
    exact (hsg z i ⟨hz.1,mem_iInter.mp hz.2 i⟩).le
  apply monotone_path_unique_exit (isOpen_openRepresentative E)
    (continuous_quotientMap.comp (continuous_const.add (continuous_id.smul continuous_const)))
    (by simpa [chamberSegment] using hxE) (by simpa [chamberSegment] using hyE)
  · intro a ha' b hb' hab hbE
    exact isMinimizerAt_chamber_open_downset hV hE hm hμ ha hsgc hs
      (chamberSegment_mem hx hy hxy ha') (chamberSegment_mem hx hy hxy hb') (chamberSegment_mono hxy hab) hbE
  · intro a ha' b hb' hab hbE
    exact isMinimizerAt_chamber_closed_downset hV hE hm hμ ha hsgc hs
      (chamberSegment_mem hx hy hxy ha') (chamberSegment_mem hx hy hxy hb') (chamberSegment_mono hxy hab) hbE
  · intro t ht hb
    have hpos := chamberSegment_normal_positive hsg hx hy hxy hne ht hb
    have hi := isMinimizerAt_transverse_line_isolated hV hE hm hμ hN hp ha hb hpos.ne'
    have htc : Tendsto (fun u : ℝ => u-t) (𝓝 t) (𝓝 0) := by
      have hcont : Continuous (fun u : ℝ => u-t) := continuous_id.sub continuous_const
      simpa only [sub_self] using hcont.tendsto t
    filter_upwards [htc.eventually hi] with u hu hub
    have he : chamberSegment x y t+(u-t) • (y-x)=chamberSegment x y u := by
      dsimp only [chamberSegment]
      module
    change quotientMap (chamberSegment x y t+(u-t) • (y-x))∈frontier (openRepresentative E) ↔ u-t=0 at hu
    rw [he] at hu
    exact sub_eq_zero.mp (hu.mp hub)

end CubicTorus

end
end

end OAI
