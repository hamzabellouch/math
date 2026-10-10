import Mathlib
import OAI.Geometry.CubicTorus.Reflection.ChamberGlobalFold

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_normal_product {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3)
    (hxi : |x i-chamberCorner s i|<1/2) (hne : x i≠chamberCorner s i) :
    0<N x i*(x i-chamberCorner s i) := by
  obtain hn|hn := lt_or_gt_of_ne hne
  · let q := x+(2*chamberCorner s i-2*x i) • EuclideanSpace.single i 1
    have hqi : q i=2*chamberCorner s i-x i := by
      simp only [q,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
      ring
    have hc : ∃ k : ℤ,2*chamberCorner s i=(k : ℝ) := by
      cases hi : s i
      · exact ⟨0,by simp [chamberCorner,hi]⟩
      · exact ⟨1,by simp [chamberCorner,hi]⟩
    have hqeq : quotientMap q=coordinateReflection i (quotientMap x) := quotientMap_centered_reflection i hc x
    have hinv := fun j => frontier_reflection_invariant hE j (hs j)
    have hqb : quotientMap q∈frontier (openRepresentative E) := by
      rw [hqeq]
      change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
      rwa [hinv i]
    have hqhalf : q i∈Ioo (chamberCorner s i) (chamberCorner s i+1/2) := by
      rw [hqi]
      obtain ⟨hl,hu⟩ := abs_lt.mp hxi
      constructor <;> linarith
    have hpos : 0<N q i := hsg q i ⟨hqb,mem_coordinateHalf_of_chamber_interval s q i hqhalf⟩
    have hNq : N q=N (coverCoordinateReflection i x) := by
      rw [← periodic_representative hp q,hqeq,← quotientMap_coordinateReflection,periodic_representative hp]
    have hcov := congrArg (fun z : Cover => z i) (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
    simp only [coverCoordinateReflection_apply,ite_true] at hcov
    rw [← hNq] at hcov
    exact mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hn)
  · have hpos : 0<N x i := hsg x i ⟨hx,mem_coordinateHalf_of_chamber_interval s x i
      ⟨hn,by linarith [(abs_lt.mp hxi).2]⟩⟩
    exact mul_pos hpos (sub_pos.mpr hn)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePlaneLift : ℂ →L[ℝ] Cover :=
  Complex.reCLM.smulRight (EuclideanSpace.single 1 1)+
    Complex.imCLM.smulRight (EuclideanSpace.single 2 1)

def coordinateSectionPoint (c : Cover) (t : ℝ) (z : ℂ) : Cover :=
  c+(t-c 0) • EuclideanSpace.single 0 1+coordinatePlaneLift z

@[simp] lemma coordinatePlaneLift_apply (z : ℂ) (i : Fin 3) :
    coordinatePlaneLift z i=if i=1 then z.re else if i=2 then z.im else 0 := by
  fin_cases i <;> simp [coordinatePlaneLift]

@[simp] lemma coordinateSectionPoint_apply (c : Cover) (t : ℝ) (z : ℂ) (i : Fin 3) :
    coordinateSectionPoint c t z i=if i=0 then t else if i=1 then c 1+z.re else c 2+z.im := by
  fin_cases i <;> simp [coordinateSectionPoint]

lemma coordinateSectionPoint_contDiff (c : Cover) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateSectionPoint c t) :=
  contDiff_const.add coordinatePlaneLift.contDiff

lemma coordinateSectionPoint_segment (c : Cover) (t r : ℝ) (z : ℂ) :
    chamberSegment (coordinateSectionPoint c t 0) (coordinateSectionPoint c t z) r=
      coordinateSectionPoint c t (r • z) := by
  ext i
  fin_cases i <;> simp [chamberSegment_apply]

lemma coordinateSectionPoint_fold (s : Fin 3 → Bool) (t : ℝ) (z : ℂ) :
    localChamberFold s (coordinateSectionPoint (chamberCorner s) t 0)
      (coordinateSectionPoint (chamberCorner s) t z)=
        coordinateSectionPoint (chamberCorner s) t (complexFold z) := by
  ext i
  fin_cases i
  · simp only [localChamberFold_apply,coordinateSectionPoint_apply]
    split_ifs with h h <;> simp_all
  · simp [localChamberFold_apply,complexFold]
  · simp [localChamberFold_apply,complexFold]

lemma coordinateSectionPoint_mem_box {c : Cover} {t : ℝ} {z : ℂ}
    (ht : t∈Icc (c 0) (c 0+1/2)) (hz : 0≤z.re ∧ 0≤z.im ∧ z.re≤1/2 ∧ z.im≤1/2) :
    coordinateSectionPoint c t z∈closedHalfBox c := by
  intro i
  fin_cases i
  · simpa using ht
  · simp only [coordinateSectionPoint_apply]
    change c 1≤c 1+z.re ∧ c 1+z.re≤c 1+1/2
    constructor <;> linarith [hz.1,hz.2.2.1]
  · simp only [coordinateSectionPoint_apply]
    change c 2≤c 2+z.im ∧ c 2+z.im≤c 2+1/2
    constructor <;> linarith [hz.2.1,hz.2.2.2]

theorem isMinimizerAt_coordinate_plane_transverse {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {t : ℝ} {z : ℂ} (hz : z≠0) (hbox : complexSquareGauge z<1/2)
    (hb : quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈frontier (openRepresentative E)) :
    0<⟪N (coordinateSectionPoint (chamberCorner s) t z),coordinatePlaneLift z⟫ := by
  let x := coordinateSectionPoint (chamberCorner s) t z
  have hsign (i : Fin 3) (hi : i=1 ∨ i=2) (hn : x i≠chamberCorner s i) :
      0<N x i*(x i-chamberCorner s i) := by
    apply isMinimizerAt_centered_normal_product hV hE hm hμ hN hp ha hs hsg hb i _ hn
    rcases hi with rfl|rfl
    · simpa [x] using (le_max_left |z.re| |z.im|).trans_lt hbox
    · simpa [x] using (le_max_right |z.re| |z.im|).trans_lt hbox
  have h1 : z.re≠0 →0<N x 1*z.re := by
    intro hh
    simpa [x] using hsign 1 (Or.inl rfl) (by simpa [x] using hh)
  have h2 : z.im≠0 →0<N x 2*z.im := by
    intro hh
    simpa [x] using hsign 2 (Or.inr rfl) (by simpa [x] using hh)
  have hn1 : 0≤N x 1*z.re := by
    by_cases hh : z.re=0
    · simp [hh]
    · exact (h1 hh).le
  have hn2 : 0≤N x 2*z.im := by
    by_cases hh : z.im=0
    · simp [hh]
    · exact (h2 hh).le
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,Fin.sum_univ_three,coordinatePlaneLift_apply,
    Fin.reduceEq,ite_true,ite_false,zero_mul,zero_add]
  change 0<z.re*N x 1+z.im*N x 2
  by_cases hh : z.re=0
  · have hh' : z.im≠0 := by intro he; exact hz (Complex.ext hh he)
    nlinarith [h2 hh']
  · nlinarith [h1 hh]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

theorem continuous_path_exit {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    {F : Set X} (hF : IsOpen F) {γ : A → ℝ → X}
    (hγ : ∀ t,Continuous (fun a => γ a t)) {r : A → ℝ}
    (hr : ∀ a,r a∈Ioo (0 : ℝ) 1)
    (ho : ∀ a t,t∈Icc (0 : ℝ) 1 → (γ a t∈F ↔ t<r a))
    (hc : ∀ a t,t∈Icc (0 : ℝ) 1 → (γ a t∈closure F ↔ t≤r a)) :
    Continuous r := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_order.2
  constructor
  · intro q hq
    by_cases hq0 : q<0
    · exact Filter.Eventually.of_forall (fun b => hq0.trans (hr b).1)
    · have hqi : q∈Icc (0 : ℝ) 1 := ⟨le_of_not_gt hq0,hq.le.trans (hr a).2.le⟩
      have hh : γ a q∈F := (ho a q hqi).mpr hq
      filter_upwards [(hγ q).continuousAt.preimage_mem_nhds (hF.mem_nhds hh)] with b hb
      exact (ho b q hqi).mp hb
  · intro q hq
    by_cases hq1 : 1<q
    · exact Filter.Eventually.of_forall (fun b => (hr b).2.trans hq1)
    · have hqi : q∈Icc (0 : ℝ) 1 := ⟨(hr a).1.le.trans hq.le,le_of_not_gt hq1⟩
      have hh : γ a q∈(closure F)ᶜ := by
        intro hn
        exact (not_le.mpr hq) ((hc a q hqi).mp hn)
      filter_upwards [(hγ q).continuousAt.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hh)] with b hb
      exact lt_of_not_ge (fun hn => hb ((hc b q hqi).mpr hn))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_chamber_continuous_exit {A : Type*} [TopologicalSpace A]
    {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x y : A → Cover} (hxc : Continuous x) (hyc : Continuous y)
    (hx : ∀ a,x a∈closedHalfBox (chamberCorner s))
    (hy : ∀ a,y a∈closedHalfBox (chamberCorner s))
    (hxy : ∀ a i,x a i≤y a i)
    (hxE : ∀ a,quotientMap (x a)∈openRepresentative E)
    (hyE : ∀ a,quotientMap (y a)∉closure (openRepresentative E)) :
    ∃ r : A → ℝ,Continuous r ∧ (∀ a,r a∈Ioo (0 : ℝ) 1) ∧
      (∀ a,quotientMap (chamberSegment (x a) (y a) (r a))∈frontier (openRepresentative E)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈openRepresentative E ↔ t<r a)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈closure (openRepresentative E) ↔ t≤r a)) ∧
      ∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈frontier (openRepresentative E) ↔ t=r a) := by
  have hex := fun a => isMinimizerAt_chamber_unique_ray_exit hV hE hm hμ hN hp ha hs hsg
    (hx a) (hy a) (hxy a) (hxE a) (hyE a)
  choose r hr hb ho hc hf using hex
  refine ⟨r,?_,hr,hb,ho,hc,hf⟩
  apply continuous_path_exit (isOpen_openRepresentative E) _ hr ho hc
  intro t
  exact continuous_quotientMap.comp (hxc.add ((continuous_const (y := t)).smul (hyc.sub hxc)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSine_chamber_endpoint (s : Fin 3 → Bool) (x : Cover) (i : Fin 3)
    (hx : x i=chamberCorner s i ∨ x i=chamberCorner s i+1/2) :
    coordinateSine i (representative (quotientMap x))=0 := by
  rw [periodic_representative (coordinateSine_periodic i)]
  rcases hx with hx|hx
  all_goals cases hs : s i
  all_goals simp [coordinateSine,hx,chamberCorner,hs]
  all_goals ring_nf
  all_goals first | exact Real.sin_pi | exact Real.sin_two_pi | simpa [mul_comm] using Real.sin_two_pi

theorem isMinimizerAt_chamber_critical_interior {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool} (i : Fin 3) {x : Cover} (hx : x∈chamberAxialCritical E N s i) :
    chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2 := by
  have hnot : ¬(x i=chamberCorner s i ∨ x i=chamberCorner s i+1/2) := by
    intro hxend
    have hzi := isMinimizerAt_normal_coordinate_seam_zero hV hE hmE hμ hN hp hae i (hs i)
      hx.2.1 (coordinateSine_chamber_endpoint s x i hxend)
    rw [periodic_representative hp] at hzi
    have he : N x=0 := by
      ext j
      by_cases hj : j=i
      · subst j; exact hzi
      · exact hx.2.2 j hj
    have hu := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae x hx.2.1
    simp [he] at hu
  exact ⟨lt_of_le_of_ne (hx.1 i).1 (fun he => hnot (Or.inl he.symm)),
    lt_of_le_of_ne (hx.1 i).2 (fun he => hnot (Or.inr he))⟩

theorem isMinimizerAt_chamber_critical_collar {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (s : Fin 3 → Bool) (i : Fin 3) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈chamberAxialCritical E N s i,
      chamberCorner s i+δ≤x i ∧ x i≤chamberCorner s i+1/2-δ := by
  have hK := isCompact_chamberAxialCritical E hN.continuous s i
  by_cases hn : (chamberAxialCritical E N s i).Nonempty
  · obtain ⟨a,ha,hmin⟩ := hK.exists_isMinOn hn (PiLp.continuous_apply _ _ i).continuousOn
    obtain ⟨b,hb,hmax⟩ := hK.exists_isMaxOn hn (PiLp.continuous_apply _ _ i).continuousOn
    have ha' := isMinimizerAt_chamber_critical_interior hV hE hmE hμ hN hp hae hs i ha
    have hb' := isMinimizerAt_chamber_critical_interior hV hE hmE hμ hN hp hae hs i hb
    let δ := min (a i-chamberCorner s i) (chamberCorner s i+1/2-b i)
    have hδ : 0<δ := lt_min (sub_pos.mpr ha'.1) (sub_pos.mpr hb'.2)
    refine ⟨δ,hδ,?_⟩
    intro x hx
    have h1 : δ≤a i-chamberCorner s i := min_le_left _ _
    have h2 : δ≤chamberCorner s i+1/2-b i := min_le_right _ _
    have h3 := hmin hx
    have h4 := hmax hx
    dsimp at h3 h4
    constructor <;> linarith
  · exact ⟨1,by norm_num,fun x hx => (hn ⟨x,hx⟩).elim⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSine_zero_reflection_iff (i j : Fin 3) (a : Torus) :
    coordinateSine i (representative (coordinateReflection j a))=0 ↔
      coordinateSine i (representative a)=0 := by
  rw [← quotientMap_representative a,← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine,coverCoordinateReflection_apply]
  by_cases hij : i=j
  · simp [hij,Real.sin_neg,quotientMap_representative]
  · simp [hij,quotientMap_representative]

lemma chamber_endpoint_of_coordinateSine_zero (s : Fin 3 → Bool) {x : Cover}
    (hx : x∈closedHalfBox (chamberCorner s)) (i : Fin 3)
    (hz : coordinateSine i (representative (quotientMap x))=0) :
    x i=chamberCorner s i ∨ x i=chamberCorner s i+1/2 := by
  by_contra hn
  push Not at hn
  have hi : chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2 :=
    ⟨lt_of_le_of_ne (hx i).1 (Ne.symm hn.1),lt_of_le_of_ne (hx i).2 hn.2⟩
  have hh := mem_coordinateHalf_of_chamber_interval s x i hi
  cases hsi : s i
  · simp only [hsi,Bool.false_eq_true,ite_false] at hh
    rw [← coordinateReflection_preimage_half] at hh
    change coordinateReflection i (quotientMap x)∈coordinateHalf i 0 at hh
    rw [coordinateHalf_zero] at hh
    change coordinateSine i (representative (coordinateReflection i (quotientMap x)))<0 at hh
    rw [descent_coordinateSine_reflection,hz,neg_zero] at hh
    exact lt_irrefl _ hh
  · simp only [hsi,ite_true] at hh
    rw [coordinateHalf_zero] at hh
    change coordinateSine i (representative (quotientMap x))<0 at hh
    rw [hz] at hh
    exact lt_irrefl _ hh

lemma chamberFoldLift_seam_iff (s : Fin 3 → Bool) (a : Torus) (i : Fin 3) :
    coordinateSine i (representative (quotientMap (chamberFoldLift s a)))=0 ↔
      coordinateSine i (representative a)=0 := by
  apply chamberFoldLift_mem_iff (F := {a : Torus | coordinateSine i (representative a)=0})
  intro j
  ext a
  exact coordinateSine_zero_reflection_iff i j a

lemma isMinimizerAt_frontier_nonempty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    (frontier (openRepresentative E)).Nonempty := by
  let : ConnectedSpace Torus := quotientMap_surjective.connectedSpace continuous_quotientMap
  by_contra hn
  have hcl : IsClopen (openRepresentative E) :=
    isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
  rcases isClopen_iff.mp hcl with he|he
  · exact (isMinimizerAt_openRepresentative_nonempty hV hE hmE).ne_empty he
  · obtain ⟨a,ha⟩ := isMinimizerAt_vacant_nonempty hV hE hmE
    rw [he,closure_univ] at ha
    exact ha (mem_univ _)

theorem isMinimizerAt_boundary_meets_seam {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ a∈frontier (openRepresentative E),coordinateSine i (representative a)=0 := by
  obtain ⟨a,ha⟩ := isMinimizerAt_frontier_nonempty hV hE hmE
  let f : Torus → ℝ := fun a => coordinateSine i (representative a)
  have hf : Continuous f := continuous_periodic_descent (coordinateSine_contDiff i).continuous
    (coordinateSine_periodic i)
  have hra : coordinateReflection i a∈frontier (openRepresentative E) := by
    change a∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rw [frontier_reflection_invariant hE i hs]
    exact ha
  have he : f (coordinateReflection i a)= -f a := descent_coordinateSine_reflection i a
  by_cases hf0 : 0≤f a
  · exact hc.intermediate_value hra ha hf.continuousOn ⟨by rw [he]; linarith,hf0⟩
  · exact hc.intermediate_value ha hra hf.continuousOn ⟨(lt_of_not_ge hf0).le,by rw [he]; linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_no_face_vertex_pattern {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (i : Fin 3)
    (hface : quotientMap (chamberVertex s (fun j => decide (j≠i)))∈openRepresentative E)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    False := by
  obtain ⟨a,ha,hzero⟩ := isMinimizerAt_boundary_meets_seam hV hE hmE hc i (hs i)
  let x := chamberFoldLift s a
  have hx : x∈closedHalfBox (chamberCorner s) := chamberFoldLift_mem s a
  have hxb : quotientMap x∈frontier (openRepresentative E) :=
    (chamberFoldLift_mem_iff (fun j => frontier_reflection_invariant hE j (hs j)) s a).mpr ha
  have hxzero : coordinateSine i (representative (quotientMap x))=0 :=
    (chamberFoldLift_seam_iff s a i).mpr hzero
  rcases chamber_endpoint_of_coordinateSine_zero s hx i hxzero with he|he
  · have hxE : quotientMap x∈openRepresentative E :=
      isMinimizerAt_chamber_open_downset hV hE hmE hμ hae hsg hs hx (chamberVertex_mem s _) (by
        intro j
        by_cases hj : j=i
        · subst j
          simp [chamberVertex,he]
        · simpa [chamberVertex,hj] using (hx j).2) hface
    rw [frontier,(isOpen_openRepresentative E).interior_eq] at hxb
    exact hxb.2 hxE
  · exact isMinimizerAt_vacant_face hV hE hmE hμ hae hsg hs i hv hx he
      (frontier_subset_closure hxb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_periodic_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) (hm : (∫ t in (0 : ℝ)..1,f t)=0) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧ deriv g=f := by
  let g : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x,f t
  have hd (x : ℝ) : HasDerivAt g (f x) x := (hf.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have he : deriv g=f := funext fun x => (hd x).deriv
  refine ⟨g,contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt,by rw [he]; exact hf⟩,?_,he⟩
  intro x
  change (∫ t in (0 : ℝ)..x+1,f t)=(∫ t in (0 : ℝ)..x,f t)
  rw [hp.intervalIntegral_add_eq_add 0 x (fun a b => hf.continuous.intervalIntegrable a b)]
  simp only [zero_add,hm,add_zero]

lemma periodic_normalized_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f 1) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      ∀ t,deriv g t=f t-(∫ u in (0 : ℝ)..1,f u) := by
  let c := ∫ u in (0 : ℝ)..1,f u
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun t => f t-c) := hf.sub contDiff_const
  have hpc : Function.Periodic (fun t => f t-c) 1 := fun t => by dsimp only; rw [hp t]
  have hzero : (∫ t in (0 : ℝ)..1,f t-c)=0 := by
    rw [intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _) intervalIntegrable_const]
    simp [c]
  obtain ⟨g,hg,hpg,hdg⟩ := exists_periodic_primitive hfc hpc hzero
  exact ⟨g,hg,hpg,fun t => congrFun hdg t⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fderiv_axial_function (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x v : Cover) :
    fderiv ℝ (fun y : Cover => f (y i)) x v=deriv f (x i)*v i := by
  have hd := (hf (x i)).hasDerivAt.comp_hasFDerivAt x
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt
  simpa [Function.comp_def] using congrArg (fun L : Cover →L[ℝ] ℝ => L v) hd.fderiv

lemma axial_function_periodic (i : Fin 3) {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa [latticeVector] using hp.int_mul (m i) (x i)

lemma tangentialDivergence_axial (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x n : Cover) :
    tangentialDivergence (fun y : Cover => f (y i) • (EuclideanSpace.single i 1 : Cover)) x n=
      deriv f (x i)*(1-(n i)^2) := by
  have hc : Differentiable ℝ (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiable
  rw [tangentialDivergence_smul_const hc.differentiableAt,fderiv_axial_function i hf]
  congr 1
  simp [tangentPart,PiLp.inner_apply,EuclideanSpace.single,pow_two]

lemma divergence_axial (i : Fin 3) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Cover) :
    divergence (fun y : Cover => f (y i) • (EuclideanSpace.single i 1 : Cover)) x=deriv f (x i) := by
  have hc : Differentiable ℝ (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).differentiable
  rw [divergence_smul_const hc.differentiableAt,fderiv_axial_function i hf]
  simp [EuclideanSpace.single]

theorem axial_flux_derivative {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ z,deriv f (z.1.1 i)*(1-((z.2 : Cover) i)^2) ∂(μ : Measure NormalBundle))=
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,deriv f (x i)) := by
  let F : Cover → Cover := fun y => f (y i) • EuclideanSpace.single i 1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff).smul contDiff_const
  have hpF : ∀ m x,F (x+latticeVector m)=F x := by
    intro m x
    exact congrArg (fun t : ℝ => t • (EuclideanSpace.single i 1 : Cover))
      (axial_function_periodic i hp m x)
  have he := Periodic.tangent_firstVariation_of_coordinate hH hF hpF
  simpa only [F,tangentialDivergence_axial i (hf.differentiable (by simp)),
    divergence_axial i (hf.differentiable (by simp))] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialNormalWeight (i : Fin 3) (z : NormalBundle) : ℝ := 1-((z.2 : Cover) i)^2

lemma continuous_axialNormalWeight (i : Fin 3) : Continuous (axialNormalWeight i) :=
  continuous_const.sub (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    continuous_normalUnit).pow 2)

lemma integrable_axialNormalWeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialNormalWeight i) (μ : Measure NormalBundle) :=
  (continuous_axialNormalWeight i).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem axial_flux_moment {E : Set Torus} {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ z,f (z.1.1 i)*axialNormalWeight i z ∂(μ : Measure NormalBundle))=
      H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))+
      (∫ u in (0 : ℝ)..1,f u)*
        ((∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))-
          H*volume.real (fundamentalCube∩quotientMap ⁻¹' E)) := by
  obtain ⟨g,hg,hpg,hdg⟩ := periodic_normalized_primitive hf hp
  have hh := axial_flux_derivative hH i hg hpg
  simp_rw [hdg,sub_mul] at hh
  have hfbase : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
  have hifi : Integrable (fun z : NormalBundle => f (z.1.1 i)*axialNormalWeight i z)
      (μ : Measure NormalBundle) :=
    (hfbase.mul (continuous_axialNormalWeight i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨M,_,hM⟩ := periodic_bounded
    (hf.continuous.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous)
    (axial_function_periodic i hp)
  have hif : Integrable (fun x : Cover => f (x i))
      (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)) :=
    Integrable.of_bound (hf.continuous.comp
      (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous).aestronglyMeasurable M
      (Eventually.of_forall hM)
  change (∫ z,f (z.1.1 i)*axialNormalWeight i z-
    (∫ u in (0 : ℝ)..1,f u)*axialNormalWeight i z ∂(μ : Measure NormalBundle))=
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i)-(∫ u in (0 : ℝ)..1,f u)) at hh
  rw [integral_sub hifi ((integrable_axialNormalWeight μ i).const_mul _),integral_const_mul,
    integral_sub hif (integrable_const _),integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hh
  linarith

theorem isMinimizerAt_axial_flux_moments {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      ∀ (i : Fin 3) (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → Function.Periodic f 1 →
      (∫ z,f (z.1.1 i)*axialNormalWeight i z ∂(μ : Measure NormalBundle))=
        H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))+
        (∫ u in (0 : ℝ)..1,f u)*
          ((∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))-H*V) := by
  obtain ⟨μ,H,hμ,hH,_⟩ := Periodic.isMinimizerAt_stable_periodic hV hE hmE
  refine ⟨μ,H,hμ,fun i f hf hp => ?_⟩
  have he := axial_flux_moment hH i hf hp
  have hvol : volume.real (fundamentalCube∩quotientMap ⁻¹' E)=V := by
    rw [← realVolume_lift hE,Measure.real,hmE.2.1,ENNReal.toReal_ofReal hV.1.le]
  simpa only [hvol] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialNormalWeight_nonneg (i : Fin 3) (z : NormalBundle) :
    0≤axialNormalWeight i z := by
  have hb := PiLp.norm_apply_le (x := (z.2 : Cover)) i
  have hn : ‖(z.2 : Cover)‖=1 := z.2.property
  rw [hn,Real.norm_eq_abs] at hb
  dsimp [axialNormalWeight]
  have hs := sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (by norm_num : (0 : ℝ)≤1) |>.mpr hb
  rw [sq_abs,one_pow] at hs
  linarith

lemma axialNormalWeight_le_one (i : Fin 3) (z : NormalBundle) :
    axialNormalWeight i z≤1 := by
  dsimp [axialNormalWeight]
  nlinarith [sq_nonneg ((z.2 : Cover) i)]

lemma sum_axialNormalWeight (z : NormalBundle) :
    (∑ i : Fin 3,axialNormalWeight i z)=2 := by
  have hn : (∑ i : Fin 3,((z.2 : Cover) i)^2)=1 := by
    rw [← EuclideanSpace.real_norm_sq_eq,z.2.property,one_pow]
  calc
    (∑ i : Fin 3,axialNormalWeight i z) = 3-∑ i : Fin 3,((z.2 : Cover) i)^2 := by
      simp only [axialNormalWeight,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one]
    _=2 := by rw [hn]; norm_num

def axialFluxWeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) : ℝ :=
  (∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))/(μ.mass : ℝ)

lemma axialFluxWeight_nonneg (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    0≤axialFluxWeight μ i := by
  exact div_nonneg (integral_nonneg (axialNormalWeight_nonneg i)) μ.mass.coe_nonneg

lemma axialFluxWeight_le_one (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    (hm : 0<(μ.mass : ℝ)) : axialFluxWeight μ i≤1 := by
  rw [axialFluxWeight,div_le_one hm]
  calc
    _≤(∫ _ : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle)) :=
      integral_mono (integrable_axialNormalWeight μ i) (integrable_const _) (axialNormalWeight_le_one i)
    _=(μ.mass : ℝ) := normalMeasure_integral_one μ

lemma sum_axialFluxWeight (μ : FiniteMeasure NormalBundle) (hm : (μ.mass : ℝ)≠0) :
    (∑ i : Fin 3,axialFluxWeight μ i)=2 := by
  simp only [axialFluxWeight,← Finset.sum_div]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_axialNormalWeight μ i)]
  simp_rw [sum_axialNormalWeight]
  have he : (∫ _ : NormalBundle,(2 : ℝ) ∂(μ : Measure NormalBundle))=2*(μ.mass : ℝ) := by
    rw [show (fun _ : NormalBundle => (2 : ℝ))=(fun _ => 2*(1 : ℝ)) from by funext z; ring,
      integral_const_mul,normalMeasure_integral_one]
  rw [he,mul_div_cancel_right₀ _ hm]

theorem axialFluxWeight_lt_one_iff {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hm : 0<(μ.mass : ℝ)) (i : Fin 3) :
    axialFluxWeight μ i<1 ↔ ∃ a∈frontier (openRepresentative E),N (representative a) i≠0 := by
  have hc : Continuous (fun z : NormalBundle => ((z.2 : Cover) i)^2) :=
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2)
  have hi : Integrable (fun z : NormalBundle => ((z.2 : Cover) i)^2) (μ : Measure NormalBundle) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : (∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))=
      (μ.mass : ℝ)-(∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)) := by
    change (∫ z,1-((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle))=_
    rw [integral_sub (integrable_const _) hi,normalMeasure_integral_one]
  have hiff : axialFluxWeight μ i<1 ↔
      0<(∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)) := by
    rw [axialFluxWeight,div_lt_one hm,hid]
    constructor <;> intro hh <;> linarith
  rw [hiff]
  constructor
  · intro hpos
    by_contra hn
    push Not at hn
    have hb := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
      (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmE).symm)
    have hzero : (∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle))=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hb,hae] with z hzb hzn
      have hh := hn (quotientMap z.1) hzb
      rw [periodic_representative hp,hzn] at hh
      simp only [hh,zero_pow (by norm_num : (2 : ℕ)≠0),Pi.zero_apply]
    linarith
  · rintro ⟨a,ha,hna⟩
    have hnn : 0≤(∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)) :=
      integral_nonneg (fun z : NormalBundle => sq_nonneg ((z.2 : Cover) i))
    apply lt_of_le_of_ne hnn
    intro he
    have hz := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle => sq_nonneg ((z.2 : Cover) i)) hi).mp he.symm
    have hn0 : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1 i=(0 : ℝ) := by
      filter_upwards [hae,hz] with z hzn hzz
      rw [hzn]
      exact sq_eq_zero_iff.mp hzz
    have hh := isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp hN) continuous_const
      (fun m x => congrArg (fun v : Cover => v i) (hp m x)) (fun _ _ => rfl) hn0
      (representative a) (by rwa [quotientMap_representative])
    exact hna hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

def scalarMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((n : ℝ)+1)
  rOut := 2/((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma scalarMollifier_tendsto : Tendsto (fun n => (scalarMollifier n).rOut) atTop (𝓝 0) := by
  simpa only [scalarMollifier,mul_one,mul_div,mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def scalarMollification (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (scalarMollifier n).normed volume ⋆ f

lemma scalarMollification_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarMollification f n) :=
  (scalarMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scalarMollifier n).contDiff_normed hf.locallyIntegrable

lemma scalarMollification_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (scalarMollification f n) 1 := by
  intro x
  simp only [scalarMollification,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x+1-y=(x-y)+1 by ring,hp]

lemma scalarMollification_bound {f : ℝ → ℝ} {M : ℝ} (hb : ∀ x,‖f x‖≤M) (n : ℕ) (x : ℝ) :
    ‖scalarMollification f n x‖≤M := by
  rw [scalarMollification,convolution_def]
  calc
    _≤∫ y : ℝ,(scalarMollifier n).normed volume y*M := by
      apply norm_integral_le_of_norm_le ((scalarMollifier n).integrable_normed.mul_const M)
      exact Eventually.of_forall fun y => by
        rw [ContinuousLinearMap.lsmul_apply,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg ((scalarMollifier n).nonneg_normed y)]
        exact mul_le_mul_of_nonneg_left (hb (x-y)) ((scalarMollifier n).nonneg_normed y)
    _=M := by rw [integral_mul_const,(scalarMollifier n).integral_normed,one_mul]

lemma scalarMollification_tendsto {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n => scalarMollification f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous scalarMollifier_tendsto hf x

theorem circle_measure_ext_smooth {μ ν : Measure (AddCircle (1 : ℝ))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ x,hp.lift x ∂μ)=(∫ x,hp.lift x ∂ν)) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let f : ℝ → ℝ := fun t => g (t : AddCircle (1 : ℝ))
  have hf : Continuous f := g.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hp : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    congr 1
    simp
  obtain ⟨M,hM0,hM⟩ := (isCompact_univ.image g.continuous).isBounded.exists_pos_norm_le
  have hfb (x : ℝ) : ‖f x‖≤M := hM _ ⟨(x : AddCircle (1 : ℝ)),mem_univ _,rfl⟩
  let F (n : ℕ) : AddCircle (1 : ℝ) → ℝ := (scalarMollification_periodic hp n).lift
  have hcF (n : ℕ) : Continuous (F n) := continuous_periodic_lift
    (scalarMollification_periodic hp n) (scalarMollification_contDiff hf n).continuous
  have hbF (n : ℕ) (x : AddCircle (1 : ℝ)) : ‖F n x‖≤M := by
    induction x using QuotientAddGroup.induction_on with | H t =>
      exact scalarMollification_bound hfb n t
  have htF (x : AddCircle (1 : ℝ)) : Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    induction x using QuotientAddGroup.induction_on with | H t =>
      exact scalarMollification_tendsto hf t
  have hlim (ρ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure ρ] :
      Tendsto (fun n => ∫ x,F n x ∂ρ) atTop (𝓝 (∫ x,g x ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (hcF n).aestronglyMeasurable) (integrable_const M)
      (fun n => Eventually.of_forall (hbF n)) (Eventually.of_forall htF)
  apply tendsto_nhds_unique (hlim μ)
  convert hlim ν using 1
  funext n
  exact he _ (scalarMollification_contDiff hf n) (scalarMollification_periodic hp n)

end CubicTorus

end
end

end OAI
