import Mathlib
import OAI.Geometry.CubicTorus.Estimates.MinimizerLevelSliceIsoperimetric

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstTransition_mem_Ioo_half : 4*Real.pi/81∈Ioo (0 : ℝ) (1/2) := by
  constructor
  · positivity
  · linarith [Real.pi_lt_four]

theorem isMinimizerAt_first_transition_corner_excluded
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (4*Real.pi/81) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hw : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  obtain ⟨hA,hAc,_,hh,hr0,hrV,_,hs1,hb0,_,ht,hb,hd⟩ :=
    isMinimizerAt_four_corner_necessary_data firstTransition_mem_Ioo_half hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  have hrad : Real.sqrt (Real.pi*(4*Real.pi/81))=2*Real.pi/9 := by
    have hsqrt := Real.sq_sqrt (show 0≤Real.pi*(4*Real.pi/81) by positivity)
    have hnon := Real.sqrt_nonneg (Real.pi*(4*Real.pi/81))
    have hp := Real.pi_pos
    nlinarith only [hsqrt,hnon,hp]
  rw [hrad] at hAc
  exact firstCorner_endpoint_contradiction hA hAc hh hb0 hw hr0 hrV hs1 ht hb hd

theorem isMinimizerAt_first_transition_nonstandard_corner_restriction
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (v : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
      (c : Fin 3 → Bool) (H : ℝ),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧ IsMinimizerAt (4*Real.pi/81) F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (i : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∀ i : Fin 3,axialFluxWeight μ i<1) ∧
      ¬(quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative F ∧
        quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative F ∧
        quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative F ∧
        quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative F) := by
  obtain ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,_,_,hw,_⟩ :=
    isMinimizerAt_nonstandard_section_system
      ⟨firstTransition_mem_Ioo_half.1,firstTransition_mem_Ioo_half.2.le⟩ hmE hnstd
  refine ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,fun i => (hw i).2,?_⟩
  rintro ⟨ht1,ht2,hb1,hb2⟩
  exact isMinimizerAt_first_transition_corner_excluded hF hm hμ hN hp ha hs hsg hH (hw 0).2 ht1 ht2 hb1 hb2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_first_transition_permuted_corner_excluded
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (4*Real.pi/81) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw : ∀ i,axialFluxWeight μ i<1) (e : Fin 3 ≃ Fin 3)
    (ht1 : quotientMap (chamberVertex c ((fun j => decide (j=0 ∨ j=1)) ∘ e))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c ((fun j => decide (j=0 ∨ j=2)) ∘ e))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c ((fun j => decide (j=1)) ∘ e))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c ((fun j => decide (j=2)) ∘ e))∈openRepresentative E) : False := by
  have hF := (torusCoordinatePermute e).continuous.measurable hE
  have hmF := isMinimizerAt_coordinatePermute hm e
  have hμF := isNormalMeasure_coordinatePermute hE hμ e
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier
    ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩ hF hmF hμF
  have hv (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' E) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative E := by
    rw [openRepresentative_coordinatePermute hE e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative E ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  apply isMinimizerAt_first_transition_corner_excluded hF hmF hμF
    (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
    (permuted_normal_ae hN.continuous hp ha e) (reflection_invariant_coordinatePermute hs e)
    (chamberSign_coordinatePermute hE hsg e) hH
  · rw [axialFluxWeight_permute]
    exact hw _
  · rwa [hv]
  · rwa [hv]
  · rwa [hv]
  · rwa [hv]

theorem isMinimizerAt_first_transition_any_corner_excluded
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (4*Real.pi/81) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (hw : ∀ i,axialFluxWeight μ i<1) (i : Fin 3)
    (ht : ∀ j : Fin 3,j≠i → quotientMap (chamberVertex c (fun k => decide (k=i ∨ k=j)))∉openRepresentative E)
    (hb : ∀ j : Fin 3,j≠i → quotientMap (chamberVertex c (fun k => decide (k=j)))∈openRepresentative E) : False := by
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have he1 : e.symm 1≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have he2 : e.symm 2≠i := by rw [← he0]; exact e.symm.injective.ne (by decide)
  have hpair (j : Fin 3) : ((fun k : Fin 3 => decide (k=0 ∨ k=j)) ∘ e)=
      (fun k => decide (k=i ∨ k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply,he0]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  apply isMinimizerAt_first_transition_permuted_corner_excluded hE hm hμ hN hp ha hs hsg hw e
  · rw [hpair]; exact ht _ he1
  · rw [hpair]; exact ht _ he2
  · rw [hsingle]; exact hb _ he1
  · rw [hsingle]; exact hb _ he2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smaller_side_double_vertices_vacant
    {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    quotientMap (chamberVertex c (fun j => decide (j≠i)))∉closure (openRepresentative E) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  apply isMinimizerAt_vertex_vacant_of_not_occupied hV' hE hm hμ hN hp ha hs
  intro hi
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV'.2],by linarith [hV'.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV'.1.le,hV'.2.le⟩).mpr hm
  have hμc := isNormalMeasure_compl hE hμ
  have hpc : ∀ m x,(-N) (x+latticeVector m)=(-N) x := fun m x => by simp only [Pi.neg_apply,hp]
  have hac := normal_reverse_ae hN.continuous hp ha
  have hsc := reflection_symmetry_compl hs
  have hsgc := isMinimizerAt_complement_chamber_sign hV' hE hm hμ hN hp ha hs hsg
  have hHc := complement_firstVariation_same_multiplier hE hμ hH
  have hv : quotientMap (chamberVertex (fun j => !(c j)) (fun j => decide (j=i)))∉openRepresentative Eᶜ := by
    rw [quotientMap_chamberVertex_complement,isMinimizerAt_openRepresentative_compl hV' hE hm]
    have hb : (fun j : Fin 3 => !(decide (j=i)))=(fun j => decide (j≠i)) := by
      funext j; simp
    rw [hb]
    exact fun h => h (subset_closure hi)
  have hv' := isMinimizerAt_vertex_vacant_of_not_occupied hVc hE.compl hmc hμc hN.neg hpc hac hsc _ _ hv
  have hneg := (isMinimizerAt_missing_axis_flux hVc hE.compl hmc hμc hN.neg hpc hac hsc hsgc hHc i hv').1
  have hpos := isMinimizerAt_coordinate_multiplier_nonneg hV hE hm hμ hH
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fin3_pair_complement (i j : Fin 3) (hij : i≠j) :
    ∃ k : Fin 3,(fun x : Fin 3 => decide (x=i ∨ x=j))=(fun x => decide (x≠k)) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact ⟨0,by decide⟩ | exact ⟨1,by decide⟩ | exact ⟨2,by decide⟩

theorem isMinimizerAt_first_transition_atMostOne_axis
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (4*Real.pi/81) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hw : ∀ i,axialFluxWeight μ i<1) :
    ∀ i j : Fin 3,
      quotientMap (chamberVertex c (fun k => decide (k=i)))∈openRepresentative E →
      quotientMap (chamberVertex c (fun k => decide (k=j)))∈openRepresentative E →i=j := by
  intro i j hi hj
  by_contra hij
  have hdouble := isMinimizerAt_smaller_side_double_vertices_vacant
    firstTransition_mem_Ioo_half hE hm hμ hN hp ha hs hsg hH
  have hpairs (a b : Fin 3) (hab : a≠b) :
      quotientMap (chamberVertex c (fun k => decide (k=a ∨ k=b)))∉openRepresentative E := by
    obtain ⟨k,hk⟩ := fin3_pair_complement a b hab
    rw [hk]
    exact fun h => hdouble k (subset_closure h)
  obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3,k≠i ∧ k≠j := by
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩ | exact ⟨2,by decide,by decide⟩
  apply isMinimizerAt_first_transition_any_corner_excluded hE hm hμ hN hp ha hs hsg hw k
  · intro l hl
    exact hpairs k l hl.symm
  · intro l hl
    have hli : l=i ∨ l=j := by omega
    rcases hli with rfl|rfl
    · exact hi
    · exact hj

lemma bool_vertex_two_point_ideal {O : (Fin 3 → Bool) → Prop}
    (hzero : O (fun _ => false))
    (hdown : ∀ b d : Fin 3 → Bool,b≤d → O d → O b)
    (i : Fin 3) (hi : O (fun j => decide (j=i)))
    (hu : ∀ j : Fin 3,O (fun k => decide (k=j)) → j=i) :
    ∀ b : Fin 3 → Bool,O b ↔ b=(fun _ => false) ∨ b=(fun j => decide (j=i)) := by
  classical
  intro b
  constructor
  · intro hb
    have hz (j : Fin 3) (hji : j≠i) : b j=false := by
      cases hbj : b j
      · rfl
      · exfalso
        apply hji
        apply hu j
        apply hdown _ b _ hb
        intro k
        by_cases hkj : k=j
        · subst k
          simp [hbj]
        · simp [hkj]
    cases hbi : b i
    · left
      funext j
      by_cases hji : j=i
      · simpa only [hji] using hbi
      · exact hz j hji
    · right
      funext j
      by_cases hji : j=i
      · simp [hji,hbi]
      · simp [hji,hz j hji]
  · rintro (rfl|rfl)
    · exact hzero
    · exact hi

theorem isMinimizerAt_first_transition_nonstandard_two_vertices
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (v : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
      (c : Fin 3 → Bool) (H : ℝ) (i : Fin 3),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧ IsMinimizerAt (4*Real.pi/81) F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ j : Fin 3,coordinateReflection j ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (j : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∀ j : Fin 3,axialFluxWeight μ j<1) ∧
      (∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative F ↔
        b=(fun _ => false) ∨ b=(fun j => decide (j=i))) := by
  have hV : 4*Real.pi/81∈Ioo (0 : ℝ) 1 :=
    ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,_,_,hw,hvi,_⟩ :=
    isMinimizerAt_nonstandard_section_system
      ⟨firstTransition_mem_Ioo_half.1,firstTransition_mem_Ioo_half.2.le⟩ hmE hnstd
  obtain ⟨i,hi⟩ := hvi
  have hiO : quotientMap (chamberVertex c (fun j => decide (j=i)))∈openRepresentative F :=
    mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative F) hi
      (isMinimizerAt_reflection_vertex_excluded hV hF hm hμ hN hp ha hs
        (chamberVertex_sine_zero c _))
  obtain ⟨hzero,_,hdown⟩ := isMinimizerAt_chamber_vertex_order hV hF hm hμ ha
    (fun x hx j => (hsg x j ⟨hx.1,mem_iInter.mp hx.2 j⟩).le) hs
  have hu := isMinimizerAt_first_transition_atMostOne_axis hF hm hμ hN hp ha hs hsg hH (fun j => (hw j).2)
  refine ⟨v,F,μ,N,hN,hp,c,H,i,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,fun j => (hw j).2,?_⟩
  exact bool_vertex_two_point_ideal hzero hdown i hiO (fun j hj => hu j i hj hiO)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSectionPoint_continuous_pair (c : Cover) :
    Continuous (fun p : ℝ × ℂ => coordinateSectionPoint c p.1 p.2) := by
  unfold coordinateSectionPoint
  fun_prop

theorem isMinimizerAt_tubular_sections {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv0 : quotientMap (chamberVertex s (fun j => decide (j=0)))∈openRepresentative E)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E)) :
    ∃ r : (Icc (chamberCorner s 0) (chamberCorner s 0+1/2)) × ℝ → ℝ,
      Continuous r ∧
      (∀ t,ContDiff ℝ (⊤ : ℕ∞) (fun a => r (t,a))) ∧
      (∀ t,Function.Periodic (fun a => r (t,a)) 1) ∧
      (∀ p,0<r p ∧ r p<unitSquareScale p.2) ∧
      (∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
          (u • unitAngle p.2))∈openRepresentative E ↔ u<r p)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
          (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p)) := by
  let T := Icc (chamberCorner s 0) (chamberCorner s 0+1/2)
  have hsgc : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i := by
    intro x hx i
    exact (hsg x i ⟨hx.1,mem_iInter.mp hx.2 i⟩).le
  have hcenter (t : T) : quotientMap (coordinateSectionPoint (chamberCorner s) t.val 0)∈openRepresentative E := by
    apply isMinimizerAt_chamber_open_downset hV hE hm hμ ha hsgc hs
      (coordinateSectionPoint_mem_box t.property (by norm_num)) (chamberVertex_mem s _) _ hv0
    intro i
    fin_cases i
    · simpa [chamberVertex] using t.property.2
    · simp [chamberVertex]
    · simp [chamberVertex]
  have hex (t : T) := isMinimizerAt_smooth_radial_section hV hE hm hμ hN hp ha hs hsg hv1 hv2 t.property (hcenter t)
  choose r hrsm hrper hrpos hrbd hrop hrcl using hex
  let q : T × ℝ → ℝ := fun p => r p.1 p.2/unitSquareScale p.2
  have hqpos (p : T × ℝ) : q p∈Ioo (0 : ℝ) 1 :=
    ⟨div_pos (hrpos p.1 p.2).1 (unitSquareScale_pos p.2),
      (div_lt_one (unitSquareScale_pos p.2)).mpr (hrpos p.1 p.2).2⟩
  have hqc : Continuous q := by
    refine continuous_path_exit (isOpen_openRepresentative E)
      (γ := fun p u => quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        ((u*unitSquareScale p.2) • unitAngle p.2))) ?_ hqpos ?_ ?_
    · intro u
      apply continuous_quotientMap.comp
      exact (coordinateSectionPoint_continuous_pair (chamberCorner s)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          ((continuous_const.mul (unitSquareScale_continuous.comp continuous_snd)).smul
            ((unitAngle_contDiff.continuous).comp continuous_snd)))
    · intro p u hu
      rw [hrop p.1 p.2 (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (lt_div_iff₀ (unitSquareScale_pos p.2)).symm
    · intro p u hu
      rw [hrcl p.1 p.2 (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (le_div_iff₀ (unitSquareScale_pos p.2)).symm
  refine ⟨fun p => r p.1 p.2,?_,hrsm,hrper,fun p => hrpos p.1 p.2,
    fun p => hrbd p.1 p.2,fun p => hrop p.1 p.2,fun p => hrcl p.1 p.2⟩
  have he : (fun p : T × ℝ => r p.1 p.2)=fun p => q p*unitSquareScale p.2 := by
    funext p
    dsimp only [q]
    rw [div_mul_cancel₀ _ (unitSquareScale_pos p.2).ne']
  rw [he]
  exact hqc.mul (unitSquareScale_continuous.comp continuous_snd)

theorem tubular_radius_uniform {c : ℝ}
    {r : (Icc c (c+1/2)) × ℝ → ℝ} (hrc : Continuous r)
    (hr : ∀ p,0<r p ∧ r p<unitSquareScale p.2) :
    ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
      ε≤r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  let K := (Icc c (c+1/2)) × (Icc (0 : ℝ) 1)
  let g : K → ℝ := fun p => min (r (p.1,p.2.val))
    (unitSquareScale p.2.val-r (p.1,p.2.val))
  have hgc : Continuous g := by
    have hc : Continuous (fun p : K => r (p.1,p.2.val)) :=
      hrc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hc.min ((unitSquareScale_continuous.comp (continuous_subtype_val.comp continuous_snd)).sub hc)
  have hgp (p : K) : 0<g p := lt_min (hr _).1 (sub_pos.mpr (hr _).2)
  have hn : (univ : Set K).Nonempty :=
    ⟨(⟨c,by constructor <;> linarith⟩,⟨0,by norm_num⟩),mem_univ _⟩
  obtain ⟨p,_,hmin⟩ := isCompact_univ.exists_isMinOn hn hgc.continuousOn
  refine ⟨g p,hgp p,?_⟩
  intro t a ha
  have hh := hmin (show (t,⟨a,ha⟩)∈(univ : Set K) from mem_univ _)
  change g p ≤ min (r (t,a)) (unitSquareScale a-r (t,a)) at hh
  obtain ⟨h1,h2⟩ := le_min_iff.mp hh
  exact ⟨h1,by linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_coordinateSectionPoint_int (c : Cover) (t : ℝ) (z : ℂ) (n : ℤ) :
    quotientMap (coordinateSectionPoint c (t+(n : ℝ)) z)=
      quotientMap (coordinateSectionPoint c t z) := by
  have he : coordinateSectionPoint c (t+(n : ℝ)) z=
      coordinateSectionPoint c t z+latticeVector (Pi.single 0 n) := by
    ext i
    fin_cases i <;> simp [latticeVector]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma coordinateSectionPoint_fold_axis (s : Fin 3 → Bool) (t : ℝ) :
    ∃ τ∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2),
      ∀ (F : Set Torus),coordinateReflection 0 ⁻¹' F=F → ∀ z : ℂ,
        (quotientMap (coordinateSectionPoint (chamberCorner s) τ z)∈F ↔
          quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈F) := by
  let n : ℤ := ⌊t-chamberCorner s 0+1/2⌋
  let w := t-(n : ℝ)
  let τ := chamberCorner s 0+|w-chamberCorner s 0|
  have hl := Int.floor_le (t-chamberCorner s 0+1/2)
  have hu := Int.lt_floor_add_one (t-chamberCorner s 0+1/2)
  have hw : |w-chamberCorner s 0|≤1/2 := by
    dsimp only [w,n]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine ⟨τ,⟨by dsimp [τ]; exact le_add_of_nonneg_right (abs_nonneg _),by dsimp [τ]; linarith⟩,?_⟩
  intro F hF z
  have hbase : ∃ k : ℤ,2*chamberCorner s 0=(k : ℝ) := by
    cases hh : s 0
    · exact ⟨0,by simp [chamberCorner,hh]⟩
    · exact ⟨1,by simp [chamberCorner,hh]⟩
  have he : coordinateSectionPoint (chamberCorner s) τ z=
      foldCoordinate 0 (chamberCorner s 0) false
        (coordinateSectionPoint (chamberCorner s) w z) := by
    ext i
    fin_cases i <;> simp [foldCoordinate_apply,τ]
  have hwq : quotientMap (coordinateSectionPoint (chamberCorner s) w z)=
      quotientMap (coordinateSectionPoint (chamberCorner s) t z) := by
    simpa only [w,Int.cast_neg,sub_eq_add_neg] using
      quotientMap_coordinateSectionPoint_int (chamberCorner s) t z (-n)
  rcases foldCoordinate_quotient_alternative 0 false hbase
    (coordinateSectionPoint (chamberCorner s) w z) with hh|hh
  · rw [he,hh,hwq]
  · rw [he,hh,hwq]
    change quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈coordinateReflection 0 ⁻¹' F ↔ _
    rw [hF]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_radial_phase {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hrpos : ∀ p,0<r p ∧ r p<unitSquareScale p.2)
    (hrop : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint c p.1 (u • unitAngle p.2))∈openRepresentative E ↔ u<r p))
    (hrcl : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint c p.1 (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p)) :
    Continuous r := by
  let q : ℝ × ℝ → ℝ := fun p => r p/unitSquareScale p.2
  have hqc : Continuous q := by
    refine continuous_path_exit (isOpen_openRepresentative E)
      (γ := fun p u => quotientMap (coordinateSectionPoint c p.1
        ((u*unitSquareScale p.2) • unitAngle p.2))) ?_ ?_ ?_ ?_
    · intro u
      exact continuous_quotientMap.comp ((coordinateSectionPoint_continuous_pair c).comp
        (continuous_fst.prodMk
          ((continuous_const.mul (unitSquareScale_continuous.comp continuous_snd)).smul
            (unitAngle_contDiff.continuous.comp continuous_snd))))
    · intro p
      exact ⟨div_pos (hrpos p).1 (unitSquareScale_pos p.2),
        (div_lt_one (unitSquareScale_pos p.2)).mpr (hrpos p).2⟩
    · intro p u hu
      rw [hrop p (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (lt_div_iff₀ (unitSquareScale_pos p.2)).symm
    · intro p u hu
      rw [hrcl p (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (le_div_iff₀ (unitSquareScale_pos p.2)).symm
  have he : r=fun p => q p*unitSquareScale p.2 := by
    funext p
    dsimp only [q]
    rw [div_mul_cancel₀ _ (unitSquareScale_pos p.2).ne']
  rw [he]
  exact hqc.mul (unitSquareScale_continuous.comp continuous_snd)

theorem isMinimizerAt_contDiff_tube_radius {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r : ℝ × ℝ → ℝ} (hrc : Continuous r)
    (hrpos : ∀ p,0<r p ∧ r p<unitSquareScale p.2)
    (hrbd : ∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
      (r p • unitAngle p.2))∈frontier (openRepresentative E)) :
    ContDiff ℝ (⊤ : ℕ∞) r := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let γ : (ℝ × ℝ) × ℝ → Cover := fun b =>
    coordinateSectionPoint (chamberCorner s) b.1.1 (b.2 • unitAngle b.1.2)
  have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by
    dsimp only [γ,coordinateSectionPoint]
    exact (contDiff_const.add
      ((contDiff_fst.fst.sub contDiff_const).smul contDiff_const)).add
        (coordinatePlaneLift.contDiff.comp
          (contDiff_snd.smul (unitAngle_contDiff.comp contDiff_fst.snd)))
  have hd : HasDerivAt (fun u => γ (p,u)) (coordinatePlaneLift (unitAngle p.2)) (r p) := by
    have hh := coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt (r p)
      ((hasDerivAt_id (r p)).smul_const (unitAngle p.2))
    simpa only [γ,coordinateSectionPoint,Function.comp_def,one_smul,id_eq] using
      hh.const_add (chamberCorner s+(p.1-chamberCorner s 0) • EuclideanSpace.single 0 1)
  have hz : r p • unitAngle p.2≠0 := smul_ne_zero (hrpos p).1.ne' (unitAngle_ne_zero p.2)
  have hgauge : complexSquareGauge (r p • unitAngle p.2)<1/2 := by
    rw [complexSquareGauge_smul (hrpos p).1.le]
    have hscl : unitSquareScale p.2*complexSquareGauge (unitAngle p.2)=1/2 := by
      dsimp [unitSquareScale]
      field_simp [(complexSquareGauge_pos (unitAngle_ne_zero p.2)).ne']
    calc
      r p*complexSquareGauge (unitAngle p.2)<unitSquareScale p.2*complexSquareGauge (unitAngle p.2) :=
        mul_lt_mul_of_pos_right (hrpos p).2 (complexSquareGauge_pos (unitAngle_ne_zero p.2))
      _=1/2 := hscl
  have hpos := isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hz hgauge (hrbd p)
  have hne : ⟪N (γ (p,r p)),coordinatePlaneLift (unitAngle p.2)⟫≠0 := by
    intro he
    rw [map_smul,real_inner_smul_right] at hpos
    change 0<r p*⟪N (γ (p,r p)),coordinatePlaneLift (unitAngle p.2)⟫ at hpos
    rw [he,mul_zero] at hpos
    exact lt_irrefl _ hpos
  exact isMinimizerAt_smooth_boundary_exit hV hE hm hμ hN hp ha hγ.contDiffAt
    hrc.continuousAt (Filter.Eventually.of_forall hrbd) hd hne

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tubular_radius_extension {E : Set Torus} (hE : MeasurableSet E)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    {r0 : (Icc (chamberCorner s 0) (chamberCorner s 0+1/2)) × ℝ → ℝ}
    (hr0c : Continuous r0)
    (hr0p : ∀ t,Function.Periodic (fun a => r0 (t,a)) 1)
    (hr0pos : ∀ p,0<r0 p ∧ r0 p<unitSquareScale p.2)
    (hr0bd : ∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
      (r0 p • unitAngle p.2))∈frontier (openRepresentative E))
    (hr0op : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        (u • unitAngle p.2))∈openRepresentative E ↔ u<r0 p))
    (hr0cl : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r0 p)) :
    ∃ r : ℝ × ℝ → ℝ,Continuous r ∧
      (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
      (∀ p,0<r p ∧ r p<unitSquareScale p.2) ∧
      (∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
        (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈openRepresentative E ↔ u<r p)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p)) ∧
      ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
        ε≤r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  choose τ hτ hfold using coordinateSectionPoint_fold_axis s
  let r : ℝ × ℝ → ℝ := fun p => r0 (⟨τ p.1,hτ p.1⟩,p.2)
  have hsO := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hsC := reflection_invariant_closure hsO
  have hsB := fun i => frontier_reflection_invariant hE i (hs i)
  have hrpos (p : ℝ × ℝ) : 0<r p ∧ r p<unitSquareScale p.2 := hr0pos _
  have hrbd (p : ℝ × ℝ) : quotientMap (coordinateSectionPoint (chamberCorner s) p.1
      (r p • unitAngle p.2))∈frontier (openRepresentative E) :=
    (hfold p.1 _ (hsB 0) _).mp (hr0bd (⟨τ p.1,hτ p.1⟩,p.2))
  have hrop (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2) :
      quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈openRepresentative E ↔ u<r p := by
    rw [← hfold p.1 _ (hsO 0) _]
    exact hr0op (⟨τ p.1,hτ p.1⟩,p.2) u hu hu'
  have hrcl (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2) :
      quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p := by
    rw [← hfold p.1 _ (hsC 0) _]
    exact hr0cl (⟨τ p.1,hτ p.1⟩,p.2) u hu hu'
  have huniq (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2)
      (hb : quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈frontier (openRepresentative E)) : u=r p := by
    rw [(isOpen_openRepresentative E).frontier_eq] at hb
    exact le_antisymm ((hrcl p u hu hu').mp hb.1)
      (le_of_not_gt (fun h => hb.2 ((hrop p u hu hu').mpr h)))
  have hrc : Continuous r := continuous_radial_phase hrpos hrop hrcl
  refine ⟨r,hrc,?_,fun t a => hr0p _ a,hrpos,hrbd,hrop,hrcl,?_⟩
  · intro t a
    apply huniq (t,a) (r (t+1,a)) (hrpos _).1.le (hrpos _).2.le
    have hh := hrbd (t+1,a)
    simpa only [show t+1=t+(1 : ℤ) from by norm_num,
      quotientMap_coordinateSectionPoint_int] using hh
  · obtain ⟨ε,hε,hεr⟩ := tubular_radius_uniform hr0c hr0pos
    exact ⟨ε,hε,fun t a ha => hεr _ a ha⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_tube_radius {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv0 : quotientMap (chamberVertex s (fun j => decide (j=0)))∈openRepresentative E)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E)) :
    ∃ r : ℝ × ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
      (∀ p,0<r p ∧ r p<unitSquareScale p.2) ∧
      (∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
        (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈openRepresentative E ↔ u<r p)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p)) ∧
      ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
        ε≤r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  obtain ⟨r0,hr0c,hr0s,hr0p,hr0pos,hr0bd,hr0op,hr0cl⟩ :=
    isMinimizerAt_tubular_sections hV hE hm hμ hN hp ha hs hsg hv0 hv1 hv2
  obtain ⟨r,hrc,hrp1,hrp2,hrpos,hrbd,hrop,hrcl,heps⟩ :=
    tubular_radius_extension hE hs hr0c hr0p hr0pos hr0bd hr0op hr0cl
  exact ⟨r,isMinimizerAt_contDiff_tube_radius hV hE hm hμ hN hp ha hs hsg hrc hrpos hrbd,
    hrp1,hrp2,hrpos,hrbd,hrop,hrcl,heps⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def TrueRadialTube (E : Set Torus) (c : Cover) (r : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) r ∧
  (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
  (∀ p,0<r p ∧ r p<unitSquareScale p.2) ∧
  (∀ p,quotientMap (coordinateSectionPoint c p.1
    (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
  (∀ p u,0≤u → u≤unitSquareScale p.2 →
    (quotientMap (coordinateSectionPoint c p.1
      (u • unitAngle p.2))∈openRepresentative E ↔ u<r p)) ∧
  (∀ p u,0≤u → u≤unitSquareScale p.2 →
    (quotientMap (coordinateSectionPoint c p.1
      (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u≤r p)) ∧
  ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
    ε≤r (t,a) ∧ r (t,a)+ε≤unitSquareScale a

theorem isMinimizerAt_two_vertices_smooth_tube {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ j : Fin 3,coordinateReflection j ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (j : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j)
    (i : Fin 3)
    (hv : ∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative E ↔
      b=(fun _ => false) ∨ b=(fun j => decide (j=i))) :
    ∃ (e : Fin 3 ≃ Fin 3) (r : ℝ × ℝ → ℝ),
      TrueRadialTube (torusCoordinatePermute e ⁻¹' E) (chamberCorner (c ∘ e.symm)) r := by
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have hF := (torusCoordinatePermute e).continuous.measurable hE
  have hmF := isMinimizerAt_coordinatePermute hm e
  have hμF := isNormalMeasure_coordinatePermute hE hμ e
  have hNF := coordinatePermutedField_contDiff e hN
  have hpF := coordinatePermutedField_periodic e hp
  have haF := permuted_normal_ae hN.continuous hp ha e
  have hsF := reflection_invariant_coordinatePermute hs e
  have hsgF := chamberSign_coordinatePermute hE hsg e
  have hvF (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' E) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative E := by
    rw [openRepresentative_coordinatePermute hE e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative E ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  have h0 : quotientMap (chamberVertex (c ∘ e.symm) (fun j => decide (j=0)))∈
      openRepresentative (torusCoordinatePermute e ⁻¹' E) := by
    rw [hvF,hsingle,he0,hv]
    exact Or.inr rfl
  have hnot (j : Fin 3) (hj : j≠0) :
      quotientMap (chamberVertex (c ∘ e.symm) (fun k => decide (k=j)))∉
        closure (openRepresentative (torusCoordinatePermute e ⁻¹' E)) := by
    intro hh
    have ho := mem_open_of_mem_closure_not_frontier
      (isOpen_openRepresentative (torusCoordinatePermute e ⁻¹' E)) hh
      (isMinimizerAt_reflection_vertex_excluded hV hF hmF hμF hNF hpF haF hsF
        (chamberVertex_sine_zero (c ∘ e.symm) _))
    rw [hvF,hsingle,hv] at ho
    have heji : e.symm j≠i := by rw [← he0]; exact e.symm.injective.ne hj
    rcases ho with h|h
    · have hh := congrFun h (e.symm j)
      simp at hh
    · have hh := congrFun h (e.symm j)
      simp [heji] at hh
  obtain ⟨r,hr⟩ := isMinimizerAt_smooth_tube_radius hV hF hmF hμF hNF hpF haF hsF hsgF h0
    (hnot 1 (by decide)) (hnot 2 (by decide))
  exact ⟨e,r,hr⟩

theorem isMinimizerAt_first_transition_nonstandard_smooth_tube
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (v : Torus) (F : Set Torus) (e : Fin 3 ≃ Fin 3) (c : Cover) (r : ℝ × ℝ → ℝ),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧
      IsMinimizerAt (4*Real.pi/81) (torusCoordinatePermute e ⁻¹' F) ∧
      TrueRadialTube (torusCoordinatePermute e ⁻¹' F) c r := by
  obtain ⟨v,F,μ,N,hN,hp,c,H,i,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,hw,hv⟩ :=
    isMinimizerAt_first_transition_nonstandard_two_vertices hmE hnstd
  have hV : 4*Real.pi/81∈Ioo (0 : ℝ) 1 :=
    ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩
  obtain ⟨e,r,hr⟩ := isMinimizerAt_two_vertices_smooth_tube hV hF hm hμ hN hp ha hs hsg i hv
  exact ⟨v,F,e,chamberCorner (c ∘ e.symm),r,hF,he,isMinimizerAt_coordinatePermute hm e,hr⟩

end CubicTorus

end
end

end OAI
