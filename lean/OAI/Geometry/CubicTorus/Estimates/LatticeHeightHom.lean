import Mathlib
import OAI.Geometry.CubicTorus.Regularity.GraphNormalExtensionDivergence

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem complete_planes_normals_parallel {S : Set Cover} {N : Cover → Cover}
    (hunit : ∀ x∈S,‖N x‖=1)
    (hplane : ∀ a∈S,∀ b,⟪N a,b-a⟫=0 → b∈S ∧ N b=N a)
    {a b : Cover} (ha : a∈S) (hb : b∈S) : N b=N a ∨ N b= -N a := by
  let n := N a
  let m := N b
  let d := ⟪n,m⟫
  have hn : ‖n‖=1 := hunit a ha
  have hm : ‖m‖=1 := hunit b hb
  have hd : d^2=1 := by
    by_contra hd
    have hden : 1-d^2≠0 := sub_ne_zero.mpr (Ne.symm hd)
    let A := ⟪n,a⟫
    let B := ⟪m,b⟫
    let c := ((A-d*B)/(1-d^2)) • n+((B-d*A)/(1-d^2)) • m
    have hcn : ⟪n,c⟫=A := by
      simp only [c,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
      change (A-d*B)/(1-d^2)+(B-d*A)/(1-d^2)*d=A
      field_simp
      ring
    have hcm : ⟪m,c⟫=B := by
      rw [show c=((A-d*B)/(1-d^2)) • n+((B-d*A)/(1-d^2)) • m from rfl,
        inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hm,
        one_pow,mul_one,real_inner_comm n m]
      change (A-d*B)/(1-d^2)*d+(B-d*A)/(1-d^2)=B
      field_simp
      ring
    have hca := hplane a ha c (by change ⟪n,c-a⟫=0; rw [inner_sub_right,hcn]; exact sub_self _)
    have hcb := hplane b hb c (by change ⟪m,c-b⟫=0; rw [inner_sub_right,hcm]; exact sub_self _)
    have hnm : n=m := hca.2.symm.trans hcb.2
    have hd1 : d=1 := by
      dsimp only [d]
      rw [hnm,real_inner_self_eq_norm_sq,hm,one_pow]
    exact hd (by rw [hd1,one_pow])
  have hdor : d=1 ∨ d= -1 := by
    have he : (d-1)*(d+1)=0 := by nlinarith
    rcases mul_eq_zero.mp he with h|h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hdor with hd1|hd1
  · left
    change m=n
    have hs : ‖m-n‖^2=0 := by
      rw [norm_sub_sq_real,hm,hn,real_inner_comm n m]
      change 1^2-2*d+1^2=0
      rw [hd1]; norm_num
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  · right
    change m= -n
    have hs : ‖m+n‖^2=0 := by
      rw [norm_add_sq_real,hm,hn,real_inner_comm n m]
      change 1^2+2*d+1^2=0
      rw [hd1]; norm_num
    have he : m+n=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    exact eq_neg_iff_add_eq_zero.mpr he

namespace Periodic

theorem isMinimizerAt_connected_or_parallel_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ᶠ v in 𝓝 (0 : Cover),
            (quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪N a,v⟫=0) ∧
            (quotientMap (a+v)∈frontier (openRepresentative E) → N (a+v)=N a)) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a) ∧
        ∀ a b,quotientMap a∈frontier (openRepresentative E) →
          quotientMap b∈frontier (openRepresentative E) → N b=N a ∨ N b= -N a := by
  rcases isMinimizerAt_connected_or_complete_planes hV hE hmin with hc|⟨N,hN,hp,hu,hloc,hplane⟩
  · exact Or.inl hc
  · exact Or.inr ⟨N,hN,hp,hu,hloc,hplane,fun a b ha hb ↦
      complete_planes_normals_parallel hu hplane ha hb⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def latticeHeightHom (n : Cover) : (Fin 3 → ℤ) →+ ℝ where
  toFun m := ⟪n,latticeVector m⟫
  map_zero' := by rw [latticeVector_zero,inner_zero_right]
  map_add' m k := by rw [latticeVector_add,inner_add_right]

theorem flat_periodic_normal_integral {S : Set Cover} {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hS : ∀ m x,x∈S → x+latticeVector m∈S)
    (hunit : ∀ x∈S,‖N x‖=1)
    (hplane : ∀ a∈S,∀ b,⟪N a,b-a⟫=0 → b∈S ∧ N b=N a)
    (hloc : ∀ a∈S,∀ᶠ v in 𝓝 (0 : Cover),a+v∈S ↔ ⟪N a,v⟫=0)
    {a : Cover} (ha : a∈S) :
    ∃ (c : ℝ) (m : Fin 3 → ℤ),c≠0 ∧ m≠0 ∧ N a=c • latticeVector m ∧
      (latticeHeightHom (N a)).range=AddSubgroup.zmultiples c := by
  let n := N a
  have hn : ‖n‖=1 := hunit a ha
  obtain ⟨r,hr,hrloc⟩ := Metric.mem_nhds_iff.mp (hloc a ha)
  have hgap : Disjoint (↑(latticeHeightHom n).range : Set ℝ) (Ioo 0 r) := by
    apply Set.disjoint_left.mpr
    rintro t ⟨k,rfl⟩ ht
    let t := ⟪n,latticeVector k⟫
    change 0<t ∧ t<r at ht
    have hkt : a+t • n∈S := by
      apply (hplane (a+latticeVector k) (hS k a ha) (a+t • n) ?_).1
      rw [hp]
      change ⟪n,(a+t • n)-(a+latticeVector k)⟫=0
      rw [show (a+t • n)-(a+latticeVector k)=t • n-latticeVector k by abel,
        inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn]
      change t*1^2-t=0
      ring
    have hsmall : t • n∈Metric.ball (0 : Cover) r := by
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,hn,mul_one,
        abs_of_pos ht.1]
      exact ht.2
    have he := (hrloc hsmall).mp hkt
    change ⟪n,t • n⟫=0 at he
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at he
    exact (ne_of_gt ht.1) he
  obtain ⟨c,hc⟩ := AddSubgroup.cyclic_of_isolated_zero hr hgap
  have hc' : (latticeHeightHom n).range=AddSubgroup.zmultiples c := by
    rw [AddSubgroup.zmultiples_eq_closure]
    exact hc
  have hcoords (i : Fin 3) : ∃ z : ℤ,(z : ℝ)*c=n i := by
    have hi : n i∈(latticeHeightHom n).range := by
      refine ⟨Pi.single i 1,?_⟩
      change ⟪n,latticeVector (Pi.single i 1)⟫=n i
      have hv : latticeVector (Pi.single i 1)=EuclideanSpace.single i 1 := by
        ext j
        simp [latticeVector,Pi.single_apply]
      rw [hv,EuclideanSpace.inner_single_right]
      simp
    rw [hc',AddSubgroup.mem_zmultiples_iff] at hi
    simpa only [zsmul_eq_mul] using hi
  choose m hm using hcoords
  have hnm : n=c • latticeVector m := by
    ext i
    change n i=c*(m i : ℝ)
    rw [← hm i,mul_comm]
  have hc0 : c≠0 := by
    intro hz
    have he : n=0 := by rw [hnm,hz,zero_smul]
    rw [he,norm_zero] at hn
    norm_num at hn
  have hm0 : m≠0 := by
    intro hz
    have he : n=0 := by rw [hnm,hz,latticeVector_zero,smul_zero]
    rw [he,norm_zero] at hn
    norm_num at hn
  exact ⟨c,m,hc0,hm0,hnm,hc'⟩

namespace Periodic

theorem isMinimizerAt_connected_or_integral_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a) ∧
        (∀ a b,quotientMap a∈frontier (openRepresentative E) →
          quotientMap b∈frontier (openRepresentative E) → N b=N a ∨ N b= -N a) ∧
        ∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∃ (c : ℝ) (m : Fin 3 → ℤ),c≠0 ∧ m≠0 ∧ N a=c • latticeVector m ∧
            (latticeHeightHom (N a)).range=AddSubgroup.zmultiples c := by
  rcases isMinimizerAt_connected_or_parallel_planes hV hE hmin with hc|⟨N,hN,hp,hu,hloc,hplane,hpar⟩
  · exact Or.inl hc
  · refine Or.inr ⟨N,hN,hp,hu,hplane,hpar,?_⟩
    intro a ha
    apply flat_periodic_normal_integral hp (S := quotientMap ⁻¹' frontier (openRepresentative E))
      ?_ hu hplane (fun a ha ↦ (hloc a ha).mono fun v hv ↦ hv.1) ha
    intro m x hx
    change quotientMap (x+latticeVector m)∈frontier (openRepresentative E)
    rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    exact hx

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem compact_flat_boundary_finite_planes {K : Set Torus} (hK : IsClosed K)
    {N : Cover → Cover}
    (hloc : ∀ a,quotientMap a∈K → ∀ᶠ v in 𝓝 (0 : Cover),
      quotientMap (a+v)∈K ↔ ⟪N a,v⟫=0)
    (hplane : ∀ a,quotientMap a∈K → ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈K) :
    ∃ s : Finset Cover,(∀ a∈s,quotientMap a∈K) ∧
      K=⋃ a∈s,quotientMap '' {b : Cover | ⟪N a,b-a⟫=0} := by
  classical
  let C : Set Cover := closedFundamentalCube ∩ quotientMap ⁻¹' K
  have hC : IsCompact C := isCompact_closedFundamentalCube.inter_right
    (hK.preimage continuous_quotientMap)
  have hrad (a : C) := Metric.mem_nhds_iff.mp (hloc a.1 a.2.2)
  choose r hr hrloc using hrad
  let U : C → Set Cover := fun a ↦ Metric.ball a (r a)
  obtain ⟨s,hs⟩ := hC.elim_finite_subcover U (fun _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  refine ⟨s.image Subtype.val,?_,?_⟩
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact b.2.2
  · ext z
    constructor
    · intro hz
      have hzC : representative z∈C := ⟨(cubeRepresentative z).property,by
        change quotientMap (representative z)∈K
        rwa [quotientMap_representative]⟩
      obtain ⟨a,ha,hza⟩ := mem_iUnion₂.mp (hs hzC)
      apply mem_iUnion₂.mpr
      refine ⟨a.1,Finset.mem_image.mpr ⟨a,ha,rfl⟩,representative z,?_,quotientMap_representative z⟩
      have hv : representative z-(a : Cover)∈Metric.ball (0 : Cover) (r a) := by
        simpa only [U,Metric.mem_ball,dist_eq_norm,sub_zero] using hza
      have hvK : quotientMap ((a : Cover)+(representative z-(a : Cover)))∈K := by
        simpa only [add_sub_cancel,quotientMap_representative] using hz
      exact (hrloc a hv).mp hvK
    · intro hz
      obtain ⟨a,ha,b,hba,rfl⟩ := mem_iUnion₂.mp hz
      obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
      exact hplane a' a'.2.2 b hba

namespace Periodic

theorem isMinimizerAt_connected_or_finite_integral_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (N : Cover → Cover) (s : Finset Cover),ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a∈s,quotientMap a∈frontier (openRepresentative E) ∧ ‖N a‖=1) ∧
        (frontier (openRepresentative E)=⋃ a∈s,quotientMap '' {b : Cover | ⟪N a,b-a⟫=0}) ∧
        (∀ a∈s,∀ b∈s,N b=N a ∨ N b= -N a) ∧
        ∀ a∈s,∃ (c : ℝ) (m : Fin 3 → ℤ),c≠0 ∧ m≠0 ∧ N a=c • latticeVector m ∧
          (latticeHeightHom (N a)).range=AddSubgroup.zmultiples c := by
  rcases isMinimizerAt_connected_or_parallel_planes hV hE hmin with hc|⟨N,hN,hp,hu,hloc,hplane,hpar⟩
  · exact Or.inl hc
  · obtain ⟨s,hs,hK⟩ := compact_flat_boundary_finite_planes isClosed_frontier
      (fun a ha ↦ (hloc a ha).mono fun v hv ↦ hv.1) (fun a ha b hb ↦ (hplane a ha b hb).1)
    refine Or.inr ⟨N,s,hN,hp,fun a ha ↦ ⟨hs a ha,hu a (hs a ha)⟩,hK,
      fun a ha b hb ↦ hpar a b (hs a ha) (hs b hb),?_⟩
    intro a ha
    apply flat_periodic_normal_integral hp (S := quotientMap ⁻¹' frontier (openRepresentative E))
      ?_ hu hplane (fun a ha ↦ (hloc a ha).mono fun v hv ↦ hv.1) (hs a ha)
    intro m x hx
    change quotientMap (x+latticeVector m)∈frontier (openRepresentative E)
    rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    exact hx

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem continuous_line_avoids_frontier {U : Set Torus} (hU : IsOpen U)
    {f : ℝ → Torus} (hf : Continuous f) (havoid : ∀ t,f t∉frontier U)
    (s t : ℝ) : f s∈U ↔ f t∈U := by
  have he : f ⁻¹' closure U=f ⁻¹' U := by
    ext r
    constructor
    · intro hr
      by_contra hn
      exact havoid r (by rw [hU.frontier_eq]; exact ⟨hr,hn⟩)
    · intro hr
      exact subset_closure hr
  have hc : IsClopen (f ⁻¹' U) := ⟨by rw [← he]; exact isClosed_closure.preimage hf,
    hU.preimage hf⟩
  constructor
  · intro hs
    have hu := hc.eq_univ ⟨s,hs⟩
    change t∈f ⁻¹' U
    rw [hu]
    exact mem_univ t
  · intro ht
    have hu := hc.eq_univ ⟨t,ht⟩
    change s∈f ⁻¹' U
    rw [hu]
    exact mem_univ s

theorem open_phase_tangent_invariant {U : Set Torus} (hU : IsOpen U)
    {n : Cover}
    (hplane : ∀ a,quotientMap a∈frontier U → ∀ b,⟪n,b-a⟫=0 →
      quotientMap b∈frontier U)
    {x y : Cover} (hxy : ⟪n,y-x⟫=0) : quotientMap x∈U ↔ quotientMap y∈U := by
  by_cases hx : quotientMap x∈frontier U
  · have hy := hplane x hx y hxy
    have hx' : quotientMap x∉U := by rw [hU.frontier_eq] at hx; exact hx.2
    have hy' : quotientMap y∉U := by rw [hU.frontier_eq] at hy; exact hy.2
    exact iff_of_false hx' hy'
  · let f : ℝ → Torus := fun t ↦ quotientMap (x+t • (y-x))
    have hf : Continuous f := continuous_quotientMap.comp
      (continuous_const.add (continuous_id.smul continuous_const))
    have ha (t : ℝ) : f t∉frontier U := by
      intro ht
      apply hx
      apply hplane (x+t • (y-x)) ht x
      rw [show x-(x+t • (y-x))= -(t • (y-x)) by abel,
        inner_neg_right,real_inner_smul_right,hxy,mul_zero,neg_zero]
    simpa only [f,zero_smul,add_zero,one_smul,add_sub_cancel] using
      continuous_line_avoids_frontier hU hf ha 0 1

theorem open_planar_phase_factor {U : Set Torus} (hU : IsOpen U)
    {n : Cover} (hn : ‖n‖=1)
    (hplane : ∀ a,quotientMap a∈frontier U → ∀ b,⟪n,b-a⟫=0 →
      quotientMap b∈frontier U)
    {c : ℝ} (hc : c∈(latticeHeightHom n).range) :
    ∃ J : Set ℝ,IsOpen J ∧ (∀ t,t+c∈J ↔ t∈J) ∧
      ∀ x,quotientMap x∈U ↔ ⟪n,x⟫∈J := by
  let J : Set ℝ := (fun t : ℝ ↦ quotientMap (t • n)) ⁻¹' U
  have hJ : IsOpen J := hU.preimage (continuous_quotientMap.comp
    (continuous_id.smul continuous_const))
  have hfactor (x : Cover) : quotientMap x∈U ↔ ⟪n,x⟫∈J := by
    apply open_phase_tangent_invariant hU hplane
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn]
    ring
  refine ⟨J,hJ,?_,hfactor⟩
  obtain ⟨k,hk⟩ := hc
  change ⟪n,latticeVector k⟫=c at hk
  intro t
  have hx : ⟪n,t • n⟫=t := by
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  have hy : ⟪n,t • n+latticeVector k⟫=t+c := by rw [inner_add_right,hx,hk]
  rw [← hy,← hfactor,quotientMap_add,quotientMap_latticeVector,add_zero,hfactor,hx]

namespace Periodic

theorem isMinimizerAt_connected_or_planar_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (n : Cover) (c : ℝ) (m : Fin 3 → ℤ) (J : Set ℝ),
        ‖n‖=1 ∧ c≠0 ∧ m≠0 ∧ n=c • latticeVector m ∧
        (latticeHeightHom n).range=AddSubgroup.zmultiples c ∧
        IsOpen J ∧ (∀ t,t+c∈J ↔ t∈J) ∧
        ∀ x,quotientMap x∈openRepresentative E ↔ ⟪n,x⟫∈J := by
  classical
  by_cases hconn : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hconn
  obtain ⟨N,hN,hp,hu,hplane,hpar,hint⟩ :=
    (isMinimizerAt_connected_or_integral_planes hV hE hmin).resolve_left hconn
  have hnon : (frontier (openRepresentative E)).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    exact hconn (he.symm ▸ isPreconnected_empty)
  obtain ⟨z,hz⟩ := hnon
  let a := representative z
  have ha : quotientMap a∈frontier (openRepresentative E) := by
    simpa only [a,quotientMap_representative] using hz
  obtain ⟨c,m,hc,hm,hnm,hcyc⟩ := hint a ha
  have hfixed (b : Cover) (hb : quotientMap b∈frontier (openRepresentative E))
      (d : Cover) (hd : ⟪N a,d-b⟫=0) : quotientMap d∈frontier (openRepresentative E) := by
    apply (hplane b hb d ?_).1
    rcases hpar a b ha hb with h|h
    · rwa [h]
    · rw [h,inner_neg_left,hd,neg_zero]
  have hc' : c∈(latticeHeightHom (N a)).range := by
    rw [hcyc]
    exact AddSubgroup.mem_zmultiples c
  obtain ⟨J,hJ,hperiod,hfactor⟩ := open_planar_phase_factor (isOpen_openRepresentative E)
    (hu a ha) hfixed hc'
  exact Or.inr ⟨N a,c,m,J,hu a ha,hc,hm,hnm,hcyc,hJ,hperiod,hfactor⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def integerCharacter (m : Fin 3 → ℤ) : Torus →+ AddCircle (1 : ℝ) where
  toFun x := ∑ i, m i • x i
  map_zero' := by simp
  map_add' x y := by simp [smul_add,Finset.sum_add_distrib]

lemma continuous_integerCharacter (m : Fin 3 → ℤ) : Continuous (integerCharacter m) := by
  change Continuous (fun x : Torus ↦ ∑ i,m i • x i)
  exact continuous_finsetSum Finset.univ fun i _ ↦
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ)) i).zsmul (m i)

lemma integerCharacter_quotientMap (m : Fin 3 → ℤ) (x : Cover) :
    integerCharacter m (quotientMap x)=(⟪latticeVector m,x⟫ : AddCircle (1 : ℝ)) := by
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=_
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,latticeVector,WithLp.ofLp_toLp]
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (∑ i,x i*(m i : ℝ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,← zsmul_eq_mul]
  rfl

lemma integerCharacter_surjective {m : Fin 3 → ℤ} (hm : m≠0) :
    Function.Surjective (integerCharacter m) := by
  have hi : ∃ i,m i≠0 := by
    by_contra hn
    push Not at hn
    exact hm (funext hn)
  obtain ⟨i,hi⟩ := hi
  intro z
  let t : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z).1
  refine ⟨quotientMap (EuclideanSpace.single i (t/(m i : ℝ))),?_⟩
  rw [integerCharacter_quotientMap,EuclideanSpace.inner_single_right]
  simp only [latticeVector,WithLp.ofLp_toLp,starRingEnd_apply,star_trivial]
  rw [div_mul_cancel₀ t (by exact_mod_cast hi)]
  exact AddCircle.coe_equivIco

theorem integerCharacter_measurePreserving {m : Fin 3 → ℤ} (hm : m≠0) :
    MeasurePreserving (integerCharacter m) torusVolume volume := by
  have hc := continuous_integerCharacter m
  let : (Measure.map (integerCharacter m) torusVolume).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure torusVolume (integerCharacter m) hc
      (integerCharacter_surjective hm)
  let : IsProbabilityMeasure (Measure.map (integerCharacter m) torusVolume) :=
    inferInstance
  refine ⟨hc.measurable,?_⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_open_phase_descends {L : Set ℝ} (hL : IsOpen L)
    (hp : ∀ t,t+1∈L ↔ t∈L) :
    ∃ K : Set (AddCircle (1 : ℝ)),IsOpen K ∧ ∀ t : ℝ,(t : AddCircle (1 : ℝ))∈K ↔ t∈L := by
  have hper : Function.Periodic (fun t ↦ t∈L) 1 := fun t ↦ propext (hp t)
  let K : Set (AddCircle (1 : ℝ)) := hper.lift
  have he : K=(fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' L := by
    ext z
    obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
    constructor
    · intro h
      exact ⟨t,h,rfl⟩
    · rintro ⟨s,hs,he⟩
      change hper.lift (t : AddCircle (1 : ℝ))
      rw [← he]
      exact hs
  refine ⟨K,?_,fun _ ↦ Iff.rfl⟩
  rw [he]
  exact QuotientAddGroup.isOpenMap_coe _ hL

theorem Periodic.isMinimizerAt_connected_or_circle_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧ IsOpen K ∧
        openRepresentative E=(integerCharacter m) ⁻¹' K ∧
        volume K=ENNReal.ofReal V := by
  rcases Periodic.isMinimizerAt_connected_or_planar_phase hV hE hmin with hconn|
    ⟨n,c,m,J,hn,hc,hm,hnm,hcyc,hJ,hperiod,hfactor⟩
  · exact Or.inl hconn
  let L : Set ℝ := (fun t : ℝ ↦ c*t) ⁻¹' J
  have hL : IsOpen L := hJ.preimage (continuous_const.mul continuous_id)
  have hLP (t : ℝ) : t+1∈L ↔ t∈L := by
    change c*(t+1)∈J ↔ c*t∈J
    simpa only [mul_add,mul_one] using hperiod (c*t)
  obtain ⟨K,hK,hKL⟩ := periodic_open_phase_descends hL hLP
  have hfactorK (x : Cover) : quotientMap x∈openRepresentative E ↔
      integerCharacter m (quotientMap x)∈K := by
    rw [integerCharacter_quotientMap,hKL]
    change quotientMap x∈openRepresentative E ↔ c*⟪latticeVector m,x⟫∈J
    rw [← real_inner_smul_left,← hnm]
    exact hfactor x
  have he : openRepresentative E=(integerCharacter m) ⁻¹' K := by
    ext z
    simpa only [quotientMap_representative,Set.mem_preimage] using hfactorK (representative z)
  refine Or.inr ⟨m,K,hm,hK,he,?_⟩
  rw [← (integerCharacter_measurePreserving hm).measure_preimage hK.measurableSet.nullMeasurableSet,
    ← he]
  exact (measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmin)).trans hmin.2.1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def simultaneousArea (l : List Variation) (μ : FiniteMeasure NormalBundle) (t : ℝ) : ℝ :=
  ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖ ∂(μ : Measure NormalBundle)

lemma simultaneousArea_smoothAt (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    ContDiffAt ℝ (⊤ : ℕ∞) (simultaneousArea l μ) 0 := by
  exact normalArea_smoothAt (simultaneousCofactor_smooth l)
    (by intro p _; exact simultaneousCofactor_zero l p.1 p.2) μ

lemma simultaneousArea_zero (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    simultaneousArea l μ 0=(μ.mass : ℝ) := by
  simp only [simultaneousArea,simultaneousCofactor_zero,fun z : NormalBundle ↦ z.2.property,
    integral_const,smul_eq_mul,mul_one]
  rfl

lemma simultaneousArea_deriv (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    deriv (simultaneousArea l μ) 0=
      ∫ z,tangentialDivergence (chainVelocity l) z.1 z.2 ∂(μ : Measure NormalBundle) := by
  have he := normalArea_first_derivative (simultaneousCofactor_smooth l)
    (by intro p _; exact simultaneousCofactor_zero l p.1 p.2) μ
  change deriv (simultaneousArea l μ) 0=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    change ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2) 0⟫=_
    rw [simultaneousCofactor_deriv,chainNormalVelocity_eq_cofactor,
      cofactorLinear_inner _ z.2.property]
    rfl

theorem normal_chain_support_jets {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) :
    ∃ l : List Variation,chainVelocity l=N ∧
      chainFlux l E=(μ.mass : ℝ) ∧
      deriv (simultaneousArea l μ) 0=H*(μ.mass : ℝ) ∧
      deriv (deriv (simultaneousArea l μ)) 0-
        H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
  obtain ⟨l,hl,hflux,_⟩ := exists_chain_of_field hN hp
  have hl' : chainVelocity l=N := funext hl
  have hf : (∫ z,⟪(z.2 : Cover),N z.1⟫ ∂(μ : Measure NormalBundle))=(μ.mass : ℝ) := by
    have he : (fun z : NormalBundle ↦ ⟪(z.2 : Cover),N z.1⟫)=ᵐ[μ.toMeasure] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hn] with z hz
      rw [hz.1,real_inner_self_eq_norm_sq,z.2.property,one_pow]
    rw [integral_congr_ae he,integral_const,smul_eq_mul,mul_one]
    rfl
  have hH := weakCMC_normal_extension hCMC hN hp hn
  have hJ : ambientQuadratic E μ H N=
      -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)) := by
    rw [ambientQuadratic_boundary hμ H hN hp]
    have he := boundaryQuadratic_eq_normalExtension (μ := μ) (H := H)
      (f := fun _ ↦ (1 : ℝ)) contDiff_const hN (by
        filter_upwards [hn,hH] with z hz hh
        exact fun _ ↦ ⟨hz.1,hz.2,hh⟩)
    simp only [one_smul] at he
    rw [he]
    have hg (x : Cover) : gradient (fun _ : Cover ↦ (1 : ℝ)) x=0 := by simp [gradient]
    simp only [normalExtensionJacobi,hg,inner_zero_right,zero_smul,
      sub_self,norm_zero,zero_pow (by norm_num : 2≠0),one_pow,one_mul,zero_sub,integral_neg]
  refine ⟨l,hl',?_,?_,?_⟩
  · rw [hflux,← periodic_normal_flux hμ hN hp,hf]
  · rw [simultaneousArea_deriv,hl',hCMC N hN hp,hf]
  · change deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
        ∂(μ : Measure NormalBundle))) 0-_= _
    rw [simultaneousArea_second_deriv,simultaneousMass_second_deriv]
    change chainQuadratic E μ H l=_
    rw [chainQuadratic_eq_ambient hμ hCMC,hl',hJ]

theorem isMinimizerAt_normal_support_jets {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (l : List Variation),
      IsNormalMeasure E μ ∧ 0<(μ.mass : ℝ) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      chainFlux l E=(μ.mass : ℝ) ∧
      deriv (simultaneousArea l μ) 0=H*(μ.mass : ℝ) ∧
      deriv (deriv (simultaneousArea l μ)) 0-
        H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0≤0 := by
  obtain ⟨μ,H,hμ,hCMC,_⟩ := isMinimizerAt_ambient_stability hV hE hmin
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  obtain ⟨l,hl,hflux,harea,hsecond⟩ := normal_chain_support_jets hμ hCMC hN hp hn
  have hpos : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  refine ⟨μ,H,l,hμ,hpos,hCMC,hflux,harea,?_⟩
  rw [hsecond,neg_nonpos]
  apply integral_nonneg_of_ae
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU,hn]
    with z hz hnz
  exact isMinimizerAt_normal_curvature_nonnegative hV hE hmin hμ hN hp
    (hn.mono fun _ h ↦ h.1) z.1 hz hnz.2

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem smooth_linear_volume_correction {m f : ℝ → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧ deriv γ 0=0 ∧
      deriv (deriv γ) 0*f 0= -deriv (deriv m) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),m t+γ t*f t=m 0+t*deriv m 0) := by
  let p := deriv m 0
  have hn : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ m 0+t*p-m t) := by fun_prop
  obtain ⟨γ,hγ,he⟩ := smooth_quotient_extension hn hf hf0
  have hγ0 : γ 0=0 := by simpa using he.self_of_nhds
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),f t≠0 := hf.continuous.continuousAt.eventually_ne hf0
  have hx : ∀ᶠ t in 𝓝 (0 : ℝ),m t+γ t*f t=m 0+t*p := by
    filter_upwards [he,hne] with t ht hft
    rw [ht,div_mul_cancel₀ _ hft]
    ring
  let q : ℝ → ℝ := fun t ↦ m t-t*p
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by dsimp [q]; fun_prop
  have hdq : deriv q=fun t ↦ deriv m t-p := by
    funext t
    simpa [q] using ((hm.differentiable (by simp) t).hasDerivAt.fun_sub
      ((hasDerivAt_id t).mul_const p)).deriv
  have hdq0 : deriv q 0=0 := by rw [hdq]; simp [p]
  have hddq : deriv (deriv q) 0=deriv (deriv m) 0 := by
    rw [hdq]
    exact ((deriv_smooth m hm).differentiable (by simp) 0).hasDerivAt.sub_const p |>.deriv
  have hxq : (fun t ↦ q t+γ t*f t)=ᶠ[𝓝 0] fun _ ↦ q 0 := by
    filter_upwards [hx] with t ht
    dsimp [q]
    linarith
  obtain ⟨hdγ,hddγ⟩ := correction_second_derivative hq hf hγ hγ0 hf0 hdq0 hxq
  rw [hddq] at hddγ
  exact ⟨γ,hγ,hγ0,hdγ,hddγ,hx⟩

namespace Periodic

theorem chain_linear_volume_correction (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧ deriv γ 0=0 ∧
      deriv (deriv γ) 0*directionalFlux E b.coordinate b.function=
        -deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume.real (chainRegion (correctedChain l b γ t) E)=
          torusVolume.real E+t*chainFlux l E) := by
  obtain ⟨γ,hγ,hγ0,hdγ,hddγ,hx⟩ := smooth_linear_volume_correction
    (simultaneousMass_smooth l E) (simultaneousFlux_smooth l b E) (by simpa using hB)
  simp only [simultaneousFlux_zero] at hddγ
  refine ⟨γ,hγ,hγ0,hdγ,hddγ,?_⟩
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|γ t| * (b.bound : ℝ)<1 :=
    (hγ.continuous.continuousAt.abs.mul_const _).eventually (eventually_lt_nhds (by simp [hγ0]))
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hx] with t ht hbt hxt
  have hv : ChainValid (correctedChain l b γ t) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  rw [volume_chainRegion hv hE]
  change chainMass (simultaneousChain l t++[(b,γ t)]) E=_
  rw [chainMass_append,hxt,simultaneousMass_zero l hE,simultaneousMass_deriv]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma coordinateCMC_of_global {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (b : Variation) : normalFirstVariation μ b=H*directionalFlux E b.coordinate b.function := by
  have he := hCMC (variationField b) (variationField_smooth b) (variationField_periodic b)
  rw [periodic_normal_flux hμ (variationField_smooth b) (variationField_periodic b)] at he
  have hleft : normalFirstVariation μ b=
      ∫ z,tangentialDivergence (variationField b) z.1 z.2 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      change ⟪(z.2 : Cover),coordinateNormalVelocity b.coordinate b.function z.1 z.2⟫=_
      rw [← cofactorLinear_coordinate (b.smooth.differentiable (by simp) z.1),
        cofactorLinear_inner _ z.2.property]
      rfl
  rw [hleft,he]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ divergence_smul_const (b.smooth.differentiable (by simp) x) _

lemma correctedChainArea_deriv_zero_speed (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (hdγ : deriv γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (correctedChainArea l b γ μ) 0=deriv (simultaneousArea l μ) 0 := by
  have hd := normalArea_first_derivative (correctedChainCofactor_smooth l b hγ)
    (by intro p _; simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]) μ
  have hc := normalArea_first_derivative (simultaneousCofactor_smooth l)
    (by intro p _; simp) μ
  change deriv (correctedChainArea l b γ μ) 0=_ at hd
  change deriv (simultaneousArea l μ) 0=_ at hc
  rw [hd,hc]
  apply integral_congr_ae
  refine ae_of_all _ fun z ↦ ?_
  change ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2) 0⟫=
    ⟪(z.2 : Cover),deriv (fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2) 0⟫
  congr 1
  let C : ℝ → Cover := fun t ↦ chainCofactor (simultaneousChain l t) z.1 z.2
  let P : ℝ → Cover := fun t ↦ coordinateNormalVelocity b.coordinate b.function
    (chainMove (simultaneousChain l t) z.1) (C t)
  have hC : ContDiff ℝ (⊤ : ℕ∞) C :=
    (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ ((z.1 : Cover),(z.2 : Cover)))))
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp
    (((simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)).prodMk hC)
  change deriv (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2) 0=deriv C 0
  have he : (fun t ↦ chainCofactor (correctedChain l b γ t) z.1 z.2)=
      (fun t ↦ C t+γ t • P t) := by
    funext t
    simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rfl
  rw [he,deriv_smooth_add hC (hγ.fun_smul hP),deriv_smooth_smul hγ hP]
  simp [hγ0,hdγ]

lemma correctedChainArea_second_zero_speed (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (hdγ : deriv γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (correctedChainArea l b γ μ)) 0=
      deriv (deriv (simultaneousArea l μ)) 0+deriv (deriv γ) 0*normalFirstVariation μ b := by
  let C : ℝ×(Cover×Cover) → Cover := fun p ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2
  let P : ℝ×(Cover×Cover) → Cover := fun p ↦ coordinateNormalVelocity b.coordinate b.function
    (chainMove (simultaneousChain l p.1) p.2.1) (C p)
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := simultaneousCofactor_smooth l
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp
    (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk hC)
  have he := normalArea_second_zero_correction hC hP (by intro p _; simp [C]) hγ hγ0 hdγ μ
  have hleft : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)‖
      ∂(μ : Measure NormalBundle))=correctedChainArea l b γ μ := by
    funext t
    simp only [correctedChainArea,correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rfl
  rw [hleft] at he
  change deriv (deriv (correctedChainArea l b γ μ)) 0=
    deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖ ∂(μ : Measure NormalBundle))) 0+_
  simpa [P,C,normalEmbedding,normalFirstVariation] using he

theorem isMinimizerAt_affine_volume_support_with_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (P H : ℝ) (A : ℝ → ℝ),0<P ∧ P=(perimeter E).toReal ∧
      ContDiffAt ℝ (⊤ : ℕ∞) A 0 ∧ A 0=P ∧ deriv A 0=H*P ∧
      deriv (deriv A) 0≤0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),isoperimetricProfile (V+t*P)≤A t/2) ∧
      (∃ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ ∧
        ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
          (∀ m x,F (x+latticeVector m)=F x) →
          (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
            H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) := by
  obtain ⟨μ,H,l,hμ,hpos,hCMC,hflux,ha,hsecond⟩ := isMinimizerAt_normal_support_jets hV hE hmin
  obtain ⟨i,f,hf,hp,hfpos⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  obtain ⟨b,hbi,hbf⟩ := exists_variation_of_function i hf hp
  have hB : directionalFlux E b.coordinate b.function≠0 := by simpa [hbi,hbf] using hfpos.ne'
  obtain ⟨γ,hγ,hγ0,hdγ,hddγ,hvol⟩ := chain_linear_volume_correction l b hE hB
  refine ⟨μ.mass,H,correctedChainArea l b γ μ,hpos,hμ.1,
    correctedChainArea_smoothAt l b hγ hγ0 μ,correctedChainArea_zero l b hγ0 μ,?_,?_,?_,μ,hμ,hCMC⟩
  · rw [correctedChainArea_deriv_zero_speed l b hγ hγ0 hdγ μ,ha]
  · rw [correctedChainArea_second_zero_speed l b hγ hγ0 hdγ μ,
      coordinateCMC_of_global hμ hCMC b]
    have he : deriv (deriv γ) 0*(H*directionalFlux E b.coordinate b.function)=
        -H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
      calc _ = H*(deriv (deriv γ) 0*directionalFlux E b.coordinate b.function) := by ring
           _ = _ := by rw [hddγ]; ring
    rw [he]
    simpa only [sub_eq_add_neg,neg_mul] using hsecond
  · have hVI : ∀ᶠ t in 𝓝 (0 : ℝ),V+t*(μ.mass : ℝ)∈Icc 0 1 := by
      have hct : ContinuousAt (fun t : ℝ ↦ V+t*(μ.mass : ℝ)) 0 := by fun_prop
      exact hct.eventually (Icc_mem_nhds (by simpa using hV.1) (by simpa using hV.2))
    filter_upwards [hvol,hVI] with t ht hvt
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hve : torusVolume (chainRegion (correctedChain l b γ t) E)=
        ENNReal.ofReal (V+t*(μ.mass : ℝ)) := by
      have hv' := ht.2
      simp only [hflux,Measure.real,hmin.2.1,ENNReal.toReal_ofReal hV.1.le] at hv'
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _),hv']
    have hprofile := isoperimetricProfile_le_competitor hvt hfin hve
    have harea := perimeter_chainRegion_le_normalArea ht.1 hE hμ
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top harea
    rw [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] at hreal
    exact hprofile.trans (div_le_div_of_nonneg_right hreal (by norm_num))

end Periodic
end CubicTorus
end
end
end

end OAI
