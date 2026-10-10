import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormalCoordinateMap
import OAI.Geometry.SmoothYau.Smoothness.NormalInverseVecNorm
import OAI.Geometry.SmoothYau.SphereMetric.CompactThreePolynomialNet

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff

theorem normalCoordinateMap_inverse_bound
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∃ C ≥ 1, ∀ q ∈ metricFrameSet g K,
      ∀ v : Fin 3 → ℝ, ‖v‖ ≤ r → ∃ x : Fin 3 → ℝ,
        normalCoordinateMap g q x = normalWaveEquiv.symm q.1+v ∧ ‖x‖ ≤ C*‖v‖ := by
  obtain ⟨e,he,hs,hi⟩ := exists_normal_family_inverse g
  let R : NormalWaveParameter × (Fin 3 → ℝ) → NormalWaveParameter × NormalWaveSpace :=
    fun w => (w.1,w.1.1+normalWaveEquiv w.2)
  have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_fst).add (normalWaveEquiv.contDiff.comp contDiff_snd))
  have h0 (q : NormalWaveParameter) (hq : q ∈ metricFrameSet g K) : (q,0) ∈ e.source := by
    rw [hs]
    exact ⟨metricFrameSet_equiv g hq,by simp⟩
  have he0 (q : NormalWaveParameter) : e (q,0) = R (q,0) := by
    rw [he]
    simp [normalFamilyTotal,R,normalJetMap_zero]
  have hsub : metricFrameSet g K ×ˢ {(0 : Fin 3 → ℝ)} ⊆ R ⁻¹' e.target := by
    rintro ⟨q,v⟩ ⟨hq,hv⟩
    have hv0 : v = 0 := hv
    subst v
    change R (q,0) ∈ e.target
    rw [←he0 q]
    exact e.map_source (h0 q hq)
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton (e.open_target.preimage hR.continuous) hsub
  obtain ⟨r₁,hr₁,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  let r := r₁/2
  have hr : 0 < r := half_pos hr₁
  let L := metricFrameSet g K ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) r
  have hL : IsCompact L := (metricFrameSet_isCompact g hK).prod (isCompact_closedBall 0 r)
  have hLt : R '' L ⊆ e.target := by
    rintro _ ⟨⟨q,v⟩,⟨hq,hv⟩,rfl⟩
    exact hUV ⟨hKU hq,hrV ((Metric.closedBall_subset_ball (half_lt_self hr₁)) hv)⟩
  obtain ⟨ψ,hψ,hEq⟩ := smooth_extension_near_compact (hL.image hR.continuous)
    e.open_target hLt hi.snd
  let f : NormalWaveParameter × (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
    fun w => normalWaveEquiv.symm (ψ (R w))
  have hf : ContDiff ℝ ∞ f := normalWaveEquiv.symm.contDiff.comp (hψ.comp hR)
  have hfEq (w : NormalWaveParameter × (Fin 3 → ℝ)) (hw : w ∈ L) :
      f w = normalWaveEquiv.symm (e.symm (R w)).2 := by
    change normalWaveEquiv.symm (ψ (R w)) = _
    congr 1
    exact ((hEq.filter_mono (nhds_le_nhdsSet (mem_image_of_mem R hw))).self_of_nhds).symm
  have hf0 (q : NormalWaveParameter) (hq : q ∈ metricFrameSet g K) : f (q,0) = 0 := by
    rw [hfEq (q,0) ⟨hq,Metric.mem_closedBall_self hr.le⟩,←he0 q,e.left_inv (h0 q hq)]
    exact map_zero _
  obtain ⟨C₀,hC₀⟩ := hL.exists_bound_of_continuousOn
    ((continuous_parameter_iteratedFDeriv f hf 1).continuousOn)
  let C := max 1 C₀
  refine ⟨r,hr,C,le_max_left _ _,?_⟩
  intro q hq v hv
  have hvmem : v ∈ Metric.closedBall (0 : Fin 3 → ℝ) r := by
    simpa [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨f (q,v),?_,?_⟩
  · have htarget : R (q,v) ∈ e.target := hLt (mem_image_of_mem R ⟨hq,hvmem⟩)
    have hright := e.right_inv htarget
    have hfst : (e.symm (R (q,v))).1 = q := by
      have hh := congrArg Prod.fst hright
      simpa only [he,normalFamilyTotal,R] using hh
    have hsnd := congrArg Prod.snd hright
    rw [he] at hsnd
    change normalJetMap (e.symm (R (q,v))).1.1 (e.symm (R (q,v))).1.2
      ((metricChristoffel g (e.symm (R (q,v))).1.1).bilinearComp
        (e.symm (R (q,v))).1.2 (e.symm (R (q,v))).1.2) (e.symm (R (q,v))).2 =
      q.1+normalWaveEquiv v at hsnd
    rw [hfst] at hsnd
    rw [hfEq (q,v) ⟨hq,hvmem⟩]
    simpa only [normalCoordinateMap,ContinuousLinearEquiv.apply_symm_apply,map_add,
      ContinuousLinearEquiv.symm_apply_apply] using congrArg normalWaveEquiv.symm hsnd
  · have hm := (convex_closedBall (0 : Fin 3 → ℝ) r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z)
      (fun z hz => by
        have hb := hC₀ (q,z) ⟨hq,hz⟩
        rw [norm_iteratedFDeriv_one] at hb
        exact hb.trans (le_max_right 1 C₀))
      (Metric.mem_closedBall_self hr.le) hvmem
    simpa only [Function.comp_apply,id_eq,hf0 q hq,sub_zero] using hm


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped Topology ContDiff

theorem metric_center_polynomial_net
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ Q > 0, ∀ n : ℝ, 1 ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
        (t.card : ℝ) ≤ Q*n^3 ∧
        ∀ y ∈ normalWaveEquiv.symm '' K, ∃ i : t, ∃ x : Fin 3 → ℝ,
          ‖x‖ < r₀ ∧ ‖x‖ ≤ 1/n ∧ normalCoordinateMap g (p i) x = y := by
  classical
  obtain ⟨ρ,hρ,A,hA,hInv⟩ := normalCoordinateMap_inverse_bound g hK
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let c := min ρ (min (r₀/(2*A)) (1/A))
  have hc : 0 < c := lt_min hρ (lt_min (div_pos hr₀ (by positivity)) (div_pos zero_lt_one hA0))
  obtain ⟨Q,hQ,hnet⟩ := compact_three_polynomial_net
    (hK.image normalWaveEquiv.symm.continuous) c hc
  refine ⟨Q,hQ,?_⟩
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨t,ht,htcard,htcover⟩ := hnet n hn
  have hcenter (i : t) : normalWaveEquiv i.1 ∈ K := by
    obtain ⟨z,hz,hzi⟩ := ht i.property
    rw [←hzi,ContinuousLinearEquiv.apply_symm_apply]
    exact hz
  choose F hF using (fun i : t => metricFrameSet_fiber_nonempty g (hcenter i))
  let p : t → metricFrameSet g K := fun i => ⟨(normalWaveEquiv i.1,F i),hF i⟩
  refine ⟨t,p,htcard,?_⟩
  intro y hy
  obtain ⟨z,hz,hd⟩ := htcover y hy
  let i : t := ⟨z,hz⟩
  let v := y-z
  have hv : ‖v‖ ≤ c/n := by simpa [v,dist_eq_norm] using hd
  have hcn : c/n ≤ c := div_le_self hc.le hn
  have hvρ : ‖v‖ ≤ ρ := hv.trans (hcn.trans (min_le_left _ _))
  obtain ⟨x,hx,hxb⟩ := hInv (p i) (p i).property v hvρ
  refine ⟨i,x,?_,?_,?_⟩
  · have hb : A*c ≤ r₀/2 := by
      have hc' : c ≤ r₀/(2*A) := (min_le_right _ _).trans (min_le_left _ _)
      have h' := (le_div_iff₀ (show 0 < 2*A by positivity)).mp hc'
      nlinarith
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*c := mul_le_mul_of_nonneg_left (hv.trans hcn) hA0.le
      _ ≤ r₀/2 := hb
      _ < r₀ := half_lt_self hr₀
  · have hb : A*c ≤ 1 := by
      have hc' : c ≤ 1/A := (min_le_right _ _).trans (min_le_right _ _)
      nlinarith [(le_div_iff₀ hA0).mp hc']
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*(c/n) := mul_le_mul_of_nonneg_left hv hA0.le
      _ = (A*c)/n := by ring
      _ ≤ 1/n := div_le_div_of_nonneg_right hb hn0.le
  · have heq : normalWaveEquiv.symm (p i).1.1 = z := normalWaveEquiv.symm_apply_apply z
    rw [heq] at hx
    simpa only [v,add_sub_cancel] using hx

end

open Set
open scoped Topology ContDiff
theorem metric_center_polynomial_net_with_coverage
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ Q > 0, ∀ n : ℝ, 1 ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
        (t.card : ℝ) ≤ Q*n^3 ∧
        ∀ y ∈ normalWaveEquiv.symm '' K, ∃ i : t, ∃ x : Fin 3 → ℝ,
          ‖x‖ < r₀ ∧ ‖x‖ ≤ 1/n ∧ normalCoordinateMap g (p i) x = y ∧
          n*‖normalWaveEquiv y-(p i).1.1‖ ≤ 1 := by
  classical
  obtain ⟨ρ,hρ,A,hA,hInv⟩ := normalCoordinateMap_inverse_bound g hK
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let B := ‖normalWaveEquiv.toContinuousLinearMap‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  let c := min (min ρ (min (r₀/(2*A)) (1/A))) (1/B)
  have hc : 0 < c := lt_min (lt_min hρ (lt_min (div_pos hr₀ (by positivity)) (div_pos zero_lt_one hA0))) (div_pos zero_lt_one hB)
  obtain ⟨Q,hQ,hnet⟩ := compact_three_polynomial_net
    (hK.image normalWaveEquiv.symm.continuous) c hc
  refine ⟨Q,hQ,?_⟩
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨t,ht,htcard,htcover⟩ := hnet n hn
  have hcenter (i : t) : normalWaveEquiv i.1 ∈ K := by
    obtain ⟨z,hz,hzi⟩ := ht i.property
    rw [←hzi,ContinuousLinearEquiv.apply_symm_apply]
    exact hz
  choose F hF using (fun i : t => metricFrameSet_fiber_nonempty g (hcenter i))
  let p : t → metricFrameSet g K := fun i => ⟨(normalWaveEquiv i.1,F i),hF i⟩
  refine ⟨t,p,htcard,?_⟩
  intro y hy
  obtain ⟨z,hz,hd⟩ := htcover y hy
  let i : t := ⟨z,hz⟩
  let v := y-z
  have hv : ‖v‖ ≤ c/n := by simpa [v,dist_eq_norm] using hd
  have hcn : c/n ≤ c := div_le_self hc.le hn
  have hvρ : ‖v‖ ≤ ρ := hv.trans (hcn.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨x,hx,hxb⟩ := hInv (p i) (p i).property v hvρ
  refine ⟨i,x,?_,?_,?_,?_⟩
  · have hb : A*c ≤ r₀/2 := by
      have hc' : c ≤ r₀/(2*A) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have h' := (le_div_iff₀ (show 0 < 2*A by positivity)).mp hc'
      nlinarith
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*c := mul_le_mul_of_nonneg_left (hv.trans hcn) hA0.le
      _ ≤ r₀/2 := hb
      _ < r₀ := half_lt_self hr₀
  · have hb : A*c ≤ 1 := by
      have hc' : c ≤ 1/A := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [(le_div_iff₀ hA0).mp hc']
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*(c/n) := mul_le_mul_of_nonneg_left hv hA0.le
      _ = (A*c)/n := by ring
      _ ≤ 1/n := div_le_div_of_nonneg_right hb hn0.le
  · have heq : normalWaveEquiv.symm (p i).1.1 = z := normalWaveEquiv.symm_apply_apply z
    rw [heq] at hx
    simpa only [v,add_sub_cancel] using hx

  · have hBc : B*c ≤ 1 := by
      have hh : c ≤ 1/B := min_le_right _ _
      have hh' := (le_div_iff₀ hB).mp hh
      nlinarith
    have hdist : ‖normalWaveEquiv y-(p i).1.1‖ ≤ B*(c/n) := by
      change ‖normalWaveEquiv y-normalWaveEquiv z‖ ≤ _
      rw [←map_sub]
      calc
        _ ≤ ‖normalWaveEquiv.toContinuousLinearMap‖*‖v‖ := normalWaveEquiv.toContinuousLinearMap.le_opNorm v
        _ ≤ B*‖v‖ := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
        _ ≤ B*(c/n) := mul_le_mul_of_nonneg_left hv hB.le
    calc
      _ ≤ n*(B*(c/n)) := mul_le_mul_of_nonneg_left hdist hn0.le
      _ = B*c := by field_simp
      _ ≤ 1 := hBc


end YauCounterexamples
end

end OAI
