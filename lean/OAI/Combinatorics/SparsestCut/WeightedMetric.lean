import OAI.Combinatorics.SparsestCut.VertexMeasure

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceWeighted
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
open SourceCharts SourceParameters SourceMetric
noncomputable section
local instance {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
local instance {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance

def D : ℝ := 4*KernelApprox.cstar+C₀
lemma D_pos : 0<D := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  unfold D
  positivity
lemma diameter {m : ℕ} [NeZero m] (f : PivotFamily.PFamily m) (hm : 3000 ≤ m)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (v w : V f) : ‖Z v-Z w‖^2≤D*m := by
  obtain ⟨θ,hθ,hr,he⟩ := v.property
  obtain ⟨η,hη,hs,hf⟩ := w.property
  have hv : vertex f v.val.1 θ hθ hr=v := by apply Subtype.ext; change (v.val.1,_)=(v.val.1,_); rw [he]
  have hw : vertex f w.val.1 η hη hs=w := by apply Subtype.ext; change (w.val.1,_)=(w.val.1,_); rw [hf]
  have hh := (abs_le.mp (macro_bound f hm Z hmac v.val.1 w.val.1 θ η hθ hη hr hs)).2
  rw [hv,hw] at hh
  have hn : ‖θ-η‖≤4*Real.sqrt m := by
    have h1 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
    have h2 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hη
    have h3 := norm_sub_le θ η
    linarith
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : p m 8 ≤ (m:ℝ) := (p_one_le hx _).trans hx
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)
  have h1 := mul_le_mul_of_nonneg_left hn (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg m))
  have h2 := mul_le_mul_of_nonneg_left hp C₀_pos.le
  have he : KernelApprox.cstar*Real.sqrt m*(4*Real.sqrt m)=4*KernelApprox.cstar*(m:ℝ) := by
    calc
      _ = 4*KernelApprox.cstar*(Real.sqrt m)^2 := by ring
      _ = _ := by rw [hq]
  rw [he] at h1
  unfold D
  linarith only [hh,h1,h2]

lemma weighted_instance {m : ℕ} (f : PivotFamily.PFamily (m+1))
    (hm : 3000 ≤ m+1) (hl : 1≤Real.log (m+1:ℕ)) (hH : SourceContraction.H ≤ (m+1:ℕ)) :
    ∃ (Z : V f → EuclideanSpace ℝ (V f)) (w : V f → ℝ),
      (∀ v, 0≤w v) ∧ (∑ v, w v)=1 ∧
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v z, ‖Z v-Z z‖^2≤D*(m+1:ℕ)) ∧
      KernelApprox.cstar/3*(m+1:ℕ)-C₀*p (m+1:ℕ) 8≤∑ v, ∑ z, w v*w z*‖Z v-Z z‖^2 ∧
      ∀ (A : Type) [Fintype A] (F : V f → A → ℝ),
        (∀ v z, (∑ a, |F v a-F z a|)≤‖Z v-Z z‖^2) →
        (∑ v, ∑ z, w v*w z*(∑ a, |F v a-F z a|))≤SourceContraction.C*SourceContraction.weight (m+1) := by
  classical
  let d := m+1
  let E := EuclideanSpace ℝ (Fin d)
  let μ := CubePoincare.cube (m:=d)
  have hm0 : 0 < d := Nat.succ_pos m
  have hx0 : (0:ℝ) < d := by exact_mod_cast hm0
  have hτ := p_pos hx0 2000
  have hu0 : ∀ s i, u f s i 0≠0 := by
    intro s i h
    have hp := u_pivot f hm0 s i 0
    rw [h,abs_zero] at hp
    have hh : (0:ℝ)<1/((d:ℝ)^30*Real.sqrt d) := by positivity
    linarith
  have hu : ∀ s i, u f s i≠0 := by
    intro s i h
    exact hu0 s i (by rw [h]; rfl)
  let s : Fin (d^3) := ⟨0,by positivity⟩
  obtain ⟨v₀⟩ := VertexMeasure.vertex_nonempty (u f) hu (p d 2000) s
  let L := VertexMeasure.label (u f) (p d 2000) s v₀
  let ν := VertexMeasure.measure (u f) (p d 2000) s v₀
  let w : V f → ℝ := fun v => ν.real {v}
  have hws : (∑ v, w v)=1 := VertexMeasure.finite_weights ν
  have hw : ∀ v, 0≤w v := fun v => measureReal_nonneg
  have hL := VertexMeasure.label_measurable (u f) (p d 2000) s v₀
  have hgood : ∀ᵐ x : E ∂μ, x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) x :=
    VertexMeasure.ae_good (u f s) (hu s) (p d 2000)
  have hgoodpair : ∀ᵐ z : E × E ∂μ.prod μ,
      (z.1∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) z.1) ∧
      (z.2∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) z.2) := by
    apply (Measure.ae_prod_iff_ae_ae (MeasurableSet.prod
      ((VertexMeasure.cube_measurable 2).inter (VertexMeasure.regular_measurable (u f s) (p d 2000)))
      ((VertexMeasure.cube_measurable 2).inter (VertexMeasure.regular_measurable (u f s) (p d 2000))))).mpr
    filter_upwards [hgood] with x hx
    filter_upwards [hgood] with y hy
    exact ⟨hx,hy⟩
  obtain ⟨Z,htri,hmac,hloc⟩ := SourceMetric.realization f hm hl
  have hdiam := diameter f hm Z hmac
  refine ⟨Z,w,hw,hws,htri,hdiam,?_,?_⟩
  · rw [VertexMeasure.pair_average (u f) (p d 2000) s v₀]
    have hi : Integrable (fun z : E × E => ‖Z (L z.1)-Z (L z.2)‖^2) (μ.prod μ) := by
      apply (integrable_const (D*d)).mono'
      · exact ((measurable_of_countable (fun z : V f × V f => ‖Z z.1-Z z.2‖^2)).comp (hL.prodMap hL)).aestronglyMeasurable
      · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hdiam _ _)
    have hb : (∫ z : E × E, KernelApprox.cstar*Real.sqrt d*‖z.1-z.2‖-C₀*p d 8 ∂μ.prod μ)≤
        ∫ z : E × E, ‖Z (L z.1)-Z (L z.2)‖^2 ∂μ.prod μ := by
      apply integral_mono_ae ((CubeGeometry.pair_norm_integrable.const_mul _).sub (integrable_const _)) hi
      filter_upwards [hgoodpair] with z hz
      have he1 : L z.1=vertex f s z.1 hz.1.1 hz.1.2 := by
        exact dite_eq_left hz.1
      have he2 : L z.2=vertex f s z.2 hz.2.1 hz.2.2 := by
        exact dite_eq_left hz.2
      rw [he1,he2]
      have hh := (abs_le.mp (macro_bound f hm Z hmac s s z.1 z.2 hz.1.1 hz.2.1 hz.1.2 hz.2.2)).1
      change KernelApprox.cstar*Real.sqrt (m+1:ℕ)*‖z.1-z.2‖-C₀*p (m+1:ℕ) 8≤_
      linarith only [hh]
    rw [integral_sub (CubeGeometry.pair_norm_integrable.const_mul _) (integrable_const _),integral_const_mul,integral_const] at hb
    simp at hb
    have ha := mul_le_mul_of_nonneg_left (CubeGeometry.pair_norm_average hm0)
      (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg d))
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)
    change KernelApprox.cstar/3*(d:ℝ)-C₀*p d 8≤_
    have he : KernelApprox.cstar*Real.sqrt d*(Real.sqrt d/3)=KernelApprox.cstar/3*(d:ℝ) := by
      calc
        _ = KernelApprox.cstar/3*(Real.sqrt d)^2 := by ring
        _ = _ := by rw [hs]
    rw [he] at ha
    linarith only [ha,hb]
  · intro A hA F hF
    rw [VertexMeasure.pair_average (u f) (p d 2000) s v₀]
    have he : (fun z : E × E => ∑ a, |F (L z.1) a-F (L z.2) a|)=ᵐ[μ.prod μ]
        (fun z => ∑ a, |ConcreteCells.function (u f) hu0 (p d 2000) F s a z.1-
          ConcreteCells.function (u f) hu0 (p d 2000) F s a z.2|) := by
      filter_upwards [hgoodpair] with z hz
      apply Finset.sum_congr rfl
      intro a ha
      rw [ConcreteCells.function_eq (u f) hu0 hτ (fun s i => (u_norm f hm0 s i).2) F s z.1 hz.1.1 hz.1.2 a,
        ConcreteCells.function_eq (u f) hu0 hτ (fun s i => (u_norm f hm0 s i).2) F s z.2 hz.2.1 hz.2.2 a]
      simp [L, VertexMeasure.label, hz.1, hz.2]
    rw [integral_congr_ae he]
    exact SourceContraction.integral_bound f hm hl hH Z hmac hloc F hF s
end
end UniformSparsestCut.SourceWeighted

end

end OAI
