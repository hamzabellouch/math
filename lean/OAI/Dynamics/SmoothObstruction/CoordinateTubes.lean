import OAI.Dynamics.SmoothObstruction.SpectralBins

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Ambient open carrier of an arbitrary open subset of a chart source.
It does not assert a smooth extension across a manifold boundary. -/
def carrier (a : M) (U : Set M) : Set (EuclideanSpace ℝ (Fin d)) :=
  I.symm ⁻¹' ((chartAt H a).target∩(chartAt H a).symm ⁻¹' U)

lemma isOpen_carrier (a : M) {U : Set M} (hU : IsOpen U) : IsOpen (carrier I a U) :=
  ((chartAt H a).isOpen_inter_preimage_symm hU).preimage I.continuous_symm

lemma coord_mem_carrier (a x : M) {U : Set M}
    (hx : x∈(chartAt H a).source) (hU : x∈U) :
    (extChartAt I a) x∈carrier I a U := by
  have ht := (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx)
  have htar : I.symm ((extChartAt I a) x)∈(chartAt H a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at ht
    exact ht.1
  refine ⟨htar,?_⟩
  change (extChartAt I a).symm ((extChartAt I a) x)∈U
  rwa [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx)]

lemma mem_of_coord_mem_carrier (a y : M) {U : Set M}
    (hy : y∈(chartAt H a).source) (hu : (extChartAt I a) y∈carrier I a U) : y∈U := by
  have hh := hu.2
  change (extChartAt I a).symm ((extChartAt I a) y)∈U at hh
  rwa [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hy)] at hh

/-- Compact charts provide a uniform positive COORDINATE margin for any
specified finite open enlargement, also in half-space models. -/
theorem uniform_margin {ι : Type*} [Fintype ι] (a : ι → M) (K U : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) (hKs : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ → y∈U i := by
  let L (i : ι) := (extChartAt I (a i)) '' K i
  have hL (i : ι) : IsCompact (L i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (I:=I) (a i)).mono
      (fun _ hx => by simpa only [extChartAt_source] using hKs i hx))
  have hex (i : ι) : ∃ r : ℝ,0<r ∧ cthickening r (L i)⊆carrier I (a i) (U i) := by
    apply (hL i).exists_cthickening_subset_open (isOpen_carrier I _ (hU i))
    rintro z ⟨x,hx,rfl⟩
    exact coord_mem_carrier I _ _ (hKs i hx) (hKU i hx)
  choose r hr hu using hex
  obtain ⟨δ,hδ,hδr⟩ := CarriedCharts.finite_positive_lower r hr
  refine ⟨δ,hδ,fun i x hx y hy hxy => ?_⟩
  apply mem_of_coord_mem_carrier I _ _ hy
  apply hu i
  apply closedBall_subset_cthickening (E:=L i) ⟨x,hx,rfl⟩ (r i)
  simpa only [mem_closedBall,dist_eq_norm] using hxy.trans (hδr i)

end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- In a compatible metric, the same coordinate margin puts nearby
carried points in any prescribed geometric atlas tube. -/
theorem uniform_metric_tube {ι : Type*} [Fintype ι]
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKs : ∀ i,K i⊆(chartAt H (a i)).source) {r : ℝ} (hr : 0<r) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ →
        y∈cthickening r (K i) := by
  obtain ⟨δ,hδ,hh⟩ := uniform_margin I a K (fun i => thickening r (K i)) hK
    (fun i => isOpen_thickening) (fun i => self_subset_thickening hr _) hKs
  exact ⟨δ,hδ,fun i x hx y hy hxy => thickening_subset_cthickening r _ (hh i x hx y hy hxy)⟩
end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- Uniform inverse-chart modulus on finitely many compact patches. This
works with a closed model range, so includes the closed half-space without
postulating an ambient extension of an inverse chart. -/
theorem uniform_inverse_modulus {ι : Type*} [Fintype ι]
    (hclosed : IsClosed (range I)) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKs : ∀ i,K i⊆(chartAt H (a i)).source)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ → dist y x<ε := by
  let L (i : ι) := (extChartAt I (a i)) '' K i
  have hL (i : ι) : IsCompact (L i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (I:=I) (a i)).mono
      (fun _ hx => by simpa only [extChartAt_source] using hKs i hx))
  have hex (i : ι) : ∃ r : ℝ,0<r ∧ cthickening r (L i)⊆carrier I (a i) univ := by
    apply (hL i).exists_cthickening_subset_open (isOpen_carrier I _ isOpen_univ)
    rintro z ⟨x,hx,rfl⟩
    exact coord_mem_carrier I _ _ (hKs i hx) (mem_univ _)
  choose r hr hu using hex
  let Q (i : ι) := cthickening (r i) (L i)∩range I
  have hQt (i : ι) : Q i⊆(extChartAt I (a i)).target := by
    intro z hz
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨(hu i hz.1).1,hz.2⟩
  have hQ (i : ι) : IsCompact (Q i) := (hL i).cthickening.inter_right hclosed
  have hm (i : ι) : ∃ s : ℝ,0<s ∧ ∀ u∈Q i,∀ v∈Q i,dist u v<s →
      dist ((extChartAt I (a i)).symm u) ((extChartAt I (a i)).symm v)<ε :=
    Metric.uniformContinuousOn_iff.mp ((hQ i).uniformContinuousOn_of_continuous
      ((continuousOn_extChartAt_symm (I:=I) (a i)).mono (hQt i))) ε hε
  choose s hs hm using hm
  obtain ⟨δ,hδ,hδi⟩ := CarriedCharts.finite_positive_lower
    (fun i => min (r i) (s i/2)) (fun i => lt_min (hr i) (div_pos (hs i) (by norm_num)))
  refine ⟨δ,hδ,fun i x hx y hy hxy => ?_⟩
  have hxt : x∈(extChartAt I (a i)).source := by simpa only [extChartAt_source] using hKs i hx
  have hyt : y∈(extChartAt I (a i)).source := by simpa only [extChartAt_source] using hy
  have hxQ : (extChartAt I (a i)) x∈Q i := ⟨self_subset_cthickening (L i) ⟨x,hx,rfl⟩,
    by exact ⟨(chartAt H (a i)) x,rfl⟩⟩
  have hyQ : (extChartAt I (a i)) y∈Q i := ⟨
    mem_cthickening_of_dist_le _ _ _ _ ⟨x,hx,rfl⟩
      (by simpa only [dist_eq_norm] using hxy.trans ((hδi i).trans (min_le_left _ _))),
    ⟨(chartAt H (a i)) y,rfl⟩⟩
  have hh := hm i _ hyQ _ hxQ (show dist ((extChartAt I (a i)) y) ((extChartAt I (a i)) x)<s i from
    (by rw [dist_eq_norm]; exact lt_of_le_of_lt (hxy.trans ((hδi i).trans (min_le_right _ _))) (by linarith [hs i])))
  simpa only [(extChartAt I (a i)).left_inv hyt,(extChartAt I (a i)).left_inv hxt] using hh
end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A uniform coordinate ball restricted to the model range lies in the
actual inverse-chart domain. This is a target statement, not an assertion
about the total value assigned to a partial chart outside its source. -/
theorem uniform_target_tube {ι : Type*} [Fintype ι]
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKs : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r : ℝ,0<r ∧ ∀ i x,x∈K i →
      closedBall ((extChartAt I (a i)) x) r∩range I⊆(extChartAt I (a i)).target := by
  let L (i : ι) := (extChartAt I (a i)) '' K i
  have hL (i : ι) : IsCompact (L i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (I:=I) (a i)).mono
      (fun _ hx => by simpa only [extChartAt_source] using hKs i hx))
  have hex (i : ι) : ∃ r : ℝ,0<r ∧ cthickening r (L i)⊆carrier I (a i) univ := by
    apply (hL i).exists_cthickening_subset_open (isOpen_carrier I _ isOpen_univ)
    rintro z ⟨x,hx,rfl⟩
    exact coord_mem_carrier I _ _ (hKs i hx) (mem_univ _)
  choose r hr hu using hex
  obtain ⟨δ,hδ,hδr⟩ := CarriedCharts.finite_positive_lower r hr
  refine ⟨δ,hδ,fun i x hx z hz => ?_⟩
  rw [extChartAt,OpenPartialHomeomorph.extend_target]
  exact ⟨(hu i ((closedBall_subset_cthickening (E:=L i) ⟨x,hx,rfl⟩ (r i))
    (closedBall_subset_closedBall (hδr i) hz.1))).1,hz.2⟩
end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Restriction of an actual bilateral gauge keeps exactly the same bases,
not a recomputed QR path or a newly chosen stationary witness. -/
def BilateralGauge.restrict (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n N : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x) (hN : N≤n) :
    BilateralGauge I S a c N B R x where
  lam := A.lam
  rate_bound := A.rate_bound
  UF := A.UF
  VF := A.VF
  UB := A.UB
  VB := A.VB
  invF := A.invF
  invB := A.invB
  centerU := A.centerU
  centerV := A.centerV
  normF t ht := A.normF t (ht.trans hN)
  normB t ht := A.normB t (ht.trans hN)
  stepF t ht := A.stepF t (ht.trans_le hN)
  stepB t ht := A.stepB t (ht.trans_le hN)

omit [ProperSpace M] in
/-- Strengthen actual short comparison by a prescribed uniform atlas tube.
Membership of the nearby orbit at ALL intermediate times is a conclusion. -/
theorem actual_tube_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ (c : ℕ → ι) (x y : M) (N : ℕ),
      (∀ t≤N,S^[t] x∈K (c t)) → I.IsInteriorPoint x → I.IsInteriorPoint y →
      y∈(chartAt H (a (c 0))).source →
      C ^ N*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖≤r →
      (∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
        S^[t] y∈cthickening τ (K (c t))) ∧
      ‖fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) y)-
        fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) x)‖≤
          N*C*C ^ (2*N)*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ := by
  obtain ⟨r,C,hr,hC,hh⟩ := actual_short_comparison I hclosed S a K hK hKU
  obtain ⟨δ,hδ,hmargin⟩ := CoordinateTubes.uniform_metric_tube I a K hK hKU hτ
  refine ⟨min r δ,C,lt_min hr hδ,hC,fun c x y N hx hxi hyi hys hsmall => ?_⟩
  obtain ⟨ht,hd⟩ := hh c x y N hx hxi hyi hys (hsmall.trans (min_le_left _ _))
  refine ⟨fun t htn => ⟨(ht t htn).1,?_⟩,hd⟩
  apply hmargin (c t) (S^[t] x) (hx t htn) _ (ht t htn).1
  apply (ht t htn).2.trans
  apply le_trans _ (hsmall.trans (min_le_right _ _))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC htn) (norm_nonneg _)

/-- Genuine good-path gauges can be attached simultaneously to the two
reference chart codes of a nearby orbit. No continued chart membership,
frame continuity, or derivative comparison is an extra hypothesis. -/
theorem uniform_genuine_bin_gauges (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0<rF ∧ 1≤CF ∧ 0<rB ∧ 1≤CB ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cF cB : ℕ → ι)
        (n N : ℕ) (B R h : ℝ) (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n → cB 0=cF 0 →
        (∀ t≤N,S^[t] (x e)∈K (cF t)) →
        (∀ t≤N,S.symm^[t] (x e)∈K (cB t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (cF 0))).source) →
        (∀ i,‖(extChartAt I (a (cF 0))) (x i)-(extChartAt I (a (cF 0))) (x e)‖≤h) →
        CF^N*h≤rF → CB^N*h≤rB →
        ∃ F Z : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i k,(F i).lam k=(A i).lam k ∧ (Z i).lam k= -(A i).lam k) ∧
          (∀ i,(Z i).U 0=(F i).U 0 ∧ (Z i).V 0=(F i).V 0) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (cF t)) (a (cF (t+1))) (S^[t] (x i)))*(F i).U t=
              (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S.symm (a (cB t)) (a (cB (t+1))) (S.symm^[t] (x i)))*(Z i).U t=
              (Z i).U (t+1)*EuclideanSplitting.rate (Z i).lam 1) ∧
          (∀ i,‖(F i).product-(F e).product‖≤N*CF*CF^(2*N)*h) ∧
          (∀ i,‖(Z i).product-(Z e).product‖≤N*CB*CB^(2*N)*h) ∧
          ∀ i t,t≤N →
            (F i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] (x i)))) (a (cF t)) (S^[t] (x i)))*(A i).UF t ∧
            (F i).V t=(A i).VF t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cF t)) (a (c (S^[t] (x i)))) (S^[t] (x i))) ∧
            (Z i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S.symm^[t] (x i)))) (a (cB t)) (S.symm^[t] (x i)))*(A i).UB t ∧
            (Z i).V t=(A i).VB t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cB t)) (a (c (S.symm^[t] (x i)))) (S.symm^[t] (x i))) := by
  classical
  obtain ⟨τ,D,hτ,hD,hcarry⟩ := uniform_carried_bilateral_explicit I a K hK hKU
  obtain ⟨rF,CF,hrF,hCF,hhF⟩ := actual_tube_comparison I hclosed S a K hK hKU hτ
  obtain ⟨rB,CB,hrB,hCB,hhB⟩ := actual_tube_comparison I hclosed S.symm a K hK hKU hτ
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,
    fun c J x e cF cB n N B R h A hc hN h0 hxF hxB hint hsource hdist hsF hsB => ?_⟩
  have hdistB (i : J) : ‖(extChartAt I (a (cB 0))) (x i)-(extChartAt I (a (cB 0))) (x e)‖≤h := by
    simpa only [h0] using hdist i
  have hsourceB (i : J) : x i∈(chartAt H (a (cB 0))).source := by
    simpa only [h0] using hsource i
  have htF (i : J) := hhF cF (x e) (x i) N hxF (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg (zero_le_one.trans hCF) N)).trans hsF)
  have htB (i : J) := hhB cB (x e) (x i) N hxB (hint e) (hint i) (hsourceB i)
    ((mul_le_mul_of_nonneg_left (hdistB i) (pow_nonneg (zero_le_one.trans hCB) N)).trans hsB)
  choose F Z hFlam hZlam hU hV hstepF hstepB hform using fun i =>
    hcarry S c (x i) N B R ((A i).restrict I S a c hN) cF cB hc h0
      (fun t ht => ((htF i).1 t ht).2) (fun t ht => ((htB i).1 t ht).2)
  refine ⟨F,Z,fun i k => ⟨hFlam i k,hZlam i k⟩,fun i => ⟨hU i,hV i⟩,hstepF,hstepB,?_,?_,?_⟩
  · intro i
    have hp (j : J) := actual_gauge_product I S (fun t => a (cF t)) (x j) (F j)
      (fun t ht => ((htF j).1 t ht).1) (hint j) (hstepF j)
    rw [←hp i,←hp e]
    exact ((htF i).2).trans (mul_le_mul_of_nonneg_left (hdist i) (by positivity))
  · intro i
    have hp (j : J) := actual_gauge_product I S.symm (fun t => a (cB t)) (x j) (Z j)
      (fun t ht => ((htB j).1 t ht).1) (hint j) (hstepB j)
    rw [←hp i,←hp e]
    exact ((htB i).2).trans (mul_le_mul_of_nonneg_left (hdistB i) (by positivity))
  · exact hform
end SmoothObstruction.ManifoldCoordinates

end

end OAI
