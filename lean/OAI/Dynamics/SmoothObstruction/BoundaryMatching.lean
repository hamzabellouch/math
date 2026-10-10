import OAI.Dynamics.SmoothObstruction.CoordinateTubes
import OAI.Dynamics.SmoothObstruction.GreenOperator

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

noncomputable def Gauge.evolution (A : Gauge d n K) :=
  EuclideanSplitting.evolution A.U A.V A.lam A.UV A.VU
noncomputable def Gauge.splitting (A : Gauge d n K) (S : Finset (Fin d)) :=
  EuclideanSplitting.splitting A.U A.V A.lam A.UV A.VU S

lemma Gauge.space_eq_range (A : Gauge d n K) (S : Finset (Fin d)) :
    A.space S=((A.splitting S).slow 0).range :=
  (splitting_slow_range _ _ _ _ _ _ _).symm

/-- The orthogonal common-bin space comparisons construct the middle
matching equivalence for two genuine gauges with a possibly positive slow
threshold. Complementarity is proved, not assumed for the moving spaces. -/
theorem gauge_matching (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    {ε : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2) :
    ∃ L : (((A.splitting S).slow 0).range×((Z.splitting T).slow 0).range) ≃L[ℝ]
      EuclideanSpace ℝ (Fin d),
      (∀ x,L x=(x.1:EuclideanSpace ℝ (Fin d))-(x.2:EuclideanSpace ℝ (Fin d))) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*Real.exp (2*K) := by
  let B := A₀.splitting S₀
  have hs : ‖B.slow 0‖≤Real.exp (2*K) :=
    splitting_slow_norm _ _ _ _ _ _ 0 (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hf : ‖B.fast 0‖≤Real.exp (2*K) :=
    splitting_fast_norm _ _ _ _ _ _ 0 (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have heS : (B.slow 0).range=A₀.space S₀ := (A₀.space_eq_range S₀).symm
  have heT : (B.fast 0).range=A₀.space S₀ᶜ :=
    splitting_fast_range _ _ _ _ _ _ _
  have hdS' : Module.finrank ℝ (B.slow 0).range=Module.finrank ℝ ((A.splitting S).slow 0).range := by
    rw [heS,←A.space_eq_range,A₀.rank,A.rank,hdS]
  have hdT' : Module.finrank ℝ (B.fast 0).range=Module.finrank ℝ ((Z.splitting T).slow 0).range := by
    rw [heT,←Z.space_eq_range,A₀.rank,Z.rank,hdT]
  apply CloseComplement.exists_matching (B.slow 0).range (B.fast 0).range
    ((A.splitting S).slow 0).range ((Z.splitting T).slow 0).range
    (B.referenceMatching 0) (B.referenceMatching_apply 0) hdS' hdT' hε hεhalf
  · simpa only [heS,←A.space_eq_range] using hcS
  · simpa only [heT,←Z.space_eq_range] using hcT
  · exact B.referenceMatching_inverse_norm 0 hs hf
  · exact hsmall
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A one-sided family of actual gauges can be carried to reference charts
using only the short orbit interval. This is also applicable at a long-window
endpoint, without demanding good data beyond that endpoint. -/
theorem uniform_genuine_single_gauges (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0<r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cR : ℕ → ι)
        (N : ℕ) (B h : ℝ) (A : J → ShortBin.Gauge d N B),
        (∀ y,y∈K (c y)) →
        (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] (x i)))) (a (c (S^[t+1] (x i)))) (S^[t] (x i)))*(A i).U t=
            (A i).U (t+1)*EuclideanSplitting.rate (A i).lam 1) →
        (∀ t≤N,S^[t] (x e)∈K (cR t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (cR 0))).source) →
        (∀ i,‖(extChartAt I (a (cR 0))) (x i)-(extChartAt I (a (cR 0))) (x e)‖≤h) →
        C₁^N*h≤r →
        ∃ F : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i,(F i).lam=(A i).lam) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (cR t)) (a (cR (t+1))) (S^[t] (x i)))*(F i).U t=
              (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1) ∧
          (∀ i,‖(F i).product-(F e).product‖≤N*C₁*C₁^(2*N)*h) ∧
          ∀ i t,t≤N →
            (F i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] (x i)))) (a (cR t)) (S^[t] (x i)))*(A i).U t ∧
            (F i).V t=(A i).V t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cR t)) (a (c (S^[t] (x i)))) (S^[t] (x i))) := by
  classical
  obtain ⟨τ,D,hτ,hD,hcarry⟩ := uniform_carried_gauge_explicit I a K hK hKU
  obtain ⟨r,C₁,hr,hC,hh⟩ := actual_tube_comparison I hclosed S a K hK hKU hτ
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e cR N B h A hc hA hx hint hsource hdist hs => ?_⟩
  have ht (i : J) := hh cR (x e) (x i) N hx (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg (zero_le_one.trans hC) N)).trans hs)
  have hc' (i : J) (t : ℕ) (_ht : t≤N) :
      S^[t] (x i)∈cthickening τ (K (c (S^[t] (x i)))) := self_subset_cthickening _ (hc _)
  choose PF QF hiF hbF hform hstep using fun i =>
    hcarry S (fun t => S^[t] (x i)) (fun t => c (S^[t] (x i))) cR
      (A i).U (A i).V (A i).lam N B (hc' i) (fun t ht' => ((ht i).1 t ht').2)
      (fun t _ => (Function.iterate_succ_apply' _ _ _).symm)
      (fun t => ⟨(A i).UV t,(A i).VU t⟩)
      (fun t ht' => ⟨(A i).normU t ht',(A i).normV t ht'⟩) (hA i)
  have hbound : D*Real.exp B=Real.exp (B+Real.log D) := by
    rw [Real.exp_add,Real.exp_log (lt_of_lt_of_le zero_lt_one hD),mul_comm]
  have hb (i : J) (t : ℕ) (ht : t≤N) :
      ‖PF i t‖≤Real.exp (B+Real.log D) ∧ ‖QF i t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbF i t ht
  let F (i : J) := ShortBin.Gauge.ofFinite (PF i) (QF i) (A i).lam (hiF i) (hb i)
  have hstep' (i : J) (t : ℕ) (ht : t<N) :
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
        (coord I S (a (cR t)) (a (cR (t+1))) (S^[t] (x i)))*(F i).U t=
          (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1 := by
    simpa only [F,ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤N by omega)] using hstep i t ht
  refine ⟨F,fun _ => rfl,hstep',?_,?_⟩
  · intro i
    have hp (j : J) := actual_gauge_product I S (fun t => a (cR t)) (x j) (F j)
      (fun t ht' => ((ht j).1 t ht').1) (hint j) (hstep' j)
    rw [←hp i,←hp e]
    exact ((ht i).2).trans (mul_le_mul_of_nonneg_left (hdist i) (by positivity))
  · intro i t ht'
    simpa only [F,ShortBin.Gauge.ofFinite,Nat.min_eq_left ht'] using hform i t

/-- The past short segment of the true forward gauge, centered at its long
endpoint. Rates are merely negated; the original starting threshold remains
available, and no new stationary witness is chosen. -/
noncomputable def BilateralGauge.endpointBackward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n N : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d N B where
  U t := A.UF (n-t)
  V t := A.VF (n-t)
  lam j := -A.lam j
  UV _t := (A.invF _).1
  VU _t := (A.invF _).2
  normU _t _ := (A.normF _ (Nat.sub_le _ _)).1
  normV _t _ := (A.normF _ (Nat.sub_le _ _)).2

omit [ProperSpace M] [Fintype ι] in
lemma BilateralGauge.endpointBackward_step (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (hc : ∀ y,y∈(chartAt H (a (c y))).source)
    {n N : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x) (hN : N≤n) :
    let F := A.endpointBackward I S a c (N:=N)
    ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (a (c (S.symm^[t] (S^[n] x))))
        (a (c (S.symm^[t+1] (S^[n] x)))) (S.symm^[t] (S^[n] x)))*F.U t=
      F.U (t+1)*EuclideanSplitting.rate F.lam 1 := by
  intro F t ht
  have hr (s : ℕ) (hs : s≤n) : S.symm^[s] (S^[n] x)=S^[n-s] x :=
    OrbitCocycle.backward_center S.toHomeomorph x hs
  rw [hr t (by omega),hr (t+1) (by omega)]
  have he : n-(t+1)+1=n-t := by omega
  have hh := reverse_gauge_step I S (fun j => a (c (S^[j] x)))
    (fun j => S^[j] x) A.UF A.lam (n-(t+1))
    (by simp only [Function.iterate_succ_apply']) (hc _) (hc _)
    (A.stepF _ (by omega))
  simpa only [he,F,BilateralGauge.endpointBackward] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Reverse the two-sided gauge without changing any coordinate basis. -/
def BilateralGauge.symm (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x) :
    BilateralGauge I S.symm a c n B R x where
  lam j := -A.lam j
  rate_bound j := by simpa only [abs_neg] using A.rate_bound j
  UF := A.UB
  VF := A.VB
  UB := A.UF
  VB := A.VF
  invF := A.invB
  invB := A.invF
  centerU := A.centerU.symm
  centerV := A.centerV.symm
  normF := A.normB
  normB := A.normF
  stepF := A.stepB
  stepB t ht := by
    have heS : S.symm.symm=S := by ext y; rfl
    simpa only [heS,neg_neg] using A.stepF t ht

/-- Quantitative endpoint comparison at a FIXED starting threshold, for all
actual witnesses reaching one endpoint bin. Only the past short segment is
used at the forward endpoint. The displayed basis identities attach the
comparison to the actual long-window spaces. -/
theorem uniform_endpoint_fast_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0<r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cR : ℕ → ι)
        (n N : ℕ) (B R h γ g : ℝ) (T : J → Finset (Fin d))
        (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ t≤N,S.symm^[t] (S^[n] (x e))∈K (cR t)) →
        (∀ i,I.IsInteriorPoint (S^[n] (x i))) →
        (∀ i,S^[n] (x i)∈(chartAt H (a (cR 0))).source) →
        (∀ i,‖(extChartAt I (a (cR 0))) (S^[n] (x i))-
          (extChartAt I (a (cR 0))) (S^[n] (x e))‖≤h) →
        C₁^N*h≤r → 0≤h →
        (∀ i,(T e).card=(T i).card) →
        (∀ i,∀ j∈(T i)ᶜ,(A i).lam j≤γ-g) →
        (∀ i,∀ j∈T i,γ+g≤(A i).lam j) →
        (let ε := Real.exp ((γ-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
        ε≤1/2) →
        ∃ F : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i j,(F i).lam j= -(A i).lam j) ∧
          (∀ i,(F i).U 0=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (c (S^[n] (x i))))
              (a (cR 0)) (S^[n] (x i)))*(A i).UF n ∧
            (F i).V 0=(A i).VF n*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cR 0))
                (a (c (S^[n] (x i)))) (S^[n] (x i)))) ∧
          ∀ i,‖((F i).space (T i)).starProjection-((F e).space (T e)).starProjection‖≤
            3*(Real.exp ((γ-g)*N+2*(B+Real.log D))*
              (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ := uniform_genuine_single_gauges I hclosed S.symm a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e cR n N B R h γ g T A hc hN hx hint
    hsource hdist ht hn hdim hslow hfast hsmall => ?_⟩
  obtain ⟨F,hlam,hstep,hprod,hform⟩ := hh c J (fun i => S^[n] (x i)) e cR N B h
    (fun i => (A i).endpointBackward I S a c) hc
    (fun i => (A i).endpointBackward_step I S a c (fun y => hKU _ (hc y)) hN)
    hx hint hsource hdist ht
  have hlam' (i : J) (j : Fin d) : (F i).lam j= -(A i).lam j := congrFun (hlam i) j
  refine ⟨F,hlam',?_,?_⟩
  · intro i
    simpa only [Function.iterate_zero_apply,BilateralGauge.endpointBackward,Nat.sub_zero]
      using hform i 0 (Nat.zero_le N)
  · intro i
    have he : -(-γ+g)=γ-g := by ring
    have hs : Real.exp (-(-γ+g)*N+2*(B+Real.log D))*
        (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)≤1/2 := by
      simpa only [he] using hsmall
    have hp : ‖(F e).product-(F i).product‖≤N*C₁*C₁^(2*N)*h := by
      rw [norm_sub_rev]
      exact hprod i
    have hcl := ShortBin.slow_projector_distance (F e) (F i) (T e) (T i) (γ := -γ)
      (hdim i) hp
      (by intro j hj; rw [hlam']; linarith [hslow e j hj])
      (by intro j hj; rw [hlam']; linarith [hfast i j hj]) (by positivity) hs
    simpa only [he] using hcl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

noncomputable def initialSpace : Submodule ℝ E := (B.slow 0).range
lemma slow_initial (x : B.initialSpace) : B.slow 0 x=x := by
  obtain ⟨v,hv⟩ := x.property
  change B.slow 0 v=x.val at hv
  rw [←hv,B.slow_self]

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)

lemma trajectory_initial (f : ℕ → E) (a : E) (ha : B.slow 0 a=a) (h : H) :
    C.trajectory f a h 0=a+C.kernel a+C.trajectory f 0 h 0 := by
  simp only [trajectory,A.forward_zero]
  simp only [terminalValue,Evolution.forward,Evolution.backward, map_add,map_sub,map_zero,
    map_sum,kernel,_root_.neg_apply,ContinuousLinearMap.coe_comp,Function.comp_apply,ha,
    zero_add]
  abel

lemma trajectory_zero : C.trajectory (fun _ => 0) 0 0=fun _ => 0 := by
  funext t
  simp [trajectory,terminalValue,Evolution.forward,Evolution.backward]

end Terminal

end Splitting

namespace Matching
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

noncomputable def correction : (B₁.initialSpace × B₂.initialSpace) →L[ℝ] E :=
  (C₁.kernel.comp (B₁.initialSpace.subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)))-
    (C₂.kernel.comp (B₂.initialSpace.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)))

omit [FiniteDimensional ℝ E] in
@[simp] lemma correction_apply (x : B₁.initialSpace × B₂.initialSpace) :
    correction C₁ C₂ x=C₁.kernel x.1-C₂.kernel x.2 := rfl

omit [FiniteDimensional ℝ E] in
lemma correction_norm {k₁ k₂ : ℝ} (hk₁ : ‖C₁.kernel‖ ≤ k₁) (hk₂ : ‖C₂.kernel‖ ≤ k₂) :
    ‖correction C₁ C₂‖ ≤ k₁+k₂ := by
  have h₁ := (norm_nonneg _).trans hk₁
  have h₂ := (norm_nonneg _).trans hk₂
  apply (correction C₁ C₂).opNorm_le_bound (by positivity)
  intro x
  calc
    _ ≤ ‖C₁.kernel x.1‖+‖C₂.kernel x.2‖ := norm_sub_le _ _
    _ ≤ k₁*‖x.1‖+k₂*‖x.2‖ := by
      gcongr
      · exact (C₁.kernel.le_opNorm _).trans (mul_le_mul_of_nonneg_right hk₁ (norm_nonneg _))
      · exact (C₂.kernel.le_opNorm _).trans (mul_le_mul_of_nonneg_right hk₂ (norm_nonneg _))
    _ ≤ k₁*‖x‖+k₂*‖x‖ := by
      gcongr
      · exact norm_fst_le x
      · exact norm_snd_le x
    _ = _ := by ring

/-- The exact two half-orbit boundary problem. The only matching input is
complementarity of the unperturbed initial spaces. The small graph terms
are inverted by a proved Neumann construction, not by assuming invertibility. -/
theorem solve (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1)
    (f₁ f₂ : ℕ → E) (h₁ : H) (h₂ : G) (m : E) :
    ∃ v₁ v₂ : ℕ → E,
      (∀ t<n₁,v₁ (t+1)=A₁.map (t+1) t (v₁ t)+f₁ t) ∧
      (∀ t<n₂,v₂ (t+1)=A₂.map (t+1) t (v₂ t)+f₂ t) ∧
      C₁.P (v₁ n₁)=h₁ ∧ C₂.P (v₂ n₂)=h₂ ∧ v₁ 0-v₂ 0=m ∧
      ∀ w₁ w₂ : ℕ → E,
        (∀ t<n₁,w₁ (t+1)=A₁.map (t+1) t (w₁ t)+f₁ t) →
        (∀ t<n₂,w₂ (t+1)=A₂.map (t+1) t (w₂ t)+f₂ t) →
        C₁.P (w₁ n₁)=h₁ → C₂.P (w₂ n₂)=h₂ → w₁ 0-w₂ 0=m →
        (∀ t≤n₁,w₁ t=v₁ t) ∧ (∀ t≤n₂,w₂ t=v₂ t) := by
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) hsmall
  let q₁ := C₁.trajectory f₁ 0 h₁ 0
  let q₂ := C₂.trajectory f₂ 0 h₂ 0
  let a := M.symm (m-q₁+q₂)
  have hM (x : B₁.initialSpace × B₂.initialSpace) :
      M x=(x.1:E)-(x.2:E)+C₁.kernel x.1-C₂.kernel x.2 := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    abel
  refine ⟨C₁.trajectory f₁ a.1 h₁,C₂.trajectory f₂ a.2 h₂,
    fun _ ht => C₁.trajectory_step _ _ _ ht,fun _ ht => C₂.trajectory_step _ _ _ ht,
    C₁.trajectory_terminal _ _ _,C₂.trajectory_terminal _ _ _,?_,?_⟩
  · rw [C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
      C₂.trajectory_initial _ _ (B₂.slow_initial _) _]
    have ha : M a=m-q₁+q₂ := M.apply_symm_apply _
    rw [hM] at ha
    change (a.1:E)+C₁.kernel a.1+q₁-((a.2:E)+C₂.kernel a.2+q₂)=m
    calc
      _ = ((a.1:E)-(a.2:E)+C₁.kernel a.1-C₂.kernel a.2)+q₁-q₂ := by abel
      _ = m := by rw [ha]; abel
  · intro w₁ w₂ hw₁ hw₂ he₁ he₂ hm
    let b₁ : B₁.initialSpace := ⟨B₁.slow 0 (w₁ 0),⟨w₁ 0,rfl⟩⟩
    let b₂ : B₂.initialSpace := ⟨B₂.slow 0 (w₂ 0),⟨w₂ 0,rfl⟩⟩
    have hv₁ := C₁.trajectory_unique f₁ b₁ (B₁.slow_initial b₁) h₁ w₁ hw₁ rfl he₁
    have hv₂ := C₂.trajectory_unique f₂ b₂ (B₂.slow_initial b₂) h₂ w₂ hw₂ rfl he₂
    have hb : M (b₁,b₂)=M a := by
      rw [M.apply_symm_apply,hM]
      rw [hv₁ 0 (by omega),hv₂ 0 (by omega),
        C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
        C₂.trajectory_initial _ _ (B₂.slow_initial _) _] at hm
      change (b₁:E)-(b₂:E)+C₁.kernel b₁-C₂.kernel b₂=m-q₁+q₂
      change (b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂)=m at hm
      calc
        _ = ((b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂))-q₁+q₂ := by abel
        _ = _ := by rw [hm]
    have hb' := M.injective hb
    have hb₁ : b₁=a.1 := congrArg Prod.fst hb'
    have hb₂ : b₂=a.2 := congrArg Prod.snd hb'
    rw [hb₁] at hv₁
    rw [hb₂] at hv₂
    exact ⟨hv₁,hv₂⟩

end Matching
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace Evolution
variable (A : Evolution E)
lemma forward_bound (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) {n t : ℕ}
    {G F : ℝ} (hG : 0≤G) (hF : 0≤F) (ht : t≤n) (ha : P 0 a=a)
    (hp : ∀ s u,s≤u → u≤n → ‖(A.map u s).comp (P s)‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) :
    ‖A.forward P f a t‖ ≤ G*‖a‖+(n:ℝ)*G*F := by
  have hterm (s u : ℕ) (hsu : s≤u) (hu : u≤n) (v : E) :
      ‖A.map u s (P s v)‖ ≤ G*‖v‖ :=
    ((A.map u s).comp (P s)).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hp s u hsu hu) (norm_nonneg _))
  have hi : ‖A.map t 0 a‖ ≤ G*‖a‖ := by
    simpa only [ha] using hterm 0 t (by omega) ht a
  unfold forward
  calc
    _ ≤ ‖A.map t 0 a‖+‖∑ j∈range t,A.map t (j+1) (P (j+1) (f j))‖ := norm_add_le _ _
    _ ≤ G*‖a‖+∑ j∈range t,G*F := by
      gcongr
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      have hjt := mem_range.mp hj
      exact (hterm (j+1) t (by omega) ht (f j)).trans
        (mul_le_mul_of_nonneg_left (hf j (by omega)) hG)
    _ ≤ _ := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      have htt : (t:ℝ)≤n := by exact_mod_cast ht
      nlinarith [mul_nonneg hG hF,mul_le_mul_of_nonneg_right htt (mul_nonneg hG hF)]

lemma backward_bound (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) {n t : ℕ}
    {G F : ℝ} (hG : 0≤G) (hF : 0≤F) (ht : t≤n) (hc : P n c=c)
    (hp : ∀ s u,s≤u → u≤n → ‖(A.map s u).comp (P u)‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) :
    ‖A.backward P f c n t‖ ≤ G*‖c‖+(n:ℝ)*G*F := by
  have hterm (s u : ℕ) (hsu : s≤u) (hu : u≤n) (v : E) :
      ‖A.map s u (P u v)‖ ≤ G*‖v‖ :=
    ((A.map s u).comp (P u)).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hp s u hsu hu) (norm_nonneg _))
  have hi : ‖A.map t n c‖ ≤ G*‖c‖ := by
    simpa only [hc] using hterm t n ht le_rfl c
  unfold backward
  calc
    _ ≤ ‖A.map t n c‖+‖∑ j∈Ico t n,A.map t (j+1) (P (j+1) (f j))‖ := norm_sub_le _ _
    _ ≤ G*‖c‖+∑ j∈Ico t n,G*F := by
      gcongr
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      have hjt := mem_Ico.mp hj
      exact (hterm t (j+1) (by omega) (by omega) (f j)).trans
        (mul_le_mul_of_nonneg_left (hf j hjt.2) hG)
    _ ≤ _ := by
      simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]
      have htt : ((n-t:ℕ):ℝ)≤n := by exact_mod_cast Nat.sub_le n t
      nlinarith [mul_nonneg hG hF,mul_le_mul_of_nonneg_right htt (mul_nonneg hG hF)]
end Evolution

namespace Splitting.Terminal
variable {A : Evolution E} {B : Splitting A} {n : ℕ} (C : B.Terminal (H:=H) n)

/-- A uniform half-orbit estimate. A polynomial factor in n is harmless
under the source's log(n+1)≤bn floor, but is explicitly retained here. -/
lemma trajectory_bound (f : ℕ → E) (a : E) (h : H) {G F : ℝ}
    (hG : 1≤G) (hF : 0≤F) (ha : B.slow 0 a=a)
    (hs : ∀ s u,s≤u → u≤n → ‖(A.map u s).comp (B.slow s)‖ ≤ G)
    (hb : ∀ s u,s≤u → u≤n → ‖(A.map s u).comp (B.fast u)‖ ≤ G)
    (hJ : ‖C.J‖ ≤ G) (hP : ‖C.P‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) (hh : ‖h‖ ≤ F) {t : ℕ} (ht : t≤n) :
    ‖C.trajectory f a h t‖ ≤ (G+G^4)*‖a‖+(2*G+G^4)*(n:ℝ)*F+G^2*F := by
  have hGn : 0≤G := by linarith
  let R := G*‖a‖+(n:ℝ)*G*F
  have hfor (u : ℕ) (hu : u≤n) : ‖A.forward B.slow f a u‖ ≤ R :=
    A.forward_bound B.slow f a hGn hF hu ha hs hf
  have hc : ‖C.terminalValue f a h‖ ≤ G*(F+G*R) := by
    apply C.J.le_opNorm _ |>.trans
    apply mul_le_mul hJ _ (norm_nonneg _) hGn
    apply (norm_sub_le _ _).trans
    apply add_le_add hh
    exact (C.P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hfor n le_rfl) hGn))
  have hbak := A.backward_bound B.fast f (C.terminalValue f a h) hGn hF ht (C.fast_J _) hb hf
  unfold trajectory
  calc
    _ ≤ ‖A.forward B.slow f a t‖+‖A.backward B.fast f (C.terminalValue f a h) n t‖ := norm_add_le _ _
    _ ≤ R+(G*(G*(F+G*R))+(n:ℝ)*G*F) :=
      add_le_add (hfor t ht) (hbak.trans (add_le_add (mul_le_mul_of_nonneg_left hc hGn) le_rfl))
    _ = _ := by dsimp only [R]; ring

end Splitting.Terminal
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- A quantitative bound for every genuine two-half boundary solution.
The explicit polynomial is retained; the source's logarithmic time floor
later absorbs it into the subexponential factor. -/
theorem solution_bound (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K F : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K) (hF : 0≤F)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (f₁ f₂ w₁ w₂ : ℕ → E) (h₁ : H) (h₂ : G) (m : E)
    (hf₁ : ∀ j<n₁,‖f₁ j‖≤F) (hf₂ : ∀ j<n₂,‖f₂ j‖≤F)
    (hh₁ : ‖h₁‖≤F) (hh₂ : ‖h₂‖≤F) (hm : ‖m‖≤F)
    (hw₁ : ∀ t<n₁,w₁ (t+1)=A₁.map (t+1) t (w₁ t)+f₁ t)
    (hw₂ : ∀ t<n₂,w₂ (t+1)=A₂.map (t+1) t (w₂ t)+f₂ t)
    (he₁ : C₁.P (w₁ n₁)=h₁) (he₂ : C₂.P (w₂ n₂)=h₂)
    (hmatch : w₁ 0-w₂ 0=m) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    (∀ t≤n₁,‖w₁ t‖≤Q*F) ∧ (∀ t≤n₂,‖w₂ t‖≤Q*F) := by
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  have hD : 0≤D := by dsimp [D]; positivity
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) (hsmall.trans_lt (by norm_num))
  have hMi : ‖M.symm.toContinuousLinearMap‖≤2*K :=
    BoundaryNeumann.inverse_norm L (correction C₁ C₂) hK hsmall
  let b₁ : B₁.initialSpace := ⟨B₁.slow 0 (w₁ 0),⟨w₁ 0,rfl⟩⟩
  let b₂ : B₂.initialSpace := ⟨B₂.slow 0 (w₂ 0),⟨w₂ 0,rfl⟩⟩
  have hv₁ := C₁.trajectory_unique f₁ b₁ (B₁.slow_initial b₁) h₁ w₁ hw₁ rfl he₁
  have hv₂ := C₂.trajectory_unique f₂ b₂ (B₂.slow_initial b₂) h₂ w₂ hw₂ rfl he₂
  let q₁ := C₁.trajectory f₁ 0 h₁ 0
  let q₂ := C₂.trajectory f₂ 0 h₂ 0
  have hn₁ : (n₁:ℝ)≤(n₁+n₂:ℕ) := by exact_mod_cast Nat.le_add_right n₁ n₂
  have hn₂ : (n₂:ℝ)≤(n₁+n₂:ℕ) := by exact_mod_cast Nat.le_add_left n₂ n₁
  have hq₁ : ‖q₁‖≤D*F := by
    have h := C₁.trajectory_bound f₁ 0 h₁ hU hF (by simp) hs₁ hb₁ hJ₁ hP₁ hf₁ hh₁ (Nat.zero_le n₁)
    simp only [norm_zero,mul_zero,zero_add] at h
    apply h.trans
    dsimp only [D]
    calc
      _ ≤ (2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by ring
  have hq₂ : ‖q₂‖≤D*F := by
    have h := C₂.trajectory_bound f₂ 0 h₂ hU hF (by simp) hs₂ hb₂ hJ₂ hP₂ hf₂ hh₂ (Nat.zero_le n₂)
    simp only [norm_zero,mul_zero,zero_add] at h
    apply h.trans
    dsimp only [D]
    calc
      _ ≤ (2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by ring
  have hMb : M (b₁,b₂)=m-q₁+q₂ := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    rw [hv₁ 0 (by omega),hv₂ 0 (by omega),
      C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
      C₂.trajectory_initial _ _ (B₂.slow_initial _) _] at hmatch
    change (b₁:E)-(b₂:E)+(C₁.kernel b₁-C₂.kernel b₂)=m-q₁+q₂
    change (b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂)=m at hmatch
    calc
      _ = ((b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂))-q₁+q₂ := by abel
      _ = _ := by rw [hmatch]
  have hbn : ‖(b₁,b₂)‖≤(2*K)*(1+2*D)*F := by
    have hb : (b₁,b₂)=M.symm (m-q₁+q₂) := ((M.symm_apply_eq).mpr hMb.symm).symm
    rw [hb]
    calc
      _ ≤ (2*K)*‖m-q₁+q₂‖ := (M.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hMi (norm_nonneg _))
      _ ≤ (2*K)*(F+D*F+D*F) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hm hq₁)) hq₂))
        (by positivity)
      _ = _ := by ring
  have hbn₁ : ‖(b₁:E)‖≤(2*K)*(1+2*D)*F := (norm_fst_le (b₁,b₂)).trans hbn
  have hbn₂ : ‖(b₂:E)‖≤(2*K)*(1+2*D)*F := (norm_snd_le (b₁,b₂)).trans hbn
  constructor
  · intro t ht
    rw [hv₁ t ht]
    apply (C₁.trajectory_bound f₁ b₁ h₁ hU hF (B₁.slow_initial _) hs₁ hb₁ hJ₁ hP₁ hf₁ hh₁ ht).trans
    change _≤((U+U^4)*(2*K)*(1+2*D)+D)*F
    calc
      _ ≤ (U+U^4)*((2*K)*(1+2*D)*F)+(2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by dsimp only [D]; ring
  · intro t ht
    rw [hv₂ t ht]
    apply (C₂.trajectory_bound f₂ b₂ h₂ hU hF (B₂.slow_initial _) hs₂ hb₂ hJ₂ hP₂ hf₂ hh₂ ht).trans
    change _≤((U+U^4)*(2*K)*(1+2*D)+D)*F
    calc
      _ ≤ (U+U^4)*((2*K)*(1+2*D)*F)+(2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by dsimp only [D]; ring

end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

abbrev Paths (E : Type*) (n₁ n₂ : ℕ) := (Fin (n₁+1) → E) × (Fin (n₂+1) → E)
abbrev Data (E H G : Type*) (n₁ n₂ : ℕ) :=
  (Fin n₁ → E) × (Fin n₂ → E) × E × H × G

/-- The actual finite-array boundary operator consists of both recurrence
residuals, the middle matching equation, and the two terminal projections. -/
noncomputable def boundaryLinear : Paths E n₁ n₂ →ₗ[ℝ] Data E H G n₁ n₂ where
  toFun v := (fun t => v.1 t.succ-A₁.map (t+1) t (v.1 t.castSucc),
    fun t => v.2 t.succ-A₂.map (t+1) t (v.2 t.castSucc),
    v.1 0-v.2 0,C₁.P (v.1 (Fin.last n₁)),C₂.P (v.2 (Fin.last n₂)))
  map_add' v w := by
    apply Prod.ext
    · funext t; simp only [Prod.fst_add,Pi.add_apply,map_add]; abel
    · apply Prod.ext
      · funext t; simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply,map_add]; abel
      · apply Prod.ext
        · simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply]; abel
        · apply Prod.ext <;> simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply,map_add]
  map_smul' c v := by
    apply Prod.ext
    · funext t; simp [smul_sub]
    · apply Prod.ext
      · funext t; simp [smul_sub]
      · apply Prod.ext
        · simp [smul_sub]
        · apply Prod.ext <;> simp

noncomputable def boundary : Paths E n₁ n₂ →L[ℝ] Data E H G n₁ n₂ :=
  (boundaryLinear C₁ C₂).toContinuousLinearMap

noncomputable def extend {n : ℕ} (v : Fin n → E) (t : ℕ) : E :=
  if h : t<n then v ⟨t,h⟩ else 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma extend_apply {n : ℕ} (v : Fin n → E) (t : Fin n) : extend v t=v t := by
  simp [extend,t.isLt]

/-- Finite-dimensional invertibility is a consequence of the Green formulas
and the genuinely small terminal graph correction. No linear inverse is
postulated. -/
theorem boundary_bijective (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1) :
    Function.Bijective (boundary C₁ C₂) := by
  classical
  have huniq (d : Data E H G n₁ n₂) : ∃! v : Paths E n₁ n₂,boundary C₁ C₂ v=d := by
    obtain ⟨v₁,v₂,hv₁,hv₂,he₁,he₂,hm,hu⟩ := solve C₁ C₂ L hL hsmall
      (extend d.1) (extend d.2.1) d.2.2.2.1 d.2.2.2.2 d.2.2.1
    let v : Paths E n₁ n₂ := (fun t => v₁ t,fun t => v₂ t)
    have hv : boundary C₁ C₂ v=d := by
      apply Prod.ext
      · funext t
        change v₁ (t+1)-A₁.map (t+1) t (v₁ t)=d.1 t
        rw [hv₁ t t.isLt,extend_apply]; abel
      · apply Prod.ext
        · funext t
          change v₂ (t+1)-A₂.map (t+1) t (v₂ t)=d.2.1 t
          rw [hv₂ t t.isLt,extend_apply]; abel
        · exact Prod.ext hm (Prod.ext he₁ he₂)
    refine ⟨v,hv,?_⟩
    intro w hw
    have h₁ : ∀ t<n₁,extend w.1 (t+1)=A₁.map (t+1) t (extend w.1 t)+extend d.1 t := by
      intro t ht
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hw
      change w.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (w.1 ⟨t,by omega⟩)=d.1 ⟨t,ht⟩ at h
      simp only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega),dite_eq_left ht]
      rw [←h]; abel
    have h₂ : ∀ t<n₂,extend w.2 (t+1)=A₂.map (t+1) t (extend w.2 t)+extend d.2.1 t := by
      intro t ht
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hw
      change w.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (w.2 ⟨t,by omega⟩)=d.2.1 ⟨t,ht⟩ at h
      simp only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega),dite_eq_left ht]
      rw [←h]; abel
    have he₁' : C₁.P (extend w.1 n₁)=d.2.2.2.1 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hw
      change C₁.P (w.1 (Fin.last n₁))=d.2.2.2.1 at h
      change C₁.P (extend w.1 (Fin.last n₁))=d.2.2.2.1
      rw [extend_apply]
      exact h
    have he₂' : C₂.P (extend w.2 n₂)=d.2.2.2.2 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hw
      change C₂.P (w.2 (Fin.last n₂))=d.2.2.2.2 at h
      change C₂.P (extend w.2 (Fin.last n₂))=d.2.2.2.2
      rw [extend_apply]
      exact h
    have hm' : extend w.1 0-extend w.2 0=d.2.2.1 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hw
      change w.1 0-w.2 0=d.2.2.1 at h
      change extend w.1 (0 : Fin (n₁+1))-extend w.2 (0 : Fin (n₂+1))=d.2.2.1
      rw [extend_apply,extend_apply]
      exact h
    obtain ⟨hu₁,hu₂⟩ := hu (extend w.1) (extend w.2) h₁ h₂ he₁' he₂' hm'
    apply Prod.ext
    · funext t
      simpa only [extend_apply] using hu₁ t (by omega)
    · funext t
      simpa only [extend_apply] using hu₂ t (by omega)
  constructor
  · intro v w h
    obtain ⟨z,hz,hzu⟩ := huniq (boundary C₁ C₂ v)
    exact (hzu v rfl).trans (hzu w h.symm).symm
  · intro d
    obtain ⟨v,hv,_⟩ := huniq d
    exact ⟨v,hv⟩

noncomputable def boundaryEquiv (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1) :
    Paths E n₁ n₂ ≃L[ℝ] Data E H G n₁ n₂ :=
  (LinearEquiv.ofBijective (boundaryLinear C₁ C₂)
    (boundary_bijective C₁ C₂ L hL hsmall)).toContinuousLinearEquiv

end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

theorem boundary_inverse_norm (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤
      (U+U^4)*(2*K)*(1+2*D)+D := by
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hQ : 0≤Q := by dsimp [Q,D]; positivity
  change ‖V.symm.toContinuousLinearMap‖≤Q
  apply V.symm.toContinuousLinearMap.opNorm_le_bound hQ
  intro d
  let w := V.symm d
  have hw : boundary C₁ C₂ w=d := V.apply_symm_apply d
  have hw₁ : ∀ t<n₁,extend w.1 (t+1)=A₁.map (t+1) t (extend w.1 t)+extend d.1 t := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hw
    change w.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (w.1 ⟨t,by omega⟩)=d.1 ⟨t,ht⟩ at h
    simp only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega),dite_eq_left ht]
    rw [←h]; abel
  have hw₂ : ∀ t<n₂,extend w.2 (t+1)=A₂.map (t+1) t (extend w.2 t)+extend d.2.1 t := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hw
    change w.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (w.2 ⟨t,by omega⟩)=d.2.1 ⟨t,ht⟩ at h
    simp only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega),dite_eq_left ht]
    rw [←h]; abel
  have he₁ : C₁.P (extend w.1 n₁)=d.2.2.2.1 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hw
    change C₁.P (w.1 (Fin.last n₁))=d.2.2.2.1 at h
    change C₁.P (extend w.1 (Fin.last n₁))=d.2.2.2.1
    rw [extend_apply]; exact h
  have he₂ : C₂.P (extend w.2 n₂)=d.2.2.2.2 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hw
    change C₂.P (w.2 (Fin.last n₂))=d.2.2.2.2 at h
    change C₂.P (extend w.2 (Fin.last n₂))=d.2.2.2.2
    rw [extend_apply]; exact h
  have hm : extend w.1 0-extend w.2 0=d.2.2.1 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hw
    change w.1 0-w.2 0=d.2.2.1 at h
    change extend w.1 (0 : Fin (n₁+1))-extend w.2 (0 : Fin (n₂+1))=d.2.2.1
    rw [extend_apply,extend_apply]; exact h
  have hf₁ : ∀ j<n₁,‖extend d.1 j‖≤‖d‖ := by
    intro j hj
    rw [extend,dite_eq_left hj]
    exact (norm_le_pi_norm d.1 ⟨j,hj⟩).trans (norm_fst_le d)
  have hf₂ : ∀ j<n₂,‖extend d.2.1 j‖≤‖d‖ := by
    intro j hj
    rw [extend,dite_eq_left hj]
    exact (norm_le_pi_norm d.2.1 ⟨j,hj⟩).trans ((norm_fst_le d.2).trans (norm_snd_le d))
  have hh₁ : ‖d.2.2.2.1‖≤‖d‖ := (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le d)))
  have hh₂ : ‖d.2.2.2.2‖≤‖d‖ := (norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le d)))
  have hmid : ‖d.2.2.1‖≤‖d‖ := (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le d))
  obtain ⟨h₁,h₂⟩ := solution_bound C₁ C₂ L hL hU hK (norm_nonneg d) hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
    (extend d.1) (extend d.2.1) (extend w.1) (extend w.2)
    d.2.2.2.1 d.2.2.2.2 d.2.2.1 hf₁ hf₂ hh₁ hh₂ hmid hw₁ hw₂ he₁ he₂ hm
  change ‖w‖≤Q*‖d‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hQ (norm_nonneg d))).mpr
    intro t
    simpa only [extend_apply] using h₁ t (by omega)
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hQ (norm_nonneg d))).mpr
    intro t
    simpa only [extend_apply] using h₂ t (by omega)

end SmoothObstruction.FiniteGreen.Matching

end

end OAI
