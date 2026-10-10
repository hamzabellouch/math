import OAI.Dynamics.SmoothObstruction.NonlinearMatching

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- An exact finite coordinate solution lying in the original chart targets
is a genuine manifold orbit, also in a half-space model. -/
theorem realize_array (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a : Fin (n+1) → M) (u : Fin (n+1) → E (d:=d))
    (hu : ∀ t,u t∈(extChartAt I (a t)).target)
    (hdom : ∀ t : Fin n,u t.castSucc∈domainU I S (a t.castSucc) (a t.succ))
    (hstep : ∀ t : Fin n,localMap I S (a t.castSucc) (a t.succ) (u t.castSucc)=u t.succ) :
    ∃ z : M,∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
      (extChartAt I (a t)) (S^[t.val] z)=u t := by
  let z := (extChartAt I (a 0)).symm (u 0)
  refine ⟨z,?_⟩
  have h (t : ℕ) (ht : t<n+1) : S^[t] z=(extChartAt I (a ⟨t,ht⟩)).symm (u ⟨t,ht⟩) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have ht' : t<n := by omega
      have hh := hstep ⟨t,ht'⟩
      have htS : S ((extChartAt I (a ⟨t,by omega⟩)).symm (u ⟨t,by omega⟩))
          ∈(extChartAt I (a ⟨t+1,ht⟩)).source := by
        have hm := (hdom ⟨t,ht'⟩).2
        change S ((extChartAt I (a ⟨t,by omega⟩)).symm (u ⟨t,by omega⟩))
          ∈(chartAt H (a ⟨t+1,ht⟩)).source at hm
        simpa only [extChartAt_source] using hm
      rw [Function.iterate_succ_apply',ih (by omega)]
      exact (extChartAt I (a ⟨t+1,ht⟩)).left_inv htS |>.symm.trans
        (congrArg (extChartAt I (a ⟨t+1,ht⟩)).symm hh)
  intro t
  rw [h t t.isLt]
  exact ⟨by simpa only [extChartAt_source] using (extChartAt I (a t)).map_target (hu t),
    (extChartAt I (a t)).right_inv (hu t)⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Matching the time-zero coordinate realizes the TWO-sided exact arrays
as one actual orbit. In particular no pair of unrelated local branches is
substituted for the smooth switch. -/
theorem realize_bilateral_array (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (u v : Fin (n+1) → E (d:=d))
    (ha : a 0=b 0) (huv : u 0=v 0)
    (hu : ∀ t,u t∈(extChartAt I (a t)).target)
    (hv : ∀ t,v t∈(extChartAt I (b t)).target)
    (hud : ∀ t : Fin n,u t.castSucc∈domainU I S (a t.castSucc) (a t.succ))
    (hvd : ∀ t : Fin n,v t.castSucc∈domainU I S.symm (b t.castSucc) (b t.succ))
    (hus : ∀ t : Fin n,localMap I S (a t.castSucc) (a t.succ) (u t.castSucc)=u t.succ)
    (hvs : ∀ t : Fin n,localMap I S.symm (b t.castSucc) (b t.succ) (v t.castSucc)=v t.succ) :
    ∃ z : M,(∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
      (extChartAt I (a t)) (S^[t.val] z)=u t) ∧
      (∀ t : Fin (n+1),S.symm^[t.val] z∈(chartAt H (b t)).source ∧
      (extChartAt I (b t)) (S.symm^[t.val] z)=v t) := by
  obtain ⟨z,hz⟩ := realize_array I S a u hu hud hus
  obtain ⟨w,hw⟩ := realize_array I S.symm b v hv hvd hvs
  have hz0 : z=(extChartAt I (a 0)).symm (u 0) := by
    have hz0 := hz 0
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hz0
    rw [←hz0.2,(extChartAt I (a 0)).left_inv (by simpa only [extChartAt_source] using hz0.1)]
  have hw0 : w=(extChartAt I (b 0)).symm (v 0) := by
    have hw0 := hw 0
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hw0
    rw [←hw0.2,(extChartAt I (b 0)).left_inv (by simpa only [extChartAt_source] using hw0.1)]
  have heq : z=w := by rw [hz0,hw0,ha,huv]
  exact ⟨z,hz,by simpa only [heq] using hw⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
open FiniteGreen FiniteGreen.Matching

/-- The authentic local-coordinate nonlinear boundary construction gives
ONE actual point of the manifold, with both orbit halves and the fixed
terminal equations. The ball-domain conditions keep every inverse chart
and every one-step expression inside the ORIGINAL manifold. -/
theorem actual_join_unique (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),S^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),S.symm^[t.val] y∈(chartAt H (b t)).source)
    (A₁ A₂ : Evolution (E (d:=d))) (B₁ : Splitting A₁) (B₂ : Splitting A₂)
    (C₁ : B₁.Terminal (H:=F) n) (C₂ : B₂.Terminal (H:=G) n)
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E (d:=d))
    (hL : ∀ z,L z=(z.1:E (d:=d))-(z.2:E (d:=d)))
    {U K C r δ : ℝ} (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hA₁ : ∀ t : Fin n,fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (S^[t.val] x))=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n,fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))=A₂.map (t+1) t)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I S (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I S (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (S^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (S^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (S.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (S^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (S.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ⊆
      domainU I S (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ⊆
      domainU I S.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n+n : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ z : M,
      (∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (S^[t.val] z)-(extChartAt I (a t)) (S^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),S.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (S.symm^[t.val] z)-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z)-
        (extChartAt I (a (Fin.last n))) (S^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (S^[t.val] z)-
        (extChartAt I (a t)) (S^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (S.symm^[t.val] z)-
        (extChartAt I (b t)) (S.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),S^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (S^[t.val] z')-(extChartAt I (a t)) (S^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),S.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (S.symm^[t.val] z')-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z')-
          (extChartAt I (a (Fin.last n))) (S^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 → z'=z := by
  let u : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (a t)) (S^[t.val] x)
  let v : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (b t)) (S.symm^[t.val] y)
  let f : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S (a t.castSucc) (a t.succ)
  let g : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S.symm (b t.castSucc) (b t.succ)
  have hu (t : Fin n) : f t (u t.castSucc)=u t.succ := by
    simp only [f,u,localMap,Function.comp_apply]
    rw [(extChartAt I (a t.castSucc)).left_inv (by simpa only [extChartAt_source] using hx t.castSucc)]
    exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ x).symm
  have hv (t : Fin n) : g t (v t.castSucc)=v t.succ := by
    simp only [g,v,localMap,Function.comp_apply]
    rw [(extChartAt I (b t.castSucc)).left_inv (by simpa only [extChartAt_source] using hy t.castSucc)]
    exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ y).symm
  obtain ⟨w,hw,hwsharp,hf,hg,hmid,hp,hq,hunique⟩ := nonlinear_orbits_unique C₁ C₂ L hL hU hK hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂ f g u v hu hv hA₁ hA₂ hC hr hδ hd₁ hd₂ hder₁ hder₂
    (by simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq] using hnear) hcontract hdata
  have hw₁ (t : Fin (n+1)) : ‖w.1 t‖≤δ/2 :=
    (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hw)
  have hw₂ (t : Fin (n+1)) : ‖w.2 t‖≤δ/2 :=
    (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hw)
  have hwδ : δ/2≤δ := by linarith
  have hb₁' (t : Fin (n+1)) : u t+w.1 t∈closedBall (u t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₁ t).trans hwδ
  have hb₂' (t : Fin (n+1)) : v t+w.2 t∈closedBall (v t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₂ t).trans hwδ
  obtain ⟨z,hz,hz'⟩ := realize_bilateral_array I S a b (fun t => u t+w.1 t) (fun t => v t+w.2 t)
    hab hmid (fun t => ht₁ t (hb₁' t)) (fun t => ht₂ t (hb₂' t))
    (fun t => hdom₁ t (hb₁' t.castSucc)) (fun t => hdom₂ t (hb₂' t.castSucc)) hf hg
  refine ⟨z,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t
    refine ⟨(hz t).1,?_⟩
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using hw₁ t
  · intro t
    refine ⟨(hz' t).1,?_⟩
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using hw₂ t
  · have hzL := (hz (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [u,Fin.val_last,add_sub_cancel_left] using hp
  · have hzL := (hz' (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [v,Fin.val_last,add_sub_cancel_left] using hq
  · intro t
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using
      (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hwsharp)
  · intro t
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using
      (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hwsharp)
  · intro z' hx' hy' hp' hq'
    let w' : Paths (E (d:=d)) n n :=
      (fun t => (extChartAt I (a t)) (S^[t.val] z')-u t,
       fun t => (extChartAt I (b t)) (S.symm^[t.val] z')-v t)
    have hn : ‖w'‖≤δ := by
      rw [Prod.norm_def,max_le_iff]
      constructor
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hx' t).2)
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hy' t).2)
    have huf (t : Fin (n+1)) : u t+w'.1 t=(extChartAt I (a t)) (S^[t.val] z') := by
      dsimp only [w']; abel
    have hvf (t : Fin (n+1)) : v t+w'.2 t=(extChartAt I (b t)) (S.symm^[t.val] z') := by
      dsimp only [w']; abel
    have he : w'=w := hunique w' hn (fun t => by
        rw [huf,huf]
        simp only [f,localMap,Function.comp_apply]
        rw [(extChartAt I (a t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hx' t.castSucc).1)]
        exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ z').symm)
      (fun t => by
        rw [hvf,hvf]
        simp only [g,localMap,Function.comp_apply]
        rw [(extChartAt I (b t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hy' t.castSucc).1)]
        exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ z').symm)
      (by rw [huf,hvf,hab]; rfl)
      (by simpa only [w',u,Fin.val_last] using hp')
      (by simpa only [w',v,Fin.val_last] using hq')
    apply (extChartAt I (a 0)).injOn
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hx' 0).1)
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hz 0).1)
    have hfirst := congrArg (fun q : Paths (E (d:=d)) n n => q.1 0) he
    have hc := (hz 0).2
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hc
    rw [hc,←hfirst, huf]
    rfl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortBin
open EuclideanSplitting FiniteGreen FiniteGreen.Matching
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

lemma Gauge.evolution_step (A : Gauge d n K) (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (t : ℕ) (h : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm D*A.U t=
      A.U (t+1)*rate A.lam 1) : A.evolution.map (t+1) t=D := by
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam t (t+1))=D
  rw [transition,show ((t+1:ℕ):ℝ)-(t:ℝ)=1 by push_cast; ring,←h,mul_assoc,A.UV t,mul_one]
  exact (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply D

lemma Gauge.unweighted (A : Gauge d n K) (S : Finset (Fin d)) {a : ℝ}
    (ha : 0≤a) (hs : ∀ j∈S,A.lam j≤a) (hf : ∀ j∈Sᶜ,-a≤A.lam j) :
    (∀ s t,s≤t → t≤n → ‖(A.evolution.map t s).comp ((A.splitting S).slow s)‖≤Real.exp (2*K+a*n)) ∧
    (∀ s t,s≤t → t≤n → ‖(A.evolution.map s t).comp ((A.splitting S).fast t)‖≤Real.exp (2*K+a*n)) :=
  unweighted_bounds A.U A.V A.lam A.UV A.VU S ha A.normU A.normV hs hf

/-- All the finite-interval linear boundary hypotheses are produced from
raw common-bin gauge comparisons and fixed endpoint projections. The norm
of the matching inverse is a middle-time cost, and the endpoint correction
retains threshold cancellation, including a positive slow threshold. -/
theorem gauge_boundary_control (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdV : Module.finrank ℝ ((A.splitting S).fast n).range=Module.finrank ℝ V)
    (hdW : Module.finrank ℝ ((Z.splitting T).fast n).range=Module.finrank ℝ W)
    (hcV : ‖((A.splitting S).fast n).range.starProjection-V.starProjection‖≤1/2)
    (hcW : ‖((Z.splitting T).fast n).range.starProjection-W.starProjection‖≤1/2)
    {ε γ g : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2)
    (hsA : ∀ j∈S,A.lam j≤γ-g) (hfA : ∀ j∈Sᶜ,γ+g≤A.lam j)
    (hsZ : ∀ j∈T,Z.lam j≤ -γ-g) (hfZ : ∀ j∈Tᶜ,-γ+g≤Z.lam j)
    (hgap : (2*Real.exp (2*K))*(2*(2*Real.exp (2*K)^2*Real.exp (-2*g*n)))≤1/2) :
    let C₁ := (A.splitting S).terminalProjection n V hdV hcV
    let C₂ := (Z.splitting T).terminalProjection n W hdW hcW
    ∃ L : ((A.splitting S).initialSpace×(Z.splitting T).initialSpace) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ v,L v=(v.1:EuclideanSpace ℝ (Fin d))-(v.2:EuclideanSpace ℝ (Fin d))) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*Real.exp (2*K) ∧
      ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2 ∧
      ‖C₁.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) ∧
      ‖C₂.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) := by
  intro C₁ C₂
  obtain ⟨L,hL,hK⟩ := gauge_matching A₀ A Z S₀ S T hε hεhalf hdS hdT hcS hcT hsmall
  have hA := endpoint_gap_bounds A.U A.V A.lam A.UV A.VU S n A.normU A.normV hsA hfA
  have hZ := endpoint_gap_bounds Z.U Z.V Z.lam Z.UV Z.VU T n Z.normU Z.normV hsZ hfZ
  have heA : ‖C₁.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) :=
    C₁.kernel_norm_gap (Real.exp_nonneg _) hA.2 hA.1
      ((A.splitting S).terminalProjection_J_norm n V hdV hcV)
      ((A.splitting S).terminalProjection_P_norm n V hdV hcV)
  have heZ : ‖C₂.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) :=
    C₂.kernel_norm_gap (Real.exp_nonneg _) hZ.2 hZ.1
      ((Z.splitting T).terminalProjection_J_norm n W hdW hcW)
      ((Z.splitting T).terminalProjection_P_norm n W hdW hcW)
  refine ⟨L,hL,hK,?_,heA,heZ⟩
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply le_trans (mul_le_mul hK (correction_norm C₁ C₂ heA heZ) (norm_nonneg (correction C₁ C₂)) (by positivity))
  simpa only [two_mul] using hgap
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
noncomputable def bvpGrowth (K a : ℝ) (n : ℕ) : ℝ := Real.exp (2*K+a*n)+2
noncomputable def bvpInverseBound (K a : ℝ) (n : ℕ) : ℝ :=
  let U := bvpGrowth K a n
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  (U+U^4)*(4*Real.exp (2*K))*(1+2*D)+D
lemma bvpGrowth_ge_two (K a : ℝ) (n : ℕ) : 2≤bvpGrowth K a n := by
  dsimp [bvpGrowth]; linarith [Real.exp_pos (2*K+a*n)]
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open FiniteGreen FiniteGreen.Matching ShortBin

omit [IsManifold I ∞ M] in
lemma interior_iterate (S : Diffeomorph I I M M ∞) {x : M} (hx : I.IsInteriorPoint x) (t : ℕ) :
    I.IsInteriorPoint (S^[t] x) := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih

/-- The long gauge equations identify every step of the evolution with
an ACTUAL coordinate derivative. -/
lemma gauge_actual_step (S : Diffeomorph I I M M ∞) (a b x : M)
    {n : ℕ} {K : ℝ} (A : ShortBin.Gauge d n K) (t : ℕ)
    (hx : x∈(chartAt H a).source) (hSx : S x∈(chartAt H b).source)
    (hint : I.IsInteriorPoint x)
    (hEq : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (coord I S a b x)*A.U t=
      A.U (t+1)*EuclideanSplitting.rate A.lam 1) :
    fderiv ℝ (localMap I S a b) ((extChartAt I a) x)=A.evolution.map (t+1) t := by
  rw [A.evolution_step (coord I S a b x) t hEq]
  exact (hasFDerivAt_localMap I S a b x ⟨hx,hSx⟩ ((interior_coord I a x hx).mpr hint)).fderiv

/-- Actual nonlinear joining, now with ALL linear matching/inverse/kernel
hypotheses proved from the genuine gauges and the common-bin comparisons.
No boundary inverse, complementary middle space or endpoint graph is assumed. -/
theorem gauged_join_unique (Smap : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),Smap^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),Smap.symm^[t.val] y∈(chartAt H (b t)).source)
    (hintx : I.IsInteriorPoint x) (hinty : I.IsInteriorPoint y)
    {K ε γ g α : ℝ} (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    (V W : Submodule ℝ (E (d:=d)))
    (hdV : Module.finrank ℝ ((A.splitting S).fast n).range=Module.finrank ℝ V)
    (hdW : Module.finrank ℝ ((Z.splitting T).fast n).range=Module.finrank ℝ W)
    (hcV : ‖((A.splitting S).fast n).range.starProjection-V.starProjection‖≤1/2)
    (hcW : ‖((Z.splitting T).fast n).range.starProjection-W.starProjection‖≤1/2)
    (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2)
    (hsA : ∀ j∈S,A.lam j≤γ-g) (hfA : ∀ j∈Sᶜ,γ+g≤A.lam j)
    (hsZ : ∀ j∈T,Z.lam j≤ -γ-g) (hfZ : ∀ j∈Tᶜ,-γ+g≤Z.lam j)
    (hgap : (2*Real.exp (2*K))*(2*(2*Real.exp (2*K)^2*Real.exp (-2*g*n)))≤1/2)
    (hα : |γ|+|g|≤α)
    (hstep₁ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap (a t.castSucc) (a t.succ) (Smap^[t.val] x))*A.U t=
        A.U (t+1)*EuclideanSplitting.rate A.lam 1)
    (hstep₂ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap.symm (b t.castSucc) (b t.succ) (Smap.symm^[t.val] y))*Z.U t=
        Z.U (t+1)*EuclideanSplitting.rate Z.lam 1)
    {C r δ : ℝ}
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (Smap^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (Smap^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (Smap.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ⊆
      domainU I Smap (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ⊆
      domainU I Smap.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : bvpInverseBound K α n*C*δ≤1/4)
    (hdata : bvpInverseBound K α n*C*r≤δ/4) :
    let C₁ := (A.splitting S).terminalProjection n V hdV hcV
    let C₂ := (Z.splitting T).terminalProjection n W hdW hcW
    let Q := bvpInverseBound K α n
    ∃ z : M,
      (∀ t : Fin (n+1),Smap^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (Smap^[t.val] z)-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),Smap.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z)-
        (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (Smap^[t.val] z)-
        (extChartAt I (a t)) (Smap^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-
        (extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),Smap^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (Smap^[t.val] z')-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),Smap.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (Smap.symm^[t.val] z')-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z')-
          (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 → z'=z := by
  intro C₁ C₂ Q
  obtain ⟨L,hL,hK,hcorr,hκ₁,hκ₂⟩ := gauge_boundary_control A₀ A Z S₀ S T V W
    hdV hdW hcV hcW hε hεhalf hdS hdT hcS hcT hsmall hsA hfA hsZ hfZ hgap
  have hnα : 0≤α := (add_nonneg (abs_nonneg γ) (abs_nonneg g)).trans hα
  have hboundA := A.unweighted S hnα
    (fun j hj => (hsA j hj).trans (by linarith [le_abs_self γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [neg_le_abs γ,neg_le_abs g]) (hfA j hj))
  have hboundZ := Z.unweighted T hnα
    (fun j hj => (hsZ j hj).trans (by linarith [neg_le_abs γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [le_abs_self γ,neg_le_abs g]) (hfZ j hj))
  have hU : 1≤bvpGrowth K α n := (by norm_num : (1:ℝ)≤2).trans (bvpGrowth_ge_two K α n)
  have hUG : Real.exp (2*K+α*n)≤bvpGrowth K α n := by dsimp [bvpGrowth]; linarith
  have hA₁ (t : Fin n) : fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))=A.evolution.map (t+1) t :=
    gauge_actual_step I Smap _ _ _ A t (hx t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hx t.succ)
      (interior_iterate I Smap hintx t) (hstep₁ t)
  have hA₂ (t : Fin n) : fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))=Z.evolution.map (t+1) t :=
    gauge_actual_step I Smap.symm _ _ _ Z t (hy t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hy t.succ)
      (interior_iterate I Smap.symm hinty t) (hstep₂ t)
  have hcontract' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*δ≤1/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hcontract
  have hdata' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*r≤δ/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hdata
  have hjoin := actual_join_unique I Smap a b x y hab hx hy A.evolution Z.evolution
    (A.splitting S) (Z.splitting T) C₁ C₂ L hL hU hK hcorr
    (fun s u hsu hun => (hboundA.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundA.2 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.2 s u hsu hun).trans hUG)
    (((A.splitting S).terminalProjection_J_norm n V hdV hcV).trans (bvpGrowth_ge_two K α n))
    (((A.splitting S).terminalProjection_P_norm n V hdV hcV).trans hU)
    (((Z.splitting T).terminalProjection_J_norm n W hdW hcW).trans (bvpGrowth_ge_two K α n))
    (((Z.splitting T).terminalProjection_P_norm n W hdW hcW).trans hU)
    hC hr hδ hA₁ hA₂ hd₁ hd₂ hder₁ hder₂ ht₁ ht₂ hdom₁ hdom₂ hnear hcontract' hdata'
  simpa only [Q,bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hjoin
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteGreen.Matching
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- A genuine nonlinear coordinate solution satisfies the exact boundary
residual equation, hence the sharp ideal-exchange estimate. -/
theorem genuine_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ Q C δ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ) (hC : 0≤C)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin (n₁+1) → E) (x₂ : Fin (n₂+1) → E)
    (hx₁ : ∀ t,f₁ t (x₁ t.castSucc)=x₁ t.succ)
    (hx₂ : ∀ t,f₂ t (x₂ t.castSucc)=x₂ t.succ)
    (hA₁ : ∀ t : Fin n₁,fderiv ℝ (f₁ t) (x₁ t.castSucc)=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n₂,fderiv ℝ (f₂ t) (x₂ t.castSucc)=A₂.map (t+1) t)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,DifferentiableAt ℝ (f₂ t) y)
    (hder₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,
      ‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t.castSucc)‖≤C*‖y-x₁ t.castSucc‖)
    (hder₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,
      ‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t.castSucc)‖≤C*‖y-x₂ t.castSucc‖)
    (v : Paths E n₁ n₂) (hv : ‖v‖≤δ)
    (hs₁ : ∀ t,f₁ t (x₁ t.castSucc+v.1 t.castSucc)=x₁ t.succ+v.1 t.succ)
    (hs₂ : ∀ t,f₂ t (x₂ t.castSucc+v.2 t.castSucc)=x₂ t.succ+v.2 t.succ)
    (hm : x₁ 0+v.1 0=x₂ 0+v.2 0)
    (hp₁ : C₁.P (v.1 (Fin.last n₁))=0) (hp₂ : C₂.P (v.2 (Fin.last n₂))=0)
    (hQ : ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤Q) :
    ‖v.1 0-B₀.slow 0 (x₂ 0-x₁ 0)‖≤4*P*K*(ε+κ)*‖x₂ 0-x₁ 0‖+Q*C*‖v‖^2 := by
  let R := ArrayRemainder.residual (H:=H) (G:=G) f₁ f₂
    (fun t => x₁ t.castSucc) (fun t => x₂ t.castSucc)
  apply array_nonlinear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hC hsmall hc₁ hc₂
    hk₁ hk₂ hs hf R v (x₂ 0-x₁ 0)
    (ArrayRemainder.residual_quadratic f₁ f₂ _ _ hC hd₁ hd₂ hder₁ hder₂ hv) _ hQ
  apply Prod.ext
  · funext t
    change v.1 t.succ-A₁.map (t+1) t (v.1 t.castSucc)=
      0+(f₁ t (x₁ t.castSucc+v.1 t.castSucc)-f₁ t (x₁ t.castSucc)-
        (fderiv ℝ (f₁ t) (x₁ t.castSucc)) (v.1 t.castSucc))
    rw [hs₁ t,hx₁ t,hA₁ t,zero_add]
    abel
  · apply Prod.ext
    · funext t
      change v.2 t.succ-A₂.map (t+1) t (v.2 t.castSucc)=
        0+(f₂ t (x₂ t.castSucc+v.2 t.castSucc)-f₂ t (x₂ t.castSucc)-
          (fderiv ℝ (f₂ t) (x₂ t.castSucc)) (v.2 t.castSucc))
      rw [hs₂ t,hx₂ t,hA₂ t,zero_add]
      abel
    · apply Prod.ext
      · change v.1 0-v.2 0=(x₂ 0-x₁ 0)+0
        have hh := congrArg (fun z => z-x₁ 0-v.2 0) hm
        simpa only [add_zero] using (by convert hh using 1 <;> abel)
      · apply Prod.ext
        · change C₁.P (v.1 (Fin.last n₁))=0+0
          simpa only [add_zero] using hp₁
        · change C₂.P (v.2 (Fin.last n₂))=0+0
          simpa only [add_zero] using hp₂
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
open FiniteGreen FiniteGreen.Matching

/-- The authentic local-coordinate nonlinear boundary construction gives
ONE actual point of the manifold, with both orbit halves and the fixed
terminal equations. The ball-domain conditions keep every inverse chart
and every one-step expression inside the ORIGINAL manifold. -/
theorem actual_join_ideal (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),S^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),S.symm^[t.val] y∈(chartAt H (b t)).source)
    (A₁ A₂ : Evolution (E (d:=d))) (B₁ : Splitting A₁) (B₂ : Splitting A₂)
    (C₁ : B₁.Terminal (H:=F) n) (C₂ : B₂.Terminal (H:=G) n)
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E (d:=d))
    (hL : ∀ z,L z=(z.1:E (d:=d))-(z.2:E (d:=d)))
    {U K C r δ : ℝ} (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (A₀ : Evolution (E (d:=d))) (B₀ : Splitting A₀)
    {P ε κ : ℝ} (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hslow : ‖B₀.slow 0‖≤P) (hfast : ‖B₀.fast 0‖≤P)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hA₁ : ∀ t : Fin n,fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (S^[t.val] x))=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n,fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))=A₂.map (t+1) t)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I S (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I S (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (S^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (S^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (S.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (S^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (S.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ⊆
      domainU I S (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ⊆
      domainU I S.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n+n : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ z : M,
      (∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (S^[t.val] z)-(extChartAt I (a t)) (S^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),S.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (S.symm^[t.val] z)-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z)-
        (extChartAt I (a (Fin.last n))) (S^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (S^[t.val] z)-
        (extChartAt I (a t)) (S^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (S.symm^[t.val] z)-
        (extChartAt I (b t)) (S.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ‖(extChartAt I (a 0)) z-(extChartAt I (a 0)) x-
        B₀.slow 0 ((extChartAt I (b 0)) y-(extChartAt I (a 0)) x)‖≤
        4*P*K*(ε+κ)*(C*r)+Q*C*(2*C*Q*r)^2 ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),S^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (S^[t.val] z')-(extChartAt I (a t)) (S^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),S.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (S.symm^[t.val] z')-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z')-
          (extChartAt I (a (Fin.last n))) (S^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 → z'=z := by
  let u : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (a t)) (S^[t.val] x)
  let v : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (b t)) (S.symm^[t.val] y)
  let f : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S (a t.castSucc) (a t.succ)
  let g : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S.symm (b t.castSucc) (b t.succ)
  have hu (t : Fin n) : f t (u t.castSucc)=u t.succ := by
    simp only [f,u,localMap,Function.comp_apply]
    rw [(extChartAt I (a t.castSucc)).left_inv (by simpa only [extChartAt_source] using hx t.castSucc)]
    exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ x).symm
  have hv (t : Fin n) : g t (v t.castSucc)=v t.succ := by
    simp only [g,v,localMap,Function.comp_apply]
    rw [(extChartAt I (b t.castSucc)).left_inv (by simpa only [extChartAt_source] using hy t.castSucc)]
    exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ y).symm
  obtain ⟨w,hw,hwsharp,hf,hg,hmid,hp,hq,hunique⟩ := nonlinear_orbits_unique C₁ C₂ L hL hU hK hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂ f g u v hu hv hA₁ hA₂ hC hr hδ hd₁ hd₂ hder₁ hder₂
    (by simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq] using hnear) hcontract hdata
  have hw₁ (t : Fin (n+1)) : ‖w.1 t‖≤δ/2 :=
    (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hw)
  have hw₂ (t : Fin (n+1)) : ‖w.2 t‖≤δ/2 :=
    (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hw)
  have hwδ : δ/2≤δ := by linarith
  have hb₁' (t : Fin (n+1)) : u t+w.1 t∈closedBall (u t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₁ t).trans hwδ
  have hb₂' (t : Fin (n+1)) : v t+w.2 t∈closedBall (v t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₂ t).trans hwδ
  obtain ⟨z,hz,hz'⟩ := realize_bilateral_array I S a b (fun t => u t+w.1 t) (fun t => v t+w.2 t)
    hab hmid (fun t => ht₁ t (hb₁' t)) (fun t => ht₂ t (hb₂' t))
    (fun t => hdom₁ t (hb₁' t.castSucc)) (fun t => hdom₂ t (hb₂' t.castSucc)) hf hg
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hUn : 0≤U := by linarith
  have hQn : 0≤Q := by dsimp [Q,D]; positivity
  have hQ := boundary_inverse_norm C₁ C₂ L hL hU hK hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
  have hi := genuine_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hC hsmall hc₁ hc₂
    hk₁ hk₂ hslow hfast f g u v hu hv hA₁ hA₂ hd₁ hd₂ hder₁ hder₂ w
    (hw.trans hwδ) hf hg hmid hp hq hQ
  have hi' : ‖w.1 0-B₀.slow 0 (v 0-u 0)‖≤
      4*P*K*(ε+κ)*(C*r)+Q*C*(2*C*Q*r)^2 := by
    apply hi.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq] using hnear
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQn hC)
      exact pow_le_pow_left₀ (norm_nonneg w) hwsharp 2
  refine ⟨z,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t
    refine ⟨(hz t).1,?_⟩
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using hw₁ t
  · intro t
    refine ⟨(hz' t).1,?_⟩
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using hw₂ t
  · have hzL := (hz (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [u,Fin.val_last,add_sub_cancel_left] using hp
  · have hzL := (hz' (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [v,Fin.val_last,add_sub_cancel_left] using hq
  · intro t
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using
      (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hwsharp)
  · intro t
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using
      (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hwsharp)
  · have hz0 := (hz 0).2
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hz0
    rw [hz0]
    simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq,add_sub_cancel_left] using hi'
  · intro z' hx' hy' hp' hq' 
    let w' : Paths (E (d:=d)) n n :=
      (fun t => (extChartAt I (a t)) (S^[t.val] z')-u t,
       fun t => (extChartAt I (b t)) (S.symm^[t.val] z')-v t)
    have hn : ‖w'‖≤δ := by
      rw [Prod.norm_def,max_le_iff]
      constructor
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hx' t).2)
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hy' t).2)
    have huf (t : Fin (n+1)) : u t+w'.1 t=(extChartAt I (a t)) (S^[t.val] z') := by
      dsimp only [w']; abel
    have hvf (t : Fin (n+1)) : v t+w'.2 t=(extChartAt I (b t)) (S.symm^[t.val] z') := by
      dsimp only [w']; abel
    have he : w'=w := hunique w' hn (fun t => by
        rw [huf,huf]
        simp only [f,localMap,Function.comp_apply]
        rw [(extChartAt I (a t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hx' t.castSucc).1)]
        exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ z').symm)
      (fun t => by
        rw [hvf,hvf]
        simp only [g,localMap,Function.comp_apply]
        rw [(extChartAt I (b t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hy' t.castSucc).1)]
        exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ z').symm)
      (by rw [huf,hvf,hab]; rfl)
      (by simpa only [w',u,Fin.val_last] using hp')
      (by simpa only [w',v,Fin.val_last] using hq')
    apply (extChartAt I (a 0)).injOn
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hx' 0).1)
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hz 0).1)
    have hfirst := congrArg (fun q : Paths (E (d:=d)) n n => q.1 0) he
    have hc := (hz 0).2
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hc
    rw [hc,←hfirst, huf]
    rfl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open FiniteGreen FiniteGreen.Matching ShortBin
theorem gauged_join_ideal (Smap : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),Smap^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),Smap.symm^[t.val] y∈(chartAt H (b t)).source)
    (hintx : I.IsInteriorPoint x) (hinty : I.IsInteriorPoint y)
    {K ε γ g α : ℝ} (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    (V W : Submodule ℝ (E (d:=d)))
    (hdV : Module.finrank ℝ ((A.splitting S).fast n).range=Module.finrank ℝ V)
    (hdW : Module.finrank ℝ ((Z.splitting T).fast n).range=Module.finrank ℝ W)
    (hcV : ‖((A.splitting S).fast n).range.starProjection-V.starProjection‖≤1/2)
    (hcW : ‖((Z.splitting T).fast n).range.starProjection-W.starProjection‖≤1/2)
    (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2)
    (hsA : ∀ j∈S,A.lam j≤γ-g) (hfA : ∀ j∈Sᶜ,γ+g≤A.lam j)
    (hsZ : ∀ j∈T,Z.lam j≤ -γ-g) (hfZ : ∀ j∈Tᶜ,-γ+g≤Z.lam j)
    (hgap : (2*Real.exp (2*K))*(2*(2*Real.exp (2*K)^2*Real.exp (-2*g*n)))≤1/2)
    (hα : |γ|+|g|≤α)
    (hstep₁ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap (a t.castSucc) (a t.succ) (Smap^[t.val] x))*A.U t=
        A.U (t+1)*EuclideanSplitting.rate A.lam 1)
    (hstep₂ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap.symm (b t.castSucc) (b t.succ) (Smap.symm^[t.val] y))*Z.U t=
        Z.U (t+1)*EuclideanSplitting.rate Z.lam 1)
    {C r δ : ℝ}
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (Smap^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (Smap^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (Smap.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ⊆
      domainU I Smap (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ⊆
      domainU I Smap.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : bvpInverseBound K α n*C*δ≤1/4)
    (hdata : bvpInverseBound K α n*C*r≤δ/4) :
    let C₁ := (A.splitting S).terminalProjection n V hdV hcV
    let C₂ := (Z.splitting T).terminalProjection n W hdW hcW
    let Q := bvpInverseBound K α n
    ∃ z : M,
      (∀ t : Fin (n+1),Smap^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (Smap^[t.val] z)-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),Smap.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z)-
        (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (Smap^[t.val] z)-
        (extChartAt I (a t)) (Smap^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-
        (extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ‖(extChartAt I (a 0)) z-(extChartAt I (a 0)) x-
        (A₀.splitting S₀).slow 0 ((extChartAt I (b 0)) y-(extChartAt I (a 0)) x)‖≤
        4*Real.exp (2*K)*(2*Real.exp (2*K))*(ε+2*Real.exp (2*K)^2*Real.exp (-2*g*n))*(C*r)+
          Q*C*(2*C*Q*r)^2 ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),Smap^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (Smap^[t.val] z')-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),Smap.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (Smap.symm^[t.val] z')-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z')-
          (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 → z'=z := by
  intro C₁ C₂ Q
  obtain ⟨L,hL,hK,hcorr,hκ₁,hκ₂⟩ := gauge_boundary_control A₀ A Z S₀ S T V W
    hdV hdW hcV hcW hε hεhalf hdS hdT hcS hcT hsmall hsA hfA hsZ hfZ hgap
  have hnα : 0≤α := (add_nonneg (abs_nonneg γ) (abs_nonneg g)).trans hα
  have hboundA := A.unweighted S hnα
    (fun j hj => (hsA j hj).trans (by linarith [le_abs_self γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [neg_le_abs γ,neg_le_abs g]) (hfA j hj))
  have hboundZ := Z.unweighted T hnα
    (fun j hj => (hsZ j hj).trans (by linarith [neg_le_abs γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [le_abs_self γ,neg_le_abs g]) (hfZ j hj))
  have hU : 1≤bvpGrowth K α n := (by norm_num : (1:ℝ)≤2).trans (bvpGrowth_ge_two K α n)
  have hUG : Real.exp (2*K+α*n)≤bvpGrowth K α n := by dsimp [bvpGrowth]; linarith
  have hA₁ (t : Fin n) : fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))=A.evolution.map (t+1) t :=
    gauge_actual_step I Smap _ _ _ A t (hx t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hx t.succ)
      (interior_iterate I Smap hintx t) (hstep₁ t)
  have hA₂ (t : Fin n) : fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))=Z.evolution.map (t+1) t :=
    gauge_actual_step I Smap.symm _ _ _ Z t (hy t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hy t.succ)
      (interior_iterate I Smap.symm hinty t) (hstep₂ t)
  have hcontract' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*δ≤1/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hcontract
  have hdata' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*r≤δ/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hdata
  have hs₀ : ‖(A₀.splitting S₀).slow 0‖≤Real.exp (2*K) :=
    EuclideanSplitting.splitting_slow_norm _ _ _ _ _ _ 0
      (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hf₀ : ‖(A₀.splitting S₀).fast 0‖≤Real.exp (2*K) :=
    EuclideanSplitting.splitting_fast_norm _ _ _ _ _ _ 0
      (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hc₁ : ‖(A.splitting S).initialSpace.starProjection-
      ((A₀.splitting S₀).slow 0).range.starProjection‖≤ε := by
    simpa only [FiniteGreen.Splitting.initialSpace,←A.space_eq_range,←A₀.space_eq_range,
      norm_sub_rev] using hcS
  have hc₂ : ‖(Z.splitting T).initialSpace.starProjection-
      ((A₀.splitting S₀).fast 0).range.starProjection‖≤ε := by
    have heT : ((A₀.splitting S₀).fast 0).range = A₀.space S₀ᶜ :=
      EuclideanSplitting.splitting_fast_range _ _ _ _ _ _ 0
    simpa only [FiniteGreen.Splitting.initialSpace,←Z.space_eq_range,
      heT,norm_sub_rev] using hcT
  have hjoin := actual_join_ideal I Smap a b x y hab hx hy A.evolution Z.evolution
    (A.splitting S) (Z.splitting T) C₁ C₂ L hL hU hK A₀.evolution (A₀.splitting S₀)
    (Real.exp_nonneg _) hε (by positivity) hc₁ hc₂ hκ₁ hκ₂ hs₀ hf₀ hcorr
    (fun s u hsu hun => (hboundA.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundA.2 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.2 s u hsu hun).trans hUG)
    (((A.splitting S).terminalProjection_J_norm n V hdV hcV).trans (bvpGrowth_ge_two K α n))
    (((A.splitting S).terminalProjection_P_norm n V hdV hcV).trans hU)
    (((Z.splitting T).terminalProjection_J_norm n W hdW hcW).trans (bvpGrowth_ge_two K α n))
    (((Z.splitting T).terminalProjection_P_norm n W hdW hcW).trans hU)
    hC hr hδ hA₁ hA₂ hd₁ hd₂ hder₁ hder₂ ht₁ ht₂ hdom₁ hdom₂ hnear hcontract' hdata'
  simpa only [Q,bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hjoin
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

omit [ProperSpace M] in
lemma coord_refl_same (a x : M) (hx : x∈(chartAt H a).source) :
    coord I (Diffeomorph.refl I M ∞) a a x=1 := by
  rw [←chartChange_coe I a a x hx hx]
  ext v
  simp [chartChange]

noncomputable def BilateralGauge.forward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d n B :=
  ShortBin.Gauge.ofFinite A.UF A.VF A.lam (fun t _ => A.invF t) A.normF

noncomputable def BilateralGauge.backward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d n B :=
  ShortBin.Gauge.ofFinite A.UB A.VB (fun j => -A.lam j) (fun t _ => A.invB t) A.normB

/-- The common-bin spaces now belong to the ORIGINAL good bilateral gauges.
All carried intermediate charts have disappeared from the conclusion. Only
initial coarse-bin coordinates are used, so no orbit-code partition appears. -/
theorem uniform_genuine_bin_splitting (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0 < rF ∧ 1 ≤ CF ∧ 0 < rB ∧ 1 ≤ CB ∧ 1 ≤ D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J)
        (n N : ℕ) (B R h g : ℝ) (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N ≤ n → (∀ i,c (x i)=c (x e)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,‖(extChartAt I (a (c (x e)))) (x i)-
          (extChartAt I (a (c (x e)))) (x e)‖ ≤ h) →
        CF^N*h ≤ rF → CB^N*h ≤ rB → 0 < g →
        Real.exp (-2*g*N+4*(B+Real.log D)) ≤ 1/2 →
        let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
        δ < Real.exp (-2*(B+Real.log D))/2 →
        Real.exp (-2*g*N+4*(B+Real.log D))+
          δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D)) ≤ 1/2 →
        ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
          (∀ i,(∀ k,(A i).lam k < γ-g ∨ γ+g < (A i).lam k) ∧
            (Finset.univ.filter (fun k => γ < (A i).lam k)).card=
              (Finset.univ.filter (fun k => γ < (A e).lam k)).card) ∧
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          (∀ i,‖(((A i).forward I S a c).space (Finset.univ.filter (fun k => (A i).lam k ≤ γ))).starProjection-
            (((A e).forward I S a c).space (Finset.univ.filter (fun k => (A e).lam k ≤ γ))).starProjection‖ ≤ 3*ε) ∧
          ∀ i,‖(((A i).forward I S a c).space (Finset.univ.filter (fun k => γ < (A i).lam k))).starProjection-
            (((A e).forward I S a c).space (Finset.univ.filter (fun k => γ < (A e).lam k))).starProjection‖ ≤ 3*ε := by
  classical
  obtain ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,hh⟩ :=
    uniform_genuine_bin_gauges I hclosed S a K hK hKU
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,
    fun c J x e n N B R h g A hc hN hcommon hint hdist hsF hsB hg hdecay hnoise hsmall => ?_⟩
  let cF (t : ℕ) := c (S^[t] (x e))
  let cB (t : ℕ) := c (S.symm^[t] (x e))
  have hsource (i : J) : x i∈(chartAt H (a (c (x e)))).source := by
    rw [←hcommon i]
    exact hKU _ (hc _)
  obtain ⟨F,Z,hlam,hcenter,hstepF,hstepB,hprodF,hprodB,hform⟩ :=
    hh c J x e cF cB n N B R h A hc hN rfl
      (fun _ _ => hc _) (fun _ _ => hc _) hint hsource hdist hsF hsB
  have hzero (i : J) : (F i).U 0=(A i).UF 0 ∧ (F i).V 0=(A i).VF 0 := by
    have hh := hform i 0 (Nat.zero_le N)
    have hid := coord_refl_same I (a (c (x e))) (x i) (hsource i)
    have hh' := And.intro hh.1 hh.2.1
    simpa only [cF,Function.iterate_zero_apply,hcommon i,hid,map_one,one_mul,mul_one] using hh'
  have hspace (i : J) (T : Finset (Fin d)) :
      (F i).space T=((A i).forward I S a c).space T := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forward,ShortBin.Gauge.ofFinite,
      Nat.zero_min,(hzero i).1,(hzero i).2]
  have hh0 : 0 ≤ h := (norm_nonneg _).trans (hdist e)
  let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hnF : 0 ≤ (N:ℝ)*CF*CF^(2*N)*h := by positivity
  have hnB : 0 ≤ (N:ℝ)*CB*CB^(2*N)*h := by positivity
  have hbF : (N:ℝ)*CF*CF^(2*N)*h ≤ δ := by dsimp [δ]; nlinarith
  have hbB : (N:ℝ)*CB*CB^(2*N)*h ≤ δ := by dsimp [δ]; nlinarith
  obtain ⟨j,hgap,hslow,hfast⟩ := ShortBin.common_splittings F Z e hg hδ
    (fun i => (hprodF i).trans hbF) (fun i => (hprodB i).trans hbB)
    (fun i => (hcenter i).1) (fun i => (hcenter i).2)
    (fun i k => by rw [(hlam i k).2,(hlam i k).1]) hdecay hnoise hsmall
  have hFl (i : J) : (F i).lam=(A i).lam := funext fun k => (hlam i k).1
  refine ⟨j,?_,?_,?_⟩
  · simpa only [hFl] using hgap
  · simpa only [hFl,hspace] using hslow
  · simpa only [hFl,hspace] using hfast
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Spaces of the genuine long-window gauge in its original endpoint chart. -/
noncomputable def BilateralGauge.forwardSpace (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) (t : ℕ) (T : Finset (Fin d)) :=
  EuclideanSplitting.groupSpace (A.UF t) (A.VF t) (A.invF t).1 (A.invF t).2 T

noncomputable def BilateralGauge.backwardSpace (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) (t : ℕ) (T : Finset (Fin d)) :=
  EuclideanSplitting.groupSpace (A.UB t) (A.VB t) (A.invB t).1 (A.invB t).2 T

/-- Endpoint-bin comparison with NO carried basis or extra threshold in the
conclusion. The reference is chosen among original certificates reaching the
same endpoint bin from a fixed starting bin. -/
theorem uniform_original_endpoint_fast_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0<r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J)
        (n N : ℕ) (B R h γ g : ℝ) (T : J → Finset (Fin d))
        (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ i,c (S^[n] (x i))=c (S^[n] (x e))) →
        (∀ i,I.IsInteriorPoint (S^[n] (x i))) →
        (∀ i,‖(extChartAt I (a (c (S^[n] (x e))))) (S^[n] (x i))-
          (extChartAt I (a (c (S^[n] (x e))))) (S^[n] (x e))‖≤h) →
        C₁^N*h≤r → 0≤h →
        (∀ i,(T e).card=(T i).card) →
        (∀ i,∀ j∈(T i)ᶜ,(A i).lam j≤γ-g) →
        (∀ i,∀ j∈T i,γ+g≤(A i).lam j) →
        (let ε := Real.exp ((γ-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
        ε≤1/2) →
        ∀ i,‖(A i |>.forwardSpace I S a c n (T i)).starProjection-
          (A e |>.forwardSpace I S a c n (T e)).starProjection‖≤
            3*(Real.exp ((γ-g)*N+2*(B+Real.log D))*
              (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ :=
    uniform_endpoint_fast_comparison I hclosed S a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e n N B R h γ g T A hc hN hcommon
    hint hdist ht hn hdim hslow hfast hsmall => ?_⟩
  let cR (t : ℕ) := c (S.symm^[t] (S^[n] (x e)))
  have hsource (i : J) : S^[n] (x i)∈(chartAt H (a (cR 0))).source := by
    change S^[n] (x i)∈(chartAt H (a (c (S^[n] (x e))))).source
    rw [←hcommon i]
    exact hKU _ (hc _)
  obtain ⟨F,hlam,hform,hclose⟩ := hh c J x e cR n N B R h γ g T A hc hN
    (fun _ _ => hc _) hint hsource hdist ht hn hdim hslow hfast hsmall
  have hzero (i : J) : (F i).U 0=(A i).UF n ∧ (F i).V 0=(A i).VF n := by
    have hid := coord_refl_same I (a (cR 0)) (S^[n] (x i)) (hsource i)
    have hc0 : c (S^[n] (x i))=cR 0 := hcommon i
    simpa only [hc0,hid,map_one,one_mul,mul_one] using hform i
  have hspace (i : J) : (F i).space (T i)=(A i).forwardSpace I S a c n (T i) := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forwardSpace,(hzero i).1,(hzero i).2]
  intro i
  simpa only [hspace] using hclose i
end SmoothObstruction.ManifoldCoordinates

end

end OAI
