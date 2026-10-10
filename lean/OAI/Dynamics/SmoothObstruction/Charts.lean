import OAI.Dynamics.SmoothObstruction.Splitting

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.GoodStationary
open Filter Topology

lemma floor_burden_eq (k : ℕ) :
    floorAt k*(2:ℝ)^k=Real.exp ((9*Real.log 2/10)*(k:ℝ)) := by
  have hp : (2:ℝ)^k=Real.exp (Real.log 2*(k:ℝ)) := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [floorAt,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),hp,←Real.exp_add]
  congr 1
  ring

lemma burden_ge_one (b : ℕ → ℝ) (hb : ∀ k,floorAt k≤b k) (k : ℕ) :
    1≤b k*(2:ℝ)^k := by
  have hc : 0≤9*Real.log 2/10 := by positivity
  have he := Real.one_le_exp_iff.mpr (mul_nonneg hc (Nat.cast_nonneg k))
  rw [←floor_burden_eq] at he
  exact he.trans (mul_le_mul_of_nonneg_right (hb k) (pow_nonneg (by norm_num) _))

lemma eventual_log_le_burden (b : ℕ → ℝ) (hb : ∀ k,floorAt k≤b k) :
    ∀ᶠ k in atTop,Real.log ((2^(k+1):ℕ)+1)≤b k*(2:ℝ)^k := by
  have hc : 0<9*Real.log 2/10 := by positivity
  have ho := (isLittleO_pow_exp_pos_mul_atTop 1 hc).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  filter_upwards [ho.bound (show (0:ℝ)<1/3 by norm_num),Filter.eventually_ge_atTop 1] with k hk hk1
  simp only [Function.comp_apply,pow_one,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k),
    abs_of_pos (Real.exp_pos _)] at hk
  have hpow : ((2^(k+1):ℕ):ℝ)+1≤(2:ℝ)^(k+2) := by
    have hh : (1:ℝ)≤2^(k+1) := one_le_pow₀ (by norm_num)
    calc
      _ = (2:ℝ)^(k+1)+1 := by norm_cast
      _ ≤ (2:ℝ)^(k+1)*2 := by linarith
      _ = (2:ℝ)^(k+2) := by simp only [show k+2=(k+1)+1 by omega,pow_succ]
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<((2^(k+1):ℕ):ℝ)+1) hpow
  rw [Real.log_pow] at hlog
  have h2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkk : (k:ℝ)+2≤3*k := by exact_mod_cast (show k+2≤3*k by omega)
  have hlog' : Real.log (((2^(k+1):ℕ):ℝ)+1)≤3*k := by
    exact hlog.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (by simpa using hkk))
  have he : 3*(k:ℝ)≤floorAt k*2^k := by rw [floor_burden_eq]; linarith
  exact hlog'.trans (he.trans (mul_le_mul_of_nonneg_right (hb k) (by positivity)))
end SmoothObstruction.GoodStationary

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_iterate (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) (t : ℕ) :
    shift^[t] (code S A x)=code S A (S^[t] x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,←code_shift,Function.iterate_succ_apply']

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma matrix_at_actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (p : Path (X:=X) (d:=d) (K:=K)) (hp : p∈Actual S A) (t : ℕ) :
    (matrix (shift^[t] p)).toContinuousLinearMap=(A (S^[t] (p 0).1)).val := by
  have he : shift^[t] p=code S A (S^[t] (p 0).1) := by
    conv_lhs => rw [show p=code S A (p 0).1 from hp]
    exact code_iterate S A (p 0).1 t
  rw [he]
  simp only [matrix,code,zpow_zero,Homeomorph.one_apply]
  rfl

/-- Quantitative finite gauges for the genuine bounded measurable cocycle.
The compact stationary QR lift, square-summable burdens, compact good
sets, and their original base masses are all constructed. On every good
witness the operator identity uses the ACTUAL original cocycle, not a
free triangular surrogate or a separately assumed frame process. -/
theorem actual_good_gauges (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    {η : ℝ} (hη : 0<η) :
    ∃ (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (b : ℕ → ℝ) (G : ℕ → Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (R C : ℝ),
      0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
      Summable (fun k => (b k)^2) ∧
      (∀ k,IsCompact (G k) ∧
        (∀ z∈G k,z.1∈Actual S A) ∧
        1-η/100≤(ν : Measure _).real (G k) ∧
        IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
        1-η/100≤(μ : Measure X).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k)) ∧
      ∀ᶠ k in atTop,∀ z∈G k,
        ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
          (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
          (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b k*2^k))) ∧
          (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b k*2^k))) ∧
          (∀ t<2^(k+1),
            (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (A (S^[t] (z.1 0).1)).val*P t=
              P (t+1)*EuclideanSplitting.rate lam 1) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  obtain ⟨ν,b,G,hbp,hbf,hbs,hG⟩ := compact_actual_good S A hA μ hS hη
  obtain ⟨R,C,hR,hC,hg⟩ := QR.compact_good_gauge
    (shift (X:=X) (d:=d) (K:=K)) matrix continuous_matrix
  refine ⟨ν,b,G,R,C,hR,hC,hbp,hbf,hbs,fun k => ?_,?_⟩
  · exact ⟨(hG k).1,fun z hz => ((hG k).2.1 z hz).1,(hG k).2.2⟩
  · filter_upwards [GoodStationary.eventual_log_le_burden b hbf] with k hk
    intro z hz
    obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hEq⟩ := hg k (b k) z ((hG k).2.1 z hz).2
      (GoodStationary.burden_ge_one b hbf k) hk
    refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,fun t ht => ?_⟩
    have ha := ((hG k).2.1 z hz).1
    simpa only [matrix_at_actual S A z.1 ha] using hEq t ht
end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual compact-manifold derivative gauges, constructed uniformly from
smoothness, compactness and the invariant original probability. The finite
chart selector, stationary frame lift, summable error sequence, large
compact middle-point sets and two-sided invertible gauges are all produced.
This is the linear input to the nonlinear switching proof, not that proof. -/
theorem manifold_good_gauges_discrete (S : Diffeomorph I I M M ∞)
    (μ : ProbabilityMeasure M) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    {η : ℝ} (hη : 0<η) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι) (D : ℝ)
      (A : M → CompactMatrix.Alphabet d D),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧ 0<D ∧ Measurable A ∧
      (∀ x,(A x).val=coord I S (a (c x)) (a (c (S x))) x) ∧
      ∃ (ν : ProbabilityMeasure (OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d))
        (b : ℕ → ℝ) (G : ℕ → Set (OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d))
        (R C : ℝ),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧
          (∀ z∈G k,z.1∈OrbitCocycle.Actual S.toHomeomorph A) ∧
          1-η/100≤(ν : Measure _).real (G k) ∧
          IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
          1-η/100≤(μ : Measure M).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k)) ∧
        ∀ᶠ k in atTop,∀ z∈G k,
          ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
            (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
            (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b k*2^k))) ∧
            (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b k*2^k))) ∧
            (∀ t<2^(k+1),let x := S^[t] (z.1 0).1
              (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
                (coord I S (a (c x)) (a (c (S x))) x)*P t=
                P (t+1)*EuclideanSplitting.rate lam 1) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq⟩ := actual_coordinate_cocycle_discrete I S
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  obtain ⟨ν,b,G,R,C,hR,hC,hbp,hbf,hbs,hG,hg⟩ :=
    OrbitCocycle.actual_good_gauges S.toHomeomorph A hA μ hS hη
  refine ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq,
    ν,b,G,R,C,hR,hC,hbp,hbf,hbs,hG,?_⟩
  filter_upwards [hg] with k hk
  intro z hz
  obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hEq⟩ := hk z hz
  refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,fun t ht => ?_⟩
  simpa only [heq,Diffeomorph.coe_toHomeomorph] using hEq t ht
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Actual reverse derivative in a pair of fixed charts, also at boundary points. -/
lemma coord_inverse_step (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈(chartAt H a).source) (hy : S x∈(chartAt H b).source) :
    coord I S.symm b a (S x)*coord I S a b x=1 := by
  have hi : (mfderiv I I S.symm (S x)).comp (mfderiv I I S x)=
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [←mfderiv_comp x (S.symm.mdifferentiable (by simp) _) (S.mdifferentiable (by simp) _)]
    have he : ((S.symm : M → M) ∘ (S : M → M))=id := by
      funext y
      exact S.symm_apply_apply y
    rw [he,mfderiv_id]
  rw [coord,coord]
  rw [ContinuousLinearMap.inCoordinates_eq hy (by simpa using hx),
    ContinuousLinearMap.inCoordinates_eq hx hy]
  ext v : 1
  simp only [mul_apply_eq_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  have hv := congrArg (fun f => f (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v)) hi
  change (mfderiv I I S.symm (S x)) ((mfderiv I I S x)
    (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v))=
    ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v at hv
  have hh := congrArg (fun w => ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx) w) hv
  rw [ContinuousLinearEquiv.apply_symm_apply] at hh
  convert hh using 1
  · change ((trivializationAt (E (d:=d)) (TangentSpace I) a)
      (⟨S.symm (S x),_⟩ : TotalSpace (E (d:=d)) (TangentSpace I))).2=
      ((trivializationAt (E (d:=d)) (TangentSpace I) a)
      (⟨x,_⟩ : TotalSpace (E (d:=d)) (TangentSpace I))).2
    congr 2
    exact Bundle.TotalSpace.ext (S.symm_apply_apply x) HEq.rfl
  · rfl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.OrbitCocycle
open Set
variable {X : Type*} [MetricSpace X] {d : ℕ} {K : ℝ}

lemma homeomorph_pow_iterate (S : X ≃ₜ X) (x : X) (n : ℕ) :
    (S^n) x=S^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Homeomorph.mul_apply,Function.iterate_succ_apply',ih]

lemma actual_middle (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (p : Path (X:=X) (d:=d) (K:=K)) (hp : p∈Actual S A) (n : ℕ) :
    (p (n:ℤ)).1=S^[n] (p 0).1 := by
  conv_lhs => rw [show p=code S A (p 0).1 from hp]
  simp only [code,zpow_natCast]
  exact homeomorph_pow_iterate S _ n

lemma backward_center (S : X ≃ₜ X) (x : X) {n t : ℕ} (ht : t≤n) :
    S.symm^[t] (S^[n] x)=S^[n-t] x := by
  have he : n=t+(n-t) := by omega
  conv_lhs => rw [he,Function.iterate_add_apply]
  exact (show Function.LeftInverse S.symm S from S.symm_apply_apply).iterate t _
end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Reversing a genuine finite derivative gauge is exact; the backward
rates are the negatives of the forward rates, and the same center basis
is used. No second derivative of a long iterate is introduced. -/
lemma reverse_gauge_step (S : Diffeomorph I I M M ∞)
    (c : ℕ → M) (x : ℕ → M) (P : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (j : ℕ)
    (hx : S (x j)=x (j+1))
    (hsrc : x j∈(chartAt H (c j)).source)
    (htar : x (j+1)∈(chartAt H (c (j+1))).source)
    (hstep : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (c j) (c (j+1)) (x j))*P j=
        P (j+1)*EuclideanSplitting.rate lam 1) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (c (j+1)) (c j) (x (j+1)))*P (j+1)=
        P j*EuclideanSplitting.rate (fun i => -lam i) 1 := by
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  let A := F.symm (coord I S (c j) (c (j+1)) (x j))
  let Z := F.symm (coord I S.symm (c (j+1)) (c j) (x (j+1)))
  have hZA : Z*A=1 := by
    rw [←map_mul,←hx,coord_inverse_step I S _ _ _ hsrc (by rwa [hx]),map_one]
  have hrate : EuclideanSplitting.rate lam 1*
      EuclideanSplitting.rate (fun i => -lam i) 1=1 := by
    have he : EuclideanSplitting.rate (fun i => -lam i) 1=
        EuclideanSplitting.rate lam (-1) := by simp [EuclideanSplitting.rate]
    rw [he,←EuclideanSplitting.rate_add]
    norm_num
  change Z*P (j+1)=_
  calc
    Z*P (j+1)=(Z*P (j+1))*
        (EuclideanSplitting.rate lam 1*EuclideanSplitting.rate (fun i => -lam i) 1) := by
      rw [hrate,mul_one]
    _=Z*(P (j+1)*EuclideanSplitting.rate lam 1)*
        EuclideanSplitting.rate (fun i => -lam i) 1 := by noncomm_ring
    _=Z*(A*P j)*EuclideanSplitting.rate (fun i => -lam i) 1 := by rw [←hstep]
    _=P j*EuclideanSplitting.rate (fun i => -lam i) 1 := by
      rw [←mul_assoc Z A,hZA,one_mul]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A finite two-sided gauge of the ACTUAL derivative, based at time zero.
This carries no splitting, threshold, switch, Jacobian or measure conclusion. -/
structure BilateralGauge (S : Diffeomorph I I M M ∞) {ι : Type*}
    (a : ι → M) (c : M → ι) (n : ℕ) (B R : ℝ) (x : M) where
  lam : Fin d → ℝ
  rate_bound : ∀ i,|lam i|≤R
  UF : ℕ → Matrix (Fin d) (Fin d) ℝ
  VF : ℕ → Matrix (Fin d) (Fin d) ℝ
  UB : ℕ → Matrix (Fin d) (Fin d) ℝ
  VB : ℕ → Matrix (Fin d) (Fin d) ℝ
  invF : ∀ t,UF t*VF t=1 ∧ VF t*UF t=1
  invB : ∀ t,UB t*VB t=1 ∧ VB t*UB t=1
  centerU : UB 0=UF 0
  centerV : VB 0=VF 0
  normF : ∀ t≤n,‖UF t‖≤Real.exp B ∧ ‖VF t‖≤Real.exp B
  normB : ∀ t≤n,‖UB t‖≤Real.exp B ∧ ‖VB t‖≤Real.exp B
  stepF : ∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
    (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*UF t=
      UF (t+1)*EuclideanSplitting.rate lam 1
  stepB : ∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
    (coord I S.symm (a (c (S.symm^[t] x))) (a (c (S.symm^[t+1] x))) (S.symm^[t] x))*UB t=
      UB (t+1)*EuclideanSplitting.rate (fun i => -lam i) 1

lemma center_from_gauge (S : Diffeomorph I I M M ∞) {ι : Type*}
    (a : ι → M) (c : M → ι) (hc : ∀ x,x∈(chartAt H (a (c x))).source)
    (x₀ : M) (n : ℕ) (B R : ℝ)
    (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hlam : ∀ i,|lam i|≤R) (hPQ : ∀ t,P t*Q t=1 ∧ Q t*P t=1)
    (hb : ∀ t≤n+n,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B)
    (hstep : ∀ t<n+n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a (c (S^[t] x₀))) (a (c (S^[t+1] x₀))) (S^[t] x₀))*P t=
        P (t+1)*EuclideanSplitting.rate lam 1) :
    Nonempty (BilateralGauge I S a c n B R (S^[n] x₀)) := by
  have hf (t : ℕ) : S^[t] (S^[n] x₀)=S^[n+t] x₀ := by
    rw [Nat.add_comm n t,Function.iterate_add_apply]
  have hr (t : ℕ) (ht : t≤n) : S.symm^[t] (S^[n] x₀)=S^[n-t] x₀ :=
    OrbitCocycle.backward_center S.toHomeomorph x₀ ht
  refine ⟨{
    lam := lam
    rate_bound := hlam
    UF := fun t => P (n+t)
    VF := fun t => Q (n+t)
    UB := fun t => P (n-t)
    VB := fun t => Q (n-t)
    invF := fun t => hPQ (n+t)
    invB := fun t => hPQ (n-t)
    centerU := by simp
    centerV := by simp
    normF := fun t ht => hb (n+t) (by omega)
    normB := fun t ht => hb (n-t) (by omega)
    stepF := ?_
    stepB := ?_
  }⟩
  · intro t ht
    simp only [hf,←Nat.add_assoc]
    exact hstep (n+t) (by omega)
  · intro t ht
    rw [hr t ht.le,hr (t+1) (by omega)]
    have he : n-(t+1)+1=n-t := by omega
    have hh := reverse_gauge_step I S (fun j => a (c (S^[j] x₀)))
      (fun j => S^[j] x₀) P lam (n-(t+1))
      (by simp only [Function.iterate_succ_apply']) (hc _) (hc _)
      (hstep _ (by omega))
    simpa only [he] using hh

/-- The compact, large original-measure good base sets now carry actual
forward AND backward gauges about their own time-zero point. The QR path
witness is eliminated existentially; no measurable frame selection is used. -/
theorem good_bilateral_gauges [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : Diffeomorph I I M M ∞) (μ : ProbabilityMeasure M)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) {η : ℝ} (hη : 0<η) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧
      ∃ (b : ℕ → ℝ) (R C : ℝ) (G : ℕ → Set M),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧ 1-η/100≤(μ : Measure M).real (G k)) ∧
        ∀ᶠ k in atTop,∀ x∈G k,
          Nonempty (BilateralGauge I S a c (2^k) (C*(b k*2^k)) R x) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq,
    ν,b,F,R,C,hR,hC,hbp,hbf,hbs,hF,hg⟩ := manifold_good_gauges_discrete I S μ hS hη
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let G (k : ℕ) := (fun z : OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d =>
    (z.1 ((2^k:ℕ):ℤ)).1) '' F k
  refine ⟨ι,hfin,hmeas,hsc,a,K,c,hK,hKU,hc,hcK,b,R,C,G,hR,hC,hbp,hbf,hbs,
    fun k => ⟨(hF k).2.2.2.1,(hF k).2.2.2.2⟩,?_⟩
  filter_upwards [hg] with k hk
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hstep⟩ := hk z hz
  have he := OrbitCocycle.actual_middle S.toHomeomorph A z.1 ((hF k).2.1 z hz) (2^k)
  change (z.1 ((2^k:ℕ):ℤ)).1=S^[2^k] (z.1 0).1 at he
  dsimp only
  rw [he]
  have hn : (2^k:ℕ)+2^k=2^(k+1) := by rw [pow_succ]; omega
  apply center_from_gauge I S a c (fun x => hKU _ (hcK x)) (z.1 0).1 (2^k)
    (C*(b k*2^k)) R lam P Q hlam hPQ
  · intro t ht
    exact ⟨hP t (by rwa [←hn]),hQ t (by rwa [←hn])⟩
  · intro t ht
    have hh := hstep t (by rwa [←hn])
    simpa only [Function.iterate_succ_apply'] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def chartChange (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) : E (d:=d) ≃L[ℝ] E (d:=d) :=
  ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x ha).symm.trans
    ((trivializationAt (E (d:=d)) (TangentSpace I) b).continuousLinearEquivAt ℝ x hb)

lemma chartChange_coe (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) :
    (chartChange I a b x ha hb : E (d:=d) →L[ℝ] E (d:=d))=
      coord I (Diffeomorph.refl I M ∞) a b x := by
  rw [coord,ContinuousLinearMap.inCoordinates_eq ha hb]
  simp only [Diffeomorph.coe_refl,mfderiv_id]
  rfl

/-- Exact cocycle conjugation for independently fixed carried charts.
This is a relation between actual manifold derivatives, not a formal
similarity hypothesis supplied in place of them. -/
theorem coord_chart_change (S : Diffeomorph I I M M ∞) (a b a' b' x : M)
    (hx : x∈domain I S a b) (hx' : x∈domain I S a' b') :
    coord I S a' b' x=
      (chartChange I b b' (S x) hx.2 hx'.2 : E (d:=d) →L[ℝ] E (d:=d)) *
      coord I S a b x *
      (chartChange I a' a x hx'.1 hx.1 : E (d:=d) →L[ℝ] E (d:=d)) := by
  rw [←coordEquiv_coe I S a b x hx,←coordEquiv_coe I S a' b' x hx']
  ext v
  simp only [mul_apply_eq_comp,ContinuousLinearEquiv.coe_coe,
    coordEquiv,chartChange,ContinuousLinearEquiv.trans_apply]
  simp

lemma chartChange_inverse (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) :
    (chartChange I a b x ha hb).symm=chartChange I b a x hb ha := by
  ext v
  simp [chartChange]

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.CarriedCharts
open Set Metric
variable {M : Type*} [MetricSpace M] {ι : Type*} [Fintype ι]

lemma finite_positive_lower (r : ι → ℝ) (hr : ∀ i,0 < r i) :
    ∃ a : ℝ,0 < a ∧ ∀ i,a ≤ r i := by
  classical
  have hh (s : Finset ι) : ∃ a : ℝ,0 < a ∧ ∀ i∈s,a ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a,ha,has⟩ := ih
      refine ⟨min a (r i),lt_min ha (hr i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hj|hj
      · subst j; exact min_le_right _ _
      · exact (min_le_left _ _).trans (has j hj)
  obtain ⟨a,ha,hh⟩ := hh Finset.univ
  exact ⟨a,ha,fun i => hh i (Finset.mem_univ i)⟩

/-- The same radius works for every chart pair actually visited by S.
Inputs need not stay in the selected compact patches: the neighboring
orbit only needs to stay inside this fixed radius of the old orbit. -/
theorem uniform_domains (S : M → M) (hS : Continuous S)
    (K U : ι → Set M) (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) :
    ∃ r : ℝ,0 < r ∧ ∀ i j x,x∈K i → S x∈K j →
      closedBall x r⊆U i∩S ⁻¹' U j := by
  have hex (ij : ι × ι) : ∃ r : ℝ,0 < r ∧
      cthickening r (K ij.1∩S ⁻¹' K ij.2)⊆U ij.1∩S ⁻¹' U ij.2 := by
    apply ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage hS)).exists_cthickening_subset_open
    · exact (hU ij.1).inter ((hU ij.2).preimage hS)
    · intro x hx
      exact ⟨hKU _ hx.1,hKU _ hx.2⟩
  choose r hr hrU using hex
  obtain ⟨a,ha,har⟩ := finite_positive_lower r hr
  refine ⟨a,ha,fun i j x hx hSx y hy => ?_⟩
  exact hrU (i,j) (closedBall_subset_cthickening (E := K i∩S ⁻¹' K j) ⟨hx,hSx⟩ (r (i,j))
    (closedBall_subset_closedBall (har (i,j)) hy))

/-- Uniform carried domains for both time directions. No orientability,
connectedness, or absence of a boundary was used in this construction. -/
theorem uniform_bilateral_domains (S : M ≃ₜ M)
    (K U : ι → Set M) (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) :
    ∃ r : ℝ,0 < r ∧
      (∀ i j x,x∈K i → S x∈K j → closedBall x r⊆U i∩S ⁻¹' U j) ∧
      (∀ i j x,x∈K i → S.symm x∈K j → closedBall x r⊆U i∩S.symm ⁻¹' U j) := by
  obtain ⟨a,ha,haf⟩ := uniform_domains S S.continuous K U hK hU hKU
  obtain ⟨b,hb,hbf⟩ := uniform_domains S.symm S.symm.continuous K U hK hU hKU
  refine ⟨min a b,lt_min ha hb,?_,?_⟩
  · exact fun i j x hx hSx => (closedBall_subset_closedBall (min_le_left a b)).trans
      (haf i j x hx hSx)
  · exact fun i j x hx hSx => (closedBall_subset_closedBall (min_le_right a b)).trans
      (hbf i j x hx hSx)

section Manifold
variable {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

/-- Application to the actual chart domains chosen by the finite-atlas
producer. The selector may be discontinuous: no continuity is asserted or
needed for the selected cocycle. Comparisons use its fixed CARRIED chart. -/
theorem actual_chart_margins (S : M ≃ₜ M) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (c : M → ι) (hc : ∀ x,x∈K (c x)) :
    ∃ r : ℝ,0 < r ∧ ∀ x y,dist y x ≤ r →
      y∈(chartAt H (a (c x))).source ∧
      S y∈(chartAt H (a (c (S x)))).source ∧
      S.symm y∈(chartAt H (a (c (S.symm x)))).source := by
  obtain ⟨r,hr,hf,hb⟩ := uniform_bilateral_domains S K
    (fun i => (chartAt H (a i)).source) hK (fun i => (chartAt H (a i)).open_source) hKU
  refine ⟨r,hr,fun x y hxy => ?_⟩
  have h₁ := hf (c x) (c (S x)) x (hc x) (hc (S x)) hxy
  have h₂ := hb (c x) (c (S.symm x)) x (hc x) (hc (S.symm x)) hxy
  exact ⟨h₁.1,h₁.2,h₂.2⟩
end Manifold
end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniform bounds on actual chart conversions throughout fixed enlarged
compact patches. Thus gauges may be transported from a discontinuously
selected atlas to a carried atlas without adding point/scale-dependent
constants. These are derivatives of the identity on M, also at its boundary. -/
theorem uniform_chart_changes (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1 ≤ D ∧ ∀ i j x,
      x∈cthickening r (K i) → x∈cthickening r (K j) →
      x∈(chartAt H (a i)).source ∧ x∈(chartAt H (a j)).source ∧
      ‖coord I (Diffeomorph.refl I M ∞) (a i) (a j) x‖ ≤ D ∧
      ‖coord I (Diffeomorph.refl I M ∞) (a j) (a i) x‖ ≤ D := by
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (K i)⊆(chartAt H (a i)).source :=
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  choose r hr hrU using hex
  obtain ⟨r₀,hr₀,hr₀r⟩ := CarriedCharts.finite_positive_lower r hr
  let N (i : ι) := cthickening (r i) (K i)
  have hNC (i : ι) : IsCompact (N i) := (hK i).cthickening
  have hb (ij : ι×ι) : ∃ D : ℝ,∀ x∈N ij.1∩N ij.2,
      ‖coord I (Diffeomorph.refl I M ∞) (a ij.1) (a ij.2) x‖ ≤ D :=
    ((hNC ij.1).inter (hNC ij.2)).exists_bound_of_continuousOn
      ((continuousOn_coord I (Diffeomorph.refl I M ∞) (a ij.1) (a ij.2)).mono
        (fun x hx => ⟨hrU _ hx.1,hrU _ hx.2⟩))
  choose C hC using hb
  let D : ℝ := 1+∑ ij,|C ij|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hCD (ij : ι×ι) : C ij ≤ D := by
    have hh := Finset.single_le_sum (fun z _ => abs_nonneg (C z)) (Finset.mem_univ ij)
    dsimp [D]
    linarith [le_abs_self (C ij)]
  refine ⟨r₀,D,hr₀,hD,fun i j x hxi hxj => ?_⟩
  have hi : x∈N i := cthickening_mono (hr₀r i) (K i) hxi
  have hj : x∈N j := cthickening_mono (hr₀r j) (K j) hxj
  exact ⟨hrU i hi,hrU j hj,(hC (i,j) x ⟨hi,hj⟩).trans (hCD (i,j)),
    (hC (j,i) x ⟨hj,hi⟩).trans (hCD (j,i))⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniformly transport genuine finite gauges between any selected and
carried chart sequences lying in the enlarged finite atlas. All norm losses
are the same fixed D; the actual manifold-derivative conjugation identity
is proved above, and is not an extra cocycle assumption. -/
theorem uniform_carried_gauge (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1 ≤ D ∧
      ∀ (S : Diffeomorph I I M M ∞) (x : ℕ → M) (c e : ℕ → ι)
        (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ) (B : ℝ),
        (∀ t≤N,x t∈cthickening r (K (c t))) →
        (∀ t≤N,x t∈cthickening r (K (e t))) →
        (∀ t<N,S (x t)=x (t+1)) →
        (∀ t,P t*Q t=1 ∧ Q t*P t=1) →
        (∀ t≤N,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B) →
        (∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c t)) (a (c (t+1))) (x t))*P t=
            P (t+1)*EuclideanSplitting.rate lam 1) →
        ∃ P' Q' : ℕ → Matrix (Fin d) (Fin d) ℝ,
          (∀ t≤N,P' t*Q' t=1 ∧ Q' t*P' t=1) ∧
          (∀ t≤N,‖P' t‖≤D*Real.exp B ∧ ‖Q' t‖≤D*Real.exp B) ∧
          ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (e t)) (a (e (t+1))) (x t))*P' t=
              P' (t+1)*EuclideanSplitting.rate lam 1 := by
  classical
  obtain ⟨r,D,hr,hD,hh⟩ := uniform_chart_changes I a K hK hKU
  refine ⟨r,D,hr,hD,fun S x c e P Q lam N B hc he hx hPQ hb hEq => ?_⟩
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  have hmem t (ht : t≤N) := hh (c t) (e t) (x t) (hc t ht) (he t ht)
  let R (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t))
  let V (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t))
  have hRV (t : ℕ) (ht : t≤N) : R t*V t=1 ∧ V t*R t=1 := by
    have hm := hmem t ht
    have hR := chartChange_coe I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1
    have hV := chartChange_coe I (a (e t)) (a (c t)) (x t) hm.2.1 hm.1
    have hid : coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_comp_coe_symm
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    have hdi : coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_symm_comp_coe
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    constructor
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hid
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hdi
  have hnorm (t : ℕ) (ht : t≤N) : ‖R t‖≤D ∧ ‖V t‖≤D := by
    have hh' := (hmem t ht).2.2
    simpa only [R,V,←Matrix.l2_opNorm_toEuclideanCLM,
      F,StarAlgEquiv.apply_symm_apply] using hh'
  have hconj (t : ℕ) (ht : t<N) : F.symm (coord I S (a (e t)) (a (e (t+1))) (x t))=
      R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*V t := by
    have h₀ := hmem t ht.le
    have h₁ := hmem (t+1) (by omega)
    have hd₀ : x t∈domain I S (a (c t)) (a (c (t+1))) :=
      ⟨h₀.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.1⟩
    have hd₁ : x t∈domain I S (a (e t)) (a (e (t+1))) :=
      ⟨h₀.2.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.2.1⟩
    rw [coord_chart_change I S _ _ _ _ _ hd₀ hd₁]
    simp only [map_mul,chartChange_coe,hx t ht,R,V]
  refine ⟨fun t => R t*P t,fun t => Q t*V t,fun t ht => ?_,fun t ht => ?_,fun t ht => ?_⟩
  · constructor
    · calc
        _=R t*(P t*Q t)*V t := by noncomm_ring
        _=1 := by rw [(hPQ t).1,mul_one,(hRV t ht).1]
    · calc
        _=Q t*(V t*R t)*P t := by noncomm_ring
        _=1 := by rw [(hRV t ht).2,mul_one,(hPQ t).2]
  · constructor
    · exact (norm_mul_le _ _).trans (mul_le_mul (hnorm t ht).1 (hb t ht).1
        (norm_nonneg _) (by linarith))
    · exact (norm_mul_le _ _).trans (by
        calc
          ‖Q t‖*‖V t‖ ≤ Real.exp B*D := mul_le_mul (hb t ht).2 (hnorm t ht).2
            (norm_nonneg _) (Real.exp_pos B).le
          _=D*Real.exp B := mul_comm _ _)
  · rw [hconj t ht]
    calc
      _=R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*(V t*R t)*P t := by noncomm_ring
      _=R (t+1)*(F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*P t) := by
        rw [(hRV t ht.le).2,mul_one,mul_assoc]
      _=(R (t+1)*P (t+1))*EuclideanSplitting.rate lam 1 := by rw [hEq t ht,mul_assoc]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniformly transport genuine finite gauges between any selected and
carried chart sequences lying in the enlarged finite atlas. All norm losses
are the same fixed D; the actual manifold-derivative conjugation identity
is proved above, and is not an extra cocycle assumption. -/
theorem uniform_carried_gauge_explicit (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1 ≤ D ∧
      ∀ (S : Diffeomorph I I M M ∞) (x : ℕ → M) (c e : ℕ → ι)
        (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ) (B : ℝ),
        (∀ t≤N,x t∈cthickening r (K (c t))) →
        (∀ t≤N,x t∈cthickening r (K (e t))) →
        (∀ t<N,S (x t)=x (t+1)) →
        (∀ t,P t*Q t=1 ∧ Q t*P t=1) →
        (∀ t≤N,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B) →
        (∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c t)) (a (c (t+1))) (x t))*P t=
            P (t+1)*EuclideanSplitting.rate lam 1) →
        ∃ P' Q' : ℕ → Matrix (Fin d) (Fin d) ℝ,
          (∀ t≤N,P' t*Q' t=1 ∧ Q' t*P' t=1) ∧
          (∀ t≤N,‖P' t‖≤D*Real.exp B ∧ ‖Q' t‖≤D*Real.exp B) ∧
          (∀ t,P' t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t))*P t ∧
            Q' t=Q t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t))) ∧
          ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (e t)) (a (e (t+1))) (x t))*P' t=
              P' (t+1)*EuclideanSplitting.rate lam 1 := by
  classical
  obtain ⟨r,D,hr,hD,hh⟩ := uniform_chart_changes I a K hK hKU
  refine ⟨r,D,hr,hD,fun S x c e P Q lam N B hc he hx hPQ hb hEq => ?_⟩
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  have hmem t (ht : t≤N) := hh (c t) (e t) (x t) (hc t ht) (he t ht)
  let R (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t))
  let V (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t))
  have hRV (t : ℕ) (ht : t≤N) : R t*V t=1 ∧ V t*R t=1 := by
    have hm := hmem t ht
    have hR := chartChange_coe I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1
    have hV := chartChange_coe I (a (e t)) (a (c t)) (x t) hm.2.1 hm.1
    have hid : coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_comp_coe_symm
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    have hdi : coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_symm_comp_coe
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    constructor
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hid
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hdi
  have hnorm (t : ℕ) (ht : t≤N) : ‖R t‖≤D ∧ ‖V t‖≤D := by
    have hh' := (hmem t ht).2.2
    simpa only [R,V,←Matrix.l2_opNorm_toEuclideanCLM,
      F,StarAlgEquiv.apply_symm_apply] using hh'
  have hconj (t : ℕ) (ht : t<N) : F.symm (coord I S (a (e t)) (a (e (t+1))) (x t))=
      R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*V t := by
    have h₀ := hmem t ht.le
    have h₁ := hmem (t+1) (by omega)
    have hd₀ : x t∈domain I S (a (c t)) (a (c (t+1))) :=
      ⟨h₀.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.1⟩
    have hd₁ : x t∈domain I S (a (e t)) (a (e (t+1))) :=
      ⟨h₀.2.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.2.1⟩
    rw [coord_chart_change I S _ _ _ _ _ hd₀ hd₁]
    simp only [map_mul,chartChange_coe,hx t ht,R,V]
  refine ⟨fun t => R t*P t,fun t => Q t*V t,fun t ht => ?_,fun t ht => ?_,fun t => ⟨rfl,rfl⟩,fun t ht => ?_⟩
  · constructor
    · calc
        _=R t*(P t*Q t)*V t := by noncomm_ring
        _=1 := by rw [(hPQ t).1,mul_one,(hRV t ht).1]
    · calc
        _=Q t*(V t*R t)*P t := by noncomm_ring
        _=1 := by rw [(hRV t ht).2,mul_one,(hPQ t).2]
  · constructor
    · exact (norm_mul_le _ _).trans (mul_le_mul (hnorm t ht).1 (hb t ht).1
        (norm_nonneg _) (by linarith))
    · exact (norm_mul_le _ _).trans (by
        calc
          ‖Q t‖*‖V t‖ ≤ Real.exp B*D := mul_le_mul (hb t ht).2 (hnorm t ht).2
            (norm_nonneg _) (Real.exp_pos B).le
          _=D*Real.exp B := mul_comm _ _)
  · rw [hconj t ht]
    calc
      _=R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*(V t*R t)*P t := by noncomm_ring
      _=R (t+1)*(F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*P t) := by
        rw [(hRV t ht.le).2,mul_one,mul_assoc]
      _=(R (t+1)*P (t+1))*EuclideanSplitting.rate lam 1 := by rw [hEq t ht,mul_assoc]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
structure Gauge (d L : ℕ) (K : ℝ) where
  U : ℕ → Matrix (Fin d) (Fin d) ℝ
  V : ℕ → Matrix (Fin d) (Fin d) ℝ
  lam : Fin d → ℝ
  UV : ∀ t,U t*V t=1
  VU : ∀ t,V t*U t=1
  normU : ∀ t≤L,‖U t‖≤Real.exp K
  normV : ∀ t≤L,‖V t‖≤Real.exp K

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator

/-- Extend only beyond the finite window by its terminal value. This
extension is algebraically invertible at every index and never affects an
actual derivative equation within the window. -/
noncomputable def Gauge.ofFinite {d n : ℕ} {B : ℝ}
    (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hi : ∀ t≤n,P t*Q t=1 ∧ Q t*P t=1)
    (hb : ∀ t≤n,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B) : Gauge d n B where
  U t := P (min t n)
  V t := Q (min t n)
  lam := lam
  UV t := (hi _ (Nat.min_le_right _ _)).1
  VU t := (hi _ (Nat.min_le_right _ _)).2
  normU t ht := by simpa only [Nat.min_eq_left ht] using (hb t ht).1
  normV t ht := by simpa only [Nat.min_eq_left ht] using (hb t ht).2
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Attach the actual stationary gauges to any two fixed carried chart
codes. Forward and backward gauges have exactly the SAME center bases,
not merely nearby center subspaces. A single uniform additive burden pays
all chart changes, independently of the number of iterates. -/
theorem uniform_carried_bilateral (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0<r ∧ 1≤D ∧
      ∀ (S : Diffeomorph I I M M ∞) (c : M → ι) (x : M) (n : ℕ) (B R : ℝ)
        (A : BilateralGauge I S a c n B R x) (eF eB : ℕ → ι),
        (∀ y,y∈K (c y)) → eB 0=eF 0 →
        (∀ t≤n,S^[t] x∈cthickening r (K (eF t))) →
        (∀ t≤n,S.symm^[t] x∈cthickening r (K (eB t))) →
        ∃ F Z : ShortBin.Gauge d n (B+Real.log D),
          (∀ i,F.lam i=A.lam i) ∧ (∀ i,Z.lam i= -A.lam i) ∧
          Z.U 0=F.U 0 ∧ Z.V 0=F.V 0 ∧
          (∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (eF t)) (a (eF (t+1))) (S^[t] x))*F.U t=
              F.U (t+1)*EuclideanSplitting.rate F.lam 1) ∧
          ∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S.symm (a (eB t)) (a (eB (t+1))) (S.symm^[t] x))*Z.U t=
              Z.U (t+1)*EuclideanSplitting.rate Z.lam 1 := by
  obtain ⟨r,D,hr,hD,hcarry⟩ := uniform_carried_gauge_explicit I a K hK hKU
  refine ⟨r,D,hr,hD,fun S c x n B R A eF eB hc h0 heF heB => ?_⟩
  have hDpos : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hbound : D*Real.exp B=Real.exp (B+Real.log D) := by
    rw [Real.exp_add,Real.exp_log hDpos,mul_comm]
  have hmF t (_ht : t≤n) : S^[t] x∈cthickening r (K (c (S^[t] x))) :=
    self_subset_cthickening _ (hc _)
  have hmB t (_ht : t≤n) : S.symm^[t] x∈cthickening r (K (c (S.symm^[t] x))) :=
    self_subset_cthickening _ (hc _)
  obtain ⟨PF,QF,hiF,hbF,formF,stepF⟩ := hcarry S (fun t => S^[t] x)
    (fun t => c (S^[t] x)) eF A.UF A.VF A.lam n B hmF heF
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invF A.normF A.stepF
  obtain ⟨PB,QB,hiB,hbB,formB,stepB⟩ := hcarry S.symm (fun t => S.symm^[t] x)
    (fun t => c (S.symm^[t] x)) eB A.UB A.VB (fun i => -A.lam i) n B hmB heB
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invB A.normB A.stepB
  have hbF' t (ht : t≤n) : ‖PF t‖≤Real.exp (B+Real.log D) ∧ ‖QF t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbF t ht
  have hbB' t (ht : t≤n) : ‖PB t‖≤Real.exp (B+Real.log D) ∧ ‖QB t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbB t ht
  refine ⟨ShortBin.Gauge.ofFinite PF QF A.lam hiF hbF',
    ShortBin.Gauge.ofFinite PB QB (fun i => -A.lam i) hiB hbB',
    fun _ => rfl,fun _ => rfl,?_,?_,?_,?_⟩
  · change PB (min 0 n)=PF (min 0 n)
    rw [Nat.zero_min,(formB 0).1,(formF 0).1]
    simp only [Function.iterate_zero_apply,h0,A.centerU]
  · change QB (min 0 n)=QF (min 0 n)
    rw [Nat.zero_min,(formB 0).2,(formF 0).2]
    simp only [Function.iterate_zero_apply,h0,A.centerV]
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepF t ht
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepB t ht

theorem uniform_carried_bilateral_explicit (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0<r ∧ 1≤D ∧
      ∀ (S : Diffeomorph I I M M ∞) (c : M → ι) (x : M) (n : ℕ) (B R : ℝ)
        (A : BilateralGauge I S a c n B R x) (eF eB : ℕ → ι),
        (∀ y,y∈K (c y)) → eB 0=eF 0 →
        (∀ t≤n,S^[t] x∈cthickening r (K (eF t))) →
        (∀ t≤n,S.symm^[t] x∈cthickening r (K (eB t))) →
        ∃ F Z : ShortBin.Gauge d n (B+Real.log D),
          (∀ i,F.lam i=A.lam i) ∧ (∀ i,Z.lam i= -A.lam i) ∧
          Z.U 0=F.U 0 ∧ Z.V 0=F.V 0 ∧
          (∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (eF t)) (a (eF (t+1))) (S^[t] x))*F.U t=
              F.U (t+1)*EuclideanSplitting.rate F.lam 1) ∧
          (∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S.symm (a (eB t)) (a (eB (t+1))) (S.symm^[t] x))*Z.U t=
              Z.U (t+1)*EuclideanSplitting.rate Z.lam 1) ∧
          ∀ t≤n,
            F.U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] x))) (a (eF t)) (S^[t] x))*A.UF t ∧
            F.V t=A.VF t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (eF t)) (a (c (S^[t] x))) (S^[t] x)) ∧
            Z.U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S.symm^[t] x))) (a (eB t)) (S.symm^[t] x))*A.UB t ∧
            Z.V t=A.VB t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (eB t)) (a (c (S.symm^[t] x))) (S.symm^[t] x)) := by
  obtain ⟨r,D,hr,hD,hcarry⟩ := uniform_carried_gauge_explicit I a K hK hKU
  refine ⟨r,D,hr,hD,fun S c x n B R A eF eB hc h0 heF heB => ?_⟩
  have hDpos : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hbound : D*Real.exp B=Real.exp (B+Real.log D) := by
    rw [Real.exp_add,Real.exp_log hDpos,mul_comm]
  have hmF t (_ht : t≤n) : S^[t] x∈cthickening r (K (c (S^[t] x))) :=
    self_subset_cthickening _ (hc _)
  have hmB t (_ht : t≤n) : S.symm^[t] x∈cthickening r (K (c (S.symm^[t] x))) :=
    self_subset_cthickening _ (hc _)
  obtain ⟨PF,QF,hiF,hbF,formF,stepF⟩ := hcarry S (fun t => S^[t] x)
    (fun t => c (S^[t] x)) eF A.UF A.VF A.lam n B hmF heF
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invF A.normF A.stepF
  obtain ⟨PB,QB,hiB,hbB,formB,stepB⟩ := hcarry S.symm (fun t => S.symm^[t] x)
    (fun t => c (S.symm^[t] x)) eB A.UB A.VB (fun i => -A.lam i) n B hmB heB
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invB A.normB A.stepB
  have hbF' t (ht : t≤n) : ‖PF t‖≤Real.exp (B+Real.log D) ∧ ‖QF t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbF t ht
  have hbB' t (ht : t≤n) : ‖PB t‖≤Real.exp (B+Real.log D) ∧ ‖QB t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbB t ht
  refine ⟨ShortBin.Gauge.ofFinite PF QF A.lam hiF hbF',
    ShortBin.Gauge.ofFinite PB QB (fun i => -A.lam i) hiB hbB',
    fun _ => rfl,fun _ => rfl,?_,?_,?_,?_,?_⟩
  · change PB (min 0 n)=PF (min 0 n)
    rw [Nat.zero_min,(formB 0).1,(formF 0).1]
    simp only [Function.iterate_zero_apply,h0,A.centerU]
  · change QB (min 0 n)=QF (min 0 n)
    rw [Nat.zero_min,(formB 0).2,(formF 0).2]
    simp only [Function.iterate_zero_apply,h0,A.centerV]
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepF t ht
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepB t ht
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht] using
      And.intro (formF t).1 (And.intro (formF t).2 (formB t))

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def localMap (S : Diffeomorph I I M M ∞) (a b : M) : E (d:=d) → E (d:=d) :=
  extChartAt I b ∘ S ∘ (extChartAt I a).symm

/-- The actual derivative cocycle is the derivative of the actual local
coordinate map. Charts may be independently selected at each endpoint;
the formula is valid on half-space models without changing derivatives. -/
theorem coord_eq_fderivWithin (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) :
    fderivWithin ℝ (localMap I S a b) (range I) ((extChartAt I a) x)=coord I S a b x := by
  have hit : (extChartAt I a) x∈(extChartAt I a).target :=
    (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have hir : (extChartAt I a) x∈range I := extChartAt_target_subset_range a hit
  have huniq : UniqueMDiffWithinAt (𝓘(ℝ,E (d:=d))) (range I) ((extChartAt I a) x) :=
    (I.uniqueDiffOn _ hir).uniqueMDiffWithinAt
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I) hit
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hcomp := mfderiv_comp_mfderivWithin_of_eq hf hs huniq
    ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hchain := mfderiv_comp x (mdifferentiableAt_extChartAt (I:=I) hx.2)
    (S.contMDiff.mdifferentiable (by simp) x)
  rw [hchain] at hcomp
  have hcoord := inTangentCoordinates_eq_mfderiv_comp
    (I:=I) (I':=I) (f:=fun p : M×M => p.1) (g:=fun p : M×M => p.2)
    (ϕ:=fun p => mfderiv I I S p.1) (x₀:=(a,b)) (x:=(x,S x)) hx.1 hx.2
  change coord I S a b x=_ at hcoord
  rw [mfderivWithin_eq_fderivWithin] at hcomp
  have he := hcomp.trans hcoord.symm
  change fderivWithin ℝ ((extChartAt I b ∘ S) ∘ (extChartAt I a).symm)
    (range I) ((extChartAt I a) x)=coord I S a b x at he
  simpa only [localMap,Function.comp_assoc] using he

/-- In an interior orbit tube this is an ordinary derivative, exactly the
input of the finite-array nonlinear construction. -/
theorem hasFDerivAt_localMap (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    HasFDerivAt (localMap I S a b) (coord I S a b x) ((extChartAt I a) x) := by
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I)
    ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1))
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hh := hf.comp_mdifferentiableWithinAt_of_eq _ hs ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hd : DifferentiableWithinAt ℝ (localMap I S a b) (range I) ((extChartAt I a) x) := by
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp hh
  rw [←coord_eq_fderivWithin I S a b x hx]
  exact hd.hasFDerivWithinAt.hasFDerivAt (mem_interior_iff_mem_nhds.mp hint)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Actual coordinate expressions are genuinely smooth in every retained
interior tube. For a boundary model no smooth extension is assumed here:
the statement uses the interior of the original model range. -/
theorem contDiffAt_localMap (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    ContDiffAt ℝ ∞ (localMap I S a b) ((extChartAt I a) x) := by
  have hs := contMDiffWithinAt_extChartAt_symm_range (I:=I) (n:=∞) a
    ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1))
  have hf : ContMDiffAt I (𝓘(ℝ,E (d:=d))) ∞ (extChartAt I b ∘ S) x :=
    (contMDiffAt_extChartAt' (I:=I) hx.2).comp x (S.contMDiff x)
  have hh := hf.comp_contMDiffWithinAt_of_eq hs
    ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hd : ContDiffWithinAt ℝ ∞ (localMap I S a b) (range I)
      ((extChartAt I a) x) := contMDiffWithinAt_iff_contDiffWithinAt.mp hh
  exact hd.contDiffAt (mem_interior_iff_mem_nhds.mp hint)

/-- Fixed target linear projections preserve the actual local regularity
and have the expected derivative: this builds the endpoint maps used by the
inverse-function branch, not a new abstract replacement for DS^n. -/
theorem projected_localMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E (d:=d) →L[ℝ] F) (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    ContDiffAt ℝ ∞ (P ∘ localMap I S a b) ((extChartAt I a) x) ∧
      HasFDerivAt (P ∘ localMap I S a b) (P.comp (coord I S a b x))
        ((extChartAt I a) x) := by
  exact ⟨P.contDiff.contDiffAt.comp _ (contDiffAt_localMap I S a b x hx hint),
    P.hasFDerivAt.comp _ (hasFDerivAt_localMap I S a b x hx hint)⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.CarriedCharts
open Set Metric Filter Topology
open scoped ContDiff
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Uniform C2 bounds up to a closed model boundary, WITHOUT an extension
assumption. Ordinary derivatives are taken only in the original interior;
the bound is independent of distance to the boundary. -/
theorem uniform_c2_boundary (f : ι → E → F) (K U : ι → Set E) (H : Set E)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i)) (hH : IsClosed H)
    (hKU : ∀ i,K i⊆U i) (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i x,x∈K i →
      closedBall x r⊆U i ∧ ∀ y∈closedBall x r,y∈interior H →
        ContDiffAt ℝ ∞ (f i) y ∧
        ‖fderiv ℝ (f i) y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ C := by
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (K i)⊆U i :=
    (hK i).exists_cthickening_subset_open (hU i) (hKU i)
  choose r hr hrU using hex
  obtain ⟨a,ha,har⟩ := finite_positive_lower r hr
  let s (i : ι) := U i∩H
  let f₁ (i : ι) := fderivWithin ℝ (f i) (s i)
  let f₂ (i : ι) := fderivWithin ℝ (f₁ i) (s i)
  have hf₁ (i : ι) : ContDiffOn ℝ ∞ (f₁ i) (s i) :=
    (hf i).fderivWithin (huniq i) (by simp)
  have hf₂ (i : ι) : ContDiffOn ℝ ∞ (f₂ i) (s i) :=
    (hf₁ i).fderivWithin (huniq i) (by simp)
  have hb (i : ι) : ∃ C : ℝ,∀ y∈cthickening (r i) (K i)∩H,
      ‖f₁ i y‖ ≤ C ∧ ‖f₂ i y‖ ≤ C := by
    have hcomp : IsCompact (cthickening (r i) (K i)∩H) := (hK i).cthickening.inter_right hH
    have hsub : cthickening (r i) (K i)∩H⊆s i := fun y hy => ⟨hrU i hy.1,hy.2⟩
    obtain ⟨A,hA⟩ := hcomp.exists_bound_of_continuousOn (f := f₁ i)
      ((hf₁ i).continuousOn.mono hsub)
    obtain ⟨B,hB⟩ := hcomp.exists_bound_of_continuousOn (f := f₂ i)
      ((hf₂ i).continuousOn.mono hsub)
    exact ⟨max A B,fun y hy => ⟨(hA y hy).trans (le_max_left _ _),
      (hB y hy).trans (le_max_right _ _)⟩⟩
  choose C hC using hb
  let D : ℝ := 1+∑ i,|C i|
  have hD : 1 ≤ D := by
    dsimp [D]
    have hh : 0≤∑ i,|C i| := Finset.sum_nonneg (fun i _ => abs_nonneg (C i))
    linarith
  have hCD (i : ι) : C i ≤ D := by
    have hh : |C i| ≤ ∑ j,|C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j))
      (Finset.mem_univ i)
    dsimp [D]
    linarith [le_abs_self (C i)]
  refine ⟨a,D,ha,hD,fun i x hx => ?_⟩
  have hball : closedBall x a⊆cthickening (r i) (K i) :=
    (closedBall_subset_closedBall (har i)).trans (closedBall_subset_cthickening hx (r i))
  refine ⟨hball.trans (hrU i),fun y hy hyH => ?_⟩
  have hyU := hrU i (hball hy)
  have hys : s i∈𝓝 y := inter_mem ((hU i).mem_nhds hyU) (mem_interior_iff_mem_nhds.mp hyH)
  have heq : f₁ i =ᶠ[𝓝 y] fderiv ℝ (f i) := by
    filter_upwards [((hU i).inter isOpen_interior).mem_nhds ⟨hyU,hyH⟩] with z hz
    exact fderivWithin_of_mem_nhds (inter_mem ((hU i).mem_nhds hz.1)
      (mem_interior_iff_mem_nhds.mp hz.2))
  have hfirst : f₁ i y=fderiv ℝ (f i) y := heq.eq_of_nhds
  have hsecond : f₂ i y=fderiv ℝ (fderiv ℝ (f i)) y :=
    (fderivWithin_of_mem_nhds hys).trans heq.fderiv_eq
  have hb' := hC i y ⟨hball hy,interior_subset hyH⟩
  rw [hfirst,hsecond] at hb'
  exact ⟨(hf i y ⟨hyU,interior_subset hyH⟩).contDiffAt hys,
    hb'.1.trans (hCD i),hb'.2.trans (hCD i)⟩
end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An ambient open carrier of the exact local expression's relative
coordinate domain. It is NOT a smooth extension of the expression. -/
def domainU (S : Diffeomorph I I M M ∞) (a b : M) : Set (E (d:=d)) :=
  I.symm ⁻¹' ((chartAt H a).target∩(chartAt H a).symm ⁻¹' (S ⁻¹' (chartAt H b).source))

omit [IsManifold I ∞ M] in
lemma isOpen_domainU (S : Diffeomorph I I M M ∞) (a b : M) : IsOpen (domainU I S a b) :=
  ((chartAt H a).isOpen_inter_preimage_symm
    ((chartAt H b).open_source.preimage S.continuous)).preimage I.continuous_symm

omit [IsManifold I ∞ M] in
lemma map_mem_domainU (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : (extChartAt I a) x∈domainU I S a b := by
  have ht := (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have htar : I.symm ((extChartAt I a) x)∈(chartAt H a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at ht
    exact ht.1
  refine ⟨htar,?_⟩
  change S ((extChartAt I a).symm ((extChartAt I a) x))∈(chartAt H b).source
  rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1)]
  exact hx.2

theorem contDiffOn_localMap (S : Diffeomorph I I M M ∞) (a b : M) :
    ContDiffOn ℝ ∞ (localMap I S a b) (domainU I S a b∩range I) := by
  intro y hy
  have hyt : y∈(extChartAt I a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨hy.1.1,hy.2⟩
  have hby : S ((extChartAt I a).symm y)∈(chartAt H b).source := hy.1.2
  have hf : ContMDiffAt I (𝓘(ℝ,E (d:=d))) ∞ (extChartAt I b ∘ S)
      ((extChartAt I a).symm y) :=
    (contMDiffAt_extChartAt' (I:=I) hby).comp _ (S.contMDiff _)
  have hh := hf.comp_contMDiffWithinAt y
    (contMDiffWithinAt_extChartAt_symm_range (I:=I) (n:=∞) a hyt)
  have hd : ContDiffWithinAt ℝ ∞ (localMap I S a b) (range I) y :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hh
  exact hd.mono inter_subset_right

/-- Genuine uniform first and second derivative bounds for all actually
used local chart pairs. Valid for the closed half-space model, uniformly
as the reference point approaches the boundary. No extension theorem or
long-iterate C2 bound has been assumed. -/
theorem actual_uniform_c2 [T2Space M] {ι : Type*} [Fintype ι]
    (hclosed : IsClosed (range I)) (S : Diffeomorph I I M M ∞)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i j x,x∈K i → S x∈K j →
      closedBall ((extChartAt I (a i)) x) r⊆domainU I S (a i) (a j) ∧
      ∀ y∈closedBall ((extChartAt I (a i)) x) r,y∈interior (range I) →
        ContDiffAt ℝ ∞ (localMap I S (a i) (a j)) y ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (localMap I S (a i) (a j))) y‖ ≤ C := by
  let L (ij : ι×ι) := (extChartAt I (a ij.1)) '' (K ij.1∩S ⁻¹' K ij.2)
  have hcomp (ij : ι×ι) : IsCompact (L ij) :=
    ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a ij.1)).mono (fun x hx => by simpa only [extChartAt_source] using hKU _ hx.1))
  have hsub (ij : ι×ι) : L ij⊆domainU I S (a ij.1) (a ij.2) := by
    rintro z ⟨x,hx,rfl⟩
    exact map_mem_domainU I S (a ij.1) (a ij.2) x ⟨hKU _ hx.1,hKU _ hx.2⟩
  obtain ⟨r,C,hr,hC,hh⟩ := CarriedCharts.uniform_c2_boundary
    (fun ij : ι×ι => localMap I S (a ij.1) (a ij.2)) L
    (fun ij => domainU I S (a ij.1) (a ij.2)) (range I) hcomp
    (fun ij => isOpen_domainU I S (a ij.1) (a ij.2)) hclosed hsub
    (fun ij => by simpa only [inter_comm] using
      I.uniqueDiffOn.inter (isOpen_domainU I S (a ij.1) (a ij.2)))
    (fun ij => contDiffOn_localMap I S (a ij.1) (a ij.2))
  exact ⟨r,C,hr,hC,fun i j x hx hSx => hh (i,j) ((extChartAt I (a i)) x) ⟨x,⟨hx,hSx⟩,rfl⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma interior_coord (a x : M) (hx : x∈(chartAt H a).source) :
    (extChartAt I a) x∈interior (range I) ↔ I.IsInteriorPoint x := by
  rw [I.isInteriorPoint_iff_of_mem_atlas (by simp : (∞ : ℕ∞ω)≠0)
    (chart_mem_atlas H a) hx]
  exact ⟨fun h => (chartAt H a).mem_interior_extend_target
    ((chartAt H a).map_source hx) h,
    fun h => (chartAt H a).interior_extend_target_subset_interior_range h⟩

/-- Carried local expressions preserve the *original* model interior on
exactly their actual relative domains, even for manifolds with boundary. -/
theorem localMap_maps_interior (S : Diffeomorph I I M M ∞) (a b : M) :
    MapsTo (localMap I S a b) (domainU I S a b∩interior (range I))
      (interior (range I)) := by
  intro y hy
  have hyt : y∈(extChartAt I a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨hy.1.1,interior_subset hy.2⟩
  let x := (extChartAt I a).symm y
  have hx : x∈(chartAt H a).source := by
    simpa only [extChartAt_source] using (extChartAt I a).map_target hyt
  have hxy : (extChartAt I a) x=y := (extChartAt I a).right_inv hyt
  have hxi : I.IsInteriorPoint x := (interior_coord I a x hx).mp (hxy.symm ▸ hy.2)
  have hSi : I.IsInteriorPoint (S x) :=
    ((S.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hxi
  have hSx : S x∈(chartAt H b).source := hy.1.2
  exact (interior_coord I b (S x) hSx).mpr hSi

omit [IsManifold I ∞ M] in
lemma localMap_coordinates (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈(chartAt H a).source) :
    localMap I S a b ((extChartAt I a) x)=(extChartAt I b) (S x) := by
  simp only [localMap,Function.comp_apply,
    (extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx)]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.StandardModels
open Set
open scoped Manifold
lemma real_closed (d : ℕ) : IsClosed (range (𝓡 d)) := by simp
lemma real_convex (d : ℕ) : Convex ℝ (range (𝓡 d)) := (𝓡 d).convex_range
lemma half_closed (d : ℕ) [NeZero d] : IsClosed (range (𝓡∂ d)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact isClosed_le continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin d)).continuous
lemma half_convex (d : ℕ) [NeZero d] : Convex ℝ (range (𝓡∂ d)) := (𝓡∂ d).convex_range
end SmoothObstruction.StandardModels

end

end OAI
