import OAI.Dynamics.SmoothObstruction.GreenOperator
import OAI.Dynamics.SmoothObstruction.ExteriorPowers

namespace OAI

section

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma rate_eigen (lam : Fin d → ℝ) (l : ℝ) (j : Fin d) :
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l) (EuclideanSpace.basisFun (Fin d) ℝ j)=
      Real.exp (l*lam j) • EuclideanSpace.basisFun (Fin d) ℝ j := by
  ext i
  change ((rate lam l)*ᵥ (EuclideanSpace.basisFun (Fin d) ℝ j)) i=_
  simp only [rate,Matrix.mulVec_diagonal,EuclideanSpace.basisFun_apply,
    PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases hi : i=j
  · subst i; simp
  · simp [hi]

lemma selected_sum {p : ℕ} (s : powersetCard (Fin d) p) (lam : Fin d → ℝ) :
    (∑ i : Fin p,lam (powersetCard.ofFinEmbEquiv.symm s i))=∑ j∈s.val,lam j := by
  rw [powersetCard.ofFinEmbEquiv_symm_apply]
  have he := Finset.sum_map (s:=Finset.univ) (s.val.orderEmbOfFin s.prop).toEmbedding lam
  have hm : Finset.map (s.val.orderEmbOfFin s.prop).toEmbedding Finset.univ=s.val :=
    Finset.map_orderEmbOfFin_univ s.val s.prop
  rw [hm] at he
  exact he.symm

/-- The dominant exterior estimate of the actual matrix transition uses the
sum over the selected fast rates on every subinterval, not a coarse norm. -/
theorem transition_exterior_bound
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : (EuclideanSpace ℝ (Fin d)) →L[ℝ] _,
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
      C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
        Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j)) := by
  have hm (q : powersetCard (Fin d) S.card) :
      (∑ i : Fin S.card,lam (powersetCard.ofFinEmbEquiv.symm q i))≤∑ j∈S,lam j := by
    rw [selected_sum]
    exact RateSums.rate_sum_max lam S q.val hg q.prop hfast hslow
  have he := exterior_gauge_bound (EuclideanSpace.basisFun (Fin d) ℝ) S.card
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s))) lam
    (sub_nonneg.mpr (by exact_mod_cast hst) : 0≤(t:ℝ)-s)
    (Real.one_le_exp_iff.mpr hK) hC hpoly
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hU)
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hV)
    (rate_eigen lam _) hm
  simpa only [transition,map_mul] using he

/-- The actual nonleading diagonal eigenvalue is smaller by exp(-2g l).
This is valid when the slow rates are positive as well as when negative. -/
lemma nonleading_rate_product (lam : Fin d → ℝ) (S : Finset (Fin d))
    {γ g l : ℝ} (hg : 0≤g) (hl : 0≤l)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (q : powersetCard (Fin d) S.card) (hq : q.val≠S) :
    |∏ i : Fin S.card,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm q i))|≤
      Real.exp (l*((∑ j∈S,lam j)-2*g)) := by
  rw [eigen_exp_product,abs_of_pos (Real.exp_pos _),selected_sum]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (RateSums.strict_rate_sum_gap lam S q.val hg q.prop hq hfast hslow) hl)
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Actual projected maximal minor in fixed orthonormal endpoint coordinates.
The rows use the selected projection coordinates and the columns are arbitrary
starting vectors; starting bases need not be orthogonal. -/
noncomputable def projectedMinor (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) : ℝ :=
  (b.exteriorPower p).repr (exterior p A (exteriorPower.ιMulti ℝ p v)) s

lemma projectedMinor_eq_det (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    projectedMinor b p s A v=
      Matrix.det (fun i j : Fin p => b.repr (A (v i)) (powersetCard.ofFinEmbEquiv.symm s j)) := by
  change (b.exteriorPower p).toBasis.repr (exteriorPower.map p A.toLinearMap
    (exteriorPower.ιMulti ℝ p v)) s=_
  rw [exteriorPower.map_apply_ιMulti,b.toBasis_exteriorPower,
    exteriorPower.basis_repr_apply,exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

lemma projectedMinor_transfer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A B : E →L[ℝ] E) (v : Fin p → E) :
    |projectedMinor b p s B v-projectedMinor b p s A v|≤
      ‖exterior p B-exterior p A‖*‖exteriorPower.ιMulti ℝ p v‖ := by
  let e := b.exteriorPower p
  let w := exteriorPower.ιMulti ℝ p v
  have hcoord (z : (⋀[ℝ]^p E)) : |e.repr z s|≤‖z‖ := by
    rw [e.repr_apply_apply,←Real.norm_eq_abs]
    simpa only [e.norm_eq_one,one_mul] using norm_inner_le_norm (𝕜:=ℝ) (e s) z
  have h := hcoord ((exterior p B-exterior p A) w)
  simp only [sub_apply,map_sub] at h
  exact h.trans ((exterior p B-exterior p A).le_opNorm w)

/-- Basis-change and orbit-transfer errors are paid against the true exterior
operator norm. No coarse n-step C² estimate is substituted. -/
lemma projectedMinor_basis_transfer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A B : E →L[ℝ] E) (v w : Fin p → E) :
    |projectedMinor b p s B w-projectedMinor b p s A v|≤
      ‖exterior p B-exterior p A‖*‖exteriorPower.ιMulti ℝ p w‖+
      ‖exterior p A‖*‖exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v‖ := by
  have hb : |projectedMinor b p s A w-projectedMinor b p s A v|≤
      ‖exterior p A‖*‖exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v‖ := by
    let e := b.exteriorPower p
    have he : projectedMinor b p s A w-projectedMinor b p s A v=
        e.repr (exterior p A (exteriorPower.ιMulti ℝ p w-exteriorPower.ιMulti ℝ p v)) s := by
      simp only [map_sub,e,projectedMinor,PiLp.sub_apply]
    rw [he,e.repr_apply_apply,←Real.norm_eq_abs]
    exact (norm_inner_le_norm (𝕜:=ℝ) (e s) _).trans (by
      rw [e.norm_eq_one,one_mul]
      exact (exterior p A).le_opNorm _)
  exact (abs_sub_le _ _ _).trans
    (add_le_add (projectedMinor_transfer b p s A B w) hb)

/-- A uniform local modulus for the wedge of a fixed number of vectors.
This is used when replacing actual subspaces by fixed frame-bin references. -/
theorem exists_wedge_lipschitz (p : ℕ) (R : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ v w : Fin p → E,
      ‖v‖≤R → ‖w‖≤R →
      ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤C*‖v-w‖ := by
  obtain ⟨C,hC⟩ := (contDiff_wedge (E:=E) p).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : Fin p → E) R) (isCompact_closedBall 0 R)
  refine ⟨C,C.coe_nonneg,fun v w hv hw => ?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul v
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv) w
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw)

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Module Set.powersetCard
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A projected top wedge actually lies on the selected determinant line.
In particular its coefficient is its norm, including the empty group. -/
lemma projected_wedge_line (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (v : Fin p → E)
    (hv : ∀ i j,j∉s → b.repr (v i) j=0) :
    exteriorPower.ιMulti ℝ p v=
      projectedMinor b p s (ContinuousLinearMap.id ℝ E) v • (b.exteriorPower p) s := by
  classical
  have hm (q : powersetCard ι p) :
      projectedMinor b p q (ContinuousLinearMap.id ℝ E) v=
        (b.exteriorPower p).repr (exteriorPower.ιMulti ℝ p v) q := by
    unfold projectedMinor
    change (b.exteriorPower p).repr (exterior p 1 _) q=_
    rw [exterior_one]
    rfl
  apply (b.exteriorPower p).repr.injective
  ext q
  by_cases hq : q=s
  · subst q
    simp only [map_smul,OrthonormalBasis.repr_self,PiLp.smul_apply,smul_eq_mul,
      PiLp.single_apply,ite_true,mul_one]
    exact (hm s).symm
  · have hz : projectedMinor b p q (ContinuousLinearMap.id ℝ E) v=0 := by
      rw [projectedMinor_eq_det]
      obtain ⟨j,hjq,hjs⟩ := (exists_mem_notMem_iff_ne q s).mp hq
      obtain ⟨i,rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem q j).mpr hjq
      apply Matrix.det_eq_zero_of_column_eq_zero i
      intro k
      exact hv k _ hjs
    rw [←hm q]
    rw [hz,map_smul,OrthonormalBasis.repr_self]
    simp [hq]

lemma projected_wedge_norm (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (v : Fin p → E)
    (hv : ∀ i j,j∉s → b.repr (v i) j=0) :
    ‖exteriorPower.ιMulti ℝ p v‖=
      |projectedMinor b p s (ContinuousLinearMap.id ℝ E) v| := by
  rw [projected_wedge_line b p s v hv,norm_smul,
    (b.exteriorPower p).norm_eq_one,mul_one,Real.norm_eq_abs]

/-- Quantitative projected leading-volume lower bound from the actual
finite gauge and a left inverse of the endpoint projection on the fast
vectors. The eigenvalue may converge to zero; it is never replaced by 1. -/
theorem projected_gauge_lower (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (U V D A Q J : E →L[ℝ] E)
    (v : Fin p → E) (a K H : ℝ) (hK : 0≤K)
    (hdiag : D=V*A*U)
    (hU : ‖exterior p U‖≤K) (hV : ‖exterior p V‖≤K)
    (hJ : ‖exterior p J‖≤H)
    (heigen : exterior p D (exteriorPower.ιMulti ℝ p v)=
      a • exteriorPower.ιMulti ℝ p v)
    (hleft : ∀ i,J (Q (A (U (v i))))=A (U (v i)))
    (hrange : ∀ i j,j∉s → b.repr (Q (A (U (v i)))) j=0) :
    |a| *‖exterior p U (exteriorPower.ιMulti ℝ p v)‖≤
      K^2*H*|projectedMinor b p s (Q*A*U) v| := by
  have hbase := gauge_line_lower p U V A D hdiag hK hU hV
    (exteriorPower.ιMulti ℝ p v) heigen
  have heq : exterior p J (exterior p Q (exterior p A (exterior p U
      (exteriorPower.ιMulti ℝ p v))))=
      exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v)) := by
    simp only [exterior_apply,exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact hleft i
  have hj := (exterior p J).le_opNorm
    (exterior p Q (exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v))))
  rw [heq] at hj
  have hn : ‖exterior p Q (exterior p A (exterior p U
      (exteriorPower.ιMulti ℝ p v)))‖=|projectedMinor b p s (Q*A*U) v| := by
    simp only [exterior_apply,exteriorPower.map_apply_ιMulti]
    change ‖exteriorPower.ιMulti ℝ p (fun i => Q (A (U (v i))))‖=_
    rw [projected_wedge_norm b p s _ hrange]
    congr 1
    rw [projectedMinor_eq_det,projectedMinor_eq_det]
    rfl
  rw [hn] at hj
  calc
    _ ≤ K^2*‖exterior p A (exterior p U (exteriorPower.ιMulti ℝ p v))‖ := hbase
    _ ≤ K^2*(H*|projectedMinor b p s (Q*A*U) v|) := by
      gcongr
      exact hj.trans (mul_le_mul_of_nonneg_right hJ (abs_nonneg _))
    _ = _ := by ring
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Exact sum-rate lower bound for a genuine finite-gauge propagator followed
by an endpoint projection. The input is its actual fast determinant line;
the dimensional exterior bound is produced by `exists_power_bound`. -/
theorem finite_projected_volume
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hVU : ∀ t,V t*U t=1) (s t p : ℕ) (q : powersetCard (Fin d) p)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) p)
    (Q J : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) (hJ : ‖J‖≤2)
    (hleft : ∀ i,J (Q (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (transition U V lam s t*U s)
        (EuclideanSpace.basisFun (Fin d) ℝ (powersetCard.ofFinEmbEquiv.symm q i))))=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t*U s)
        (EuclideanSpace.basisFun (Fin d) ℝ (powersetCard.ofFinEmbEquiv.symm q i)))
    (hrange : ∀ i j,j∉r → b.repr (Q (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (transition U V lam s t*U s)
        (EuclideanSpace.basisFun (Fin d) ℝ (powersetCard.ofFinEmbEquiv.symm q i)))) j=0) :
    let v := fun i => EuclideanSpace.basisFun (Fin d) ℝ (powersetCard.ofFinEmbEquiv.symm q i)
    Real.exp (((t:ℝ)-s)*(∑ j∈q.val,lam j))*
      ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s)) (exteriorPower.ιMulti ℝ p v)‖≤
      (C*(Real.exp K)^p)^2*(C*2^p)*
        |projectedMinor b p r
          (Q*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t*U s)) v| := by
  dsimp only
  let b₀ := EuclideanSpace.basisFun (Fin d) ℝ
  let v := fun i => b₀ (powersetCard.ofFinEmbEquiv.symm q i)
  have hb : (b₀.exteriorPower p) q=exteriorPower.ιMulti ℝ p v := by
    change (b₀.exteriorPower p).toBasis q=_
    rw [b₀.toBasis_exteriorPower,exteriorPower.coe_basis]
    rfl
  have heigen := exterior_eigen_basis b₀ p
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
    (fun j => Real.exp (((t:ℝ)-s)*lam j)) (rate_eigen lam _) q
  rw [hb,eigen_exp_product,selected_sum] at heigen
  have hdiagM : rate lam ((t:ℝ)-s)=V t*transition U V lam s t*U s := by
    symm
    dsimp [transition]
    calc
      _ = (V t*U t)*rate lam ((t:ℝ)-s)*(V s*U s) := by noncomm_ring
      _ = _ := by rw [hVU,hVU,one_mul,mul_one]
  have hdiag : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s))=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) := by
    rw [←map_mul,←map_mul,←hdiagM]
  have hbnd (M : Matrix (Fin d) (Fin d) ℝ) (hM : ‖M‖≤Real.exp K) :
      ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M)‖≤C*(Real.exp K)^p := by
    apply (hpoly _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact max_le (Real.one_le_exp_iff.mpr hK) hM
  have hJb : ‖exterior p J‖≤C*2^p := (hpoly J).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le (by norm_num) hJ) p) hC)
  have hh := projected_gauge_lower b p r
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) Q J v
    _ (C*(Real.exp K)^p) (C*2^p) (by positivity) hdiag (hbnd (U s) hU)
    (hbnd (V t) hV) hJb heigen
    (by simpa only [map_mul,mul_apply_eq_comp] using hleft)
    (by simpa only [map_mul,mul_apply_eq_comp] using hrange)
  simpa only [abs_of_pos (Real.exp_pos _),map_mul,mul_assoc] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Extend the inverse endpoint restriction back to an ambient linear map.
It is a left inverse on the actual moving fast space, with uniform norm 2. -/
noncomputable def ambientInverse (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) : E →L[ℝ] E :=
  U.subtypeL.comp ((equiv U V hdim hclose).symm.toContinuousLinearMap.comp
    V.orthogonalProjectionOnto)

lemma ambientInverse_left (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) (x : E) (hx : x∈U) :
    ambientInverse U V hdim hclose (V.starProjection x)=x := by
  have hp : V.orthogonalProjectionOnto (V.starProjection x)=V.orthogonalProjectionOnto x := by
    apply Subtype.ext
    change V.starProjection (V.starProjection x)=V.starProjection x
    exact V.starProjection_eq_self_iff.mpr (by simp)
  change ((equiv U V hdim hclose).symm (V.orthogonalProjectionOnto (V.starProjection x)):E)=x
  rw [hp]
  change ((equiv U V hdim hclose).symm (equiv U V hdim hclose ⟨x,hx⟩):E)=x
  rw [ContinuousLinearEquiv.symm_apply_apply]

lemma norm_ambientInverse (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) :
    ‖ambientInverse U V hdim hclose‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(equiv U V hdim hclose).symm (V.orthogonalProjectionOnto x)‖≤2*‖x‖
  apply ((equiv U V hdim hclose).symm.toContinuousLinearMap.le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right (inverse_norm U V hdim hclose) (norm_nonneg _)).trans
  exact mul_le_mul_of_nonneg_left (V.norm_orthogonalProjectionOnto_apply_le x) (by norm_num)
end SmoothObstruction.CloseProjection

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma transition_group (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (lam : Fin d → ℝ) (s t : ℕ) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x∈groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x∈
      groupSpace (U t) (V t) (hUV t) (hVU t) S := by
  rcases Submodule.mem_map.mp hx with ⟨y,hy,rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)) y,?_,?_⟩
  · rw [mem_coordinateSpace] at hy ⊢
    intro j hj
    change (rate lam ((t:ℝ)-s)*ᵥ WithLp.ofLp y) j=0
    rw [rate,Matrix.mulVec_diagonal,hy j hj,mul_zero]
  · change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)) y)=
        Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
          (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) y)
    rw [←mul_apply_eq_comp,←mul_apply_eq_comp,←map_mul,←map_mul]
    congr 2
    dsimp [transition]
    rw [mul_assoc _ _ (U s),hVU,mul_one]

lemma gauge_column_mem (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) (j : Fin d) (hj : j∈S) :
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U (EuclideanSpace.basisFun (Fin d) ℝ j)∈
      groupSpace U V hUV hVU S := by
  apply Submodule.mem_map.mpr
  refine ⟨EuclideanSpace.basisFun (Fin d) ℝ j,?_,rfl⟩
  rw [mem_coordinateSpace]
  intro i hi
  have hij : i≠j := by rintro rfl; exact hi hj
  simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_eq_right hij]

/-- A true old fast leading minor, with the endpoint left inverse BUILT
from the common-bin projection closeness, rather than assumed. The estimate
retains exp(sum rates * length) even for contracting determinant lines. -/
theorem projected_fast_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (s t p : ℕ) (q : powersetCard (Fin d) p)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=p)
    (hclose : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) q.val).starProjection-W.starProjection‖≤1/2)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) p)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    let v := fun i => EuclideanSpace.basisFun (Fin d) ℝ (powersetCard.ofFinEmbEquiv.symm q i)
    Real.exp (((t:ℝ)-s)*(∑ j∈q.val,lam j))*
      ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s)) (exteriorPower.ιMulti ℝ p v)‖≤
      (C*(Real.exp K)^p)^2*(C*2^p)*
        |projectedMinor b p r
          (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t*U s)) v| := by
  let F := groupSpace (U t) (V t) (hUV t) (hVU t) q.val
  have hd : Module.finrank ℝ F=Module.finrank ℝ W := by
    rw [finrank_groupSpace,hdim,q.prop]
  apply finite_projected_volume U V lam hVU s t p q b r W.starProjection
    (CloseProjection.ambientInverse F W hd hclose) hK hC hpoly hU hV
    (CloseProjection.norm_ambientInverse F W hd hclose)
  · intro i
    apply CloseProjection.ambientInverse_left
    rw [map_mul,mul_apply_eq_comp]
    apply transition_group U V hUV hVU lam s t q.val
    apply gauge_column_mem
    rw [powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro i j hj
    apply hcoords _ (by simp) j hj
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The empty as well as every orthonormal determinant line has unit volume. -/
lemma norm_wedge_orthonormal (p : ℕ) (v : Fin p → E) (hv : Orthonormal ℝ v) :
    ‖exteriorPower.ιMulti ℝ p v‖=1 := by
  have hg : Matrix.gram ℝ v=1 := by
    ext i j
    exact (orthonormal_iff_ite.mp hv) i j
  have hh := exteriorPower.inner_ιMulti_self v
  rw [hg,Matrix.det_one,real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ p v)]
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma rate_coordinate_wedge (lam : Fin d → ℝ) (l : ℝ) (p : ℕ)
    (q : powersetCard (Fin d) p) (v : Fin p → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i,v i∈coordinateSpace q.val) :
    exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
      (exteriorPower.ιMulti ℝ p v)=
      Real.exp (l*(∑ j∈q.val,lam j)) • exteriorPower.ιMulti ℝ p v := by
  let b₀ := EuclideanSpace.basisFun (Fin d) ℝ
  have hc : ∀ i j,j∉q → b₀.repr (v i) j=0 := by
    intro i j hj
    exact (mem_coordinateSpace q.val (v i)).mp (hv i) j hj
  have he := exterior_eigen_basis b₀ p
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
    (fun j => Real.exp (l*lam j)) (rate_eigen lam l) q
  rw [eigen_exp_product,selected_sum] at he
  rw [projected_wedge_line b₀ p q v hc,map_smul,he]
  exact smul_comm _ _ _

/-- Leading fast minor in an ACTUAL orthonormal starting frame. The input
columns are not the Lyapunov gauge columns. This yields a relative lower
bound at the true sum-exponent scale, whether it expands or contracts. -/
theorem orthonormal_fast_minor_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (s t p : ℕ) (q : powersetCard (Fin d) p)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=p)
    (hclose : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) q.val).starProjection-W.starProjection‖≤1/2)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) p)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (w : Fin p → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ w)
    (hw : ∀ i,w i∈groupSpace (U s) (V s) (hUV s) (hVU s) q.val)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    Real.exp (((t:ℝ)-s)*(∑ j∈q.val,lam j))≤
      (C*(Real.exp K)^p)^2*(C*2^p)*
        |projectedMinor b p r
          (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w| := by
  let v := fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s) (w i)
  have hv : ∀ i,v i∈coordinateSpace q.val := by
    intro i
    have h := hw i
    rw [groupSpace,Submodule.map_equiv_eq_comap_symm] at h
    exact h
  have huv : ∀ i,Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) (v i)=w i := by
    intro i
    dsimp [v]
    rw [←mul_apply_eq_comp,←map_mul,hUV,map_one]
    rfl
  let F := groupSpace (U t) (V t) (hUV t) (hVU t) q.val
  have hd : Module.finrank ℝ F=Module.finrank ℝ W := by
    rw [finrank_groupSpace,hdim,q.prop]
  let J := CloseProjection.ambientInverse F W hd hclose
  have hdiagM : rate lam ((t:ℝ)-s)=V t*transition U V lam s t*U s := by
    symm
    dsimp [transition]
    calc
      _ = (V t*U t)*rate lam ((t:ℝ)-s)*(V s*U s) := by noncomm_ring
      _ = _ := by rw [hVU,hVU,one_mul,mul_one]
  have hdiag : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s))=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) := by
    rw [←map_mul,←map_mul,←hdiagM]
  have hbnd (M : Matrix (Fin d) (Fin d) ℝ) (hM : ‖M‖≤Real.exp K) :
      ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M)‖≤C*(Real.exp K)^p := by
    apply (hpoly _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact max_le (Real.one_le_exp_iff.mpr hK) hM
  have hJb : ‖exterior p J‖≤C*2^p := (hpoly J).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (max_le (by norm_num) (CloseProjection.norm_ambientInverse F W hd hclose)) p) hC)
  have hh := projected_gauge_lower b p r
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V t))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) W.starProjection J v
    _ (C*(Real.exp K)^p) (C*2^p) (by positivity) hdiag (hbnd (U s) hU)
    (hbnd (V t) hV) hJb (rate_coordinate_wedge lam _ p q v hv)
    (by
      intro i
      rw [huv]
      exact CloseProjection.ambientInverse_left F W hd hclose _
        (transition_group U V hUV hVU lam s t q.val _ (hw i)))
    (by intro i j hj; exact hcoords _ (by simp) j hj)
  have hn : ‖exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s))
      (exteriorPower.ιMulti ℝ p v)‖=1 := by
    rw [exterior_apply,exteriorPower.map_apply_ιMulti]
    change ‖exteriorPower.ιMulti ℝ p (fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) (v i))‖=1
    simp_rw [huv]
    exact norm_wedge_orthonormal p w horth
  have hm : projectedMinor b p r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
        Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s)) v=
      projectedMinor b p r
        (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w := by
    rw [projectedMinor_eq_det,projectedMinor_eq_det]
    simp only [mul_apply_eq_comp,huv]
  simpa only [abs_of_pos (Real.exp_pos _),hn,mul_one,hm] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- A diagonal map on the orthogonal complement of one determinant line. -/
lemma diagonal_missing_line_bound (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (a : ι → ℝ) (ha : ∀ i,T (b i)=a i • b i)
    (i₀ : ι) (x : E) (hx : b.repr x i₀=0)
    {K : ℝ} (hK : 0≤K) (hbound : ∀ i,i≠i₀ → |a i|≤K) :
    ‖T x‖≤(Fintype.card ι:ℝ)*K*‖x‖ := by
  classical
  have hrepr : x=∑ i,(b.repr x i) • b i := (b.sum_repr x).symm
  calc
    ‖T x‖=‖∑ i,(b.repr x i) • T (b i)‖ := by
      conv_lhs => rw [hrepr]
      simp only [map_sum,map_smul]
    _ ≤ ∑ i,‖(b.repr x i) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι,K*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i=i₀
      · subst i
        simp only [hx,zero_smul,norm_zero]
        positivity
      · rw [ha,norm_smul,norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs,Real.norm_eq_abs]
        have hc : |b.repr x i|≤‖x‖ := by
          rw [b.repr_apply_apply,←Real.norm_eq_abs]
          simpa only [b.norm_eq_one,one_mul] using norm_inner_le_norm (𝕜:=ℝ) (b i) x
        calc
          _ ≤ ‖x‖*K := mul_le_mul hc (hbound i hi) (abs_nonneg _) (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma coordinate_wedge_missing_fast (S : Finset (Fin d))
    (v : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hslow : v i₀∈coordinateSpace Sᶜ) :
    ((EuclideanSpace.basisFun (Fin d) ℝ).exteriorPower S.card).repr
      (exteriorPower.ιMulti ℝ S.card v) (⟨S,rfl⟩ : powersetCard (Fin d) S.card)=0 := by
  let b₀ := EuclideanSpace.basisFun (Fin d) ℝ
  have he : projectedMinor b₀ S.card ⟨S,rfl⟩ (ContinuousLinearMap.id ℝ _) v=0 := by
    rw [projectedMinor_eq_det]
    apply Matrix.det_eq_zero_of_row_eq_zero i₀
    intro j
    apply (mem_coordinateSpace Sᶜ _).mp hslow
    simp only [Finset.mem_compl,not_not]
    rw [powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_mem _ _ _
  change (b₀.exteriorPower S.card).repr (exterior S.card 1 (exteriorPower.ιMulti ℝ S.card v)) ⟨S,rfl⟩=0 at he
  rw [exterior_one] at he
  exact he

/-- True nonleading volume suppression for the diagonal propagator, applied
to arbitrary vectors including one slow vector, not merely coordinate
columns. The loss is the exact spectral gap exp(-2g length). -/
lemma rate_nonleading_volume (lam : Fin d → ℝ) (S : Finset (Fin d))
    {γ g l : ℝ} (hg : 0≤g) (hl : 0≤l)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hv : v i₀∈coordinateSpace Sᶜ) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam l))
      (exteriorPower.ιMulti ℝ S.card v)‖≤
      (Fintype.card (powersetCard (Fin d) S.card):ℝ)*
        Real.exp (l*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card v‖ := by
  apply diagonal_missing_line_bound
    ((EuclideanSpace.basisFun (Fin d) ℝ).exteriorPower S.card) _
    (fun q => ∏ i : Fin S.card,Real.exp (l*lam (powersetCard.ofFinEmbEquiv.symm q i)))
    (exterior_eigen_basis _ _ _ _ (rate_eigen lam l)) ⟨S,rfl⟩ _
    (coordinate_wedge_missing_fast S v i₀ hv) (Real.exp_nonneg _)
  intro q hq
  apply nonleading_rate_product lam S hg hl hfast hslow q
  intro he
  exact hq (Subtype.ext he)

/-- The actual finite-gauge transition suppresses every maximal starting
wedge containing a slow vector relative to its true fast sum-rate. -/
theorem transition_nonleading_volume
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d))
    (i₀ : Fin S.card) (hw : w i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
      (exteriorPower.ιMulti ℝ S.card w)‖≤
      (C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card w‖ := by
  let v := fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s) (w i)
  have hv : v i₀∈coordinateSpace Sᶜ := by
    rw [groupSpace,Submodule.map_equiv_eq_comap_symm] at hw
    exact hw
  have he := rate_nonleading_volume lam S hg
    (sub_nonneg.mpr (by exact_mod_cast hst) : 0≤(t:ℝ)-s) hfast hslow v i₀ hv
  have hbnd (M : Matrix (Fin d) (Fin d) ℝ) (hM : ‖M‖≤Real.exp K) :
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M)‖≤C*(Real.exp K)^S.card := by
    apply (hpoly _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact max_le (Real.one_le_exp_iff.mpr hK) hM
  have hwedge : exteriorPower.ιMulti ℝ S.card v=
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))
        (exteriorPower.ιMulti ℝ S.card w) := by
    rw [exterior_apply,exteriorPower.map_apply_ιMulti]
    rfl
  have hvb : ‖exteriorPower.ιMulti ℝ S.card v‖≤
      (C*(Real.exp K)^S.card)*‖exteriorPower.ιMulti ℝ S.card w‖ := by
    rw [hwedge]
    exact ((exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (V s))).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbnd (V s) hV) (norm_nonneg _))
  have htransition : exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
      (exteriorPower.ιMulti ℝ S.card w)=
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))
        (exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
          (exteriorPower.ιMulti ℝ S.card v)) := by
    rw [hwedge]
    simp only [transition,map_mul,exterior_mul,mul_apply_eq_comp]
  rw [htransition]
  calc
    _ ≤ ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U t))‖*
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (rate lam ((t:ℝ)-s)))
        (exteriorPower.ιMulti ℝ S.card v)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C*(Real.exp K)^S.card)*((Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card v‖) := by
      exact mul_le_mul (hbnd (U t) hU) he (norm_nonneg _) (by positivity)
    _ ≤ (C*(Real.exp K)^S.card)*((Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ((C*(Real.exp K)^S.card)*‖exteriorPower.ιMulti ℝ S.card w‖)) := by
      gcongr
    _ = _ := by ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuity is proved from the actual determinant polynomial. -/
noncomputable def continuousWedge (p : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p => E) (⋀[ℝ]^p E) where
  toMultilinearMap := (exteriorPower.ιMulti ℝ p).toMultilinearMap
  cont := (contDiff_wedge p).continuous

lemma unit_wedge_bound (p : ℕ) (v : Fin p → E) (hv : ∀ i,‖v i‖≤1) :
    ‖exteriorPower.ιMulti ℝ p v‖≤‖continuousWedge (E:=E) p‖ := by
  have hh := (continuousWedge (E:=E) p).le_opNorm v
  apply hh.trans
  have hp : (∏ i,‖v i‖)≤1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun index _ => hv index)
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
lemma projectedMinor_norm_le (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    |projectedMinor b p r A v|≤‖exterior p A (exteriorPower.ιMulti ℝ p v)‖ := by
  rw [projectedMinor,(b.exteriorPower p).repr_apply_apply,←Real.norm_eq_abs]
  simpa only [(b.exteriorPower p).norm_eq_one,one_mul] using
    norm_inner_le_norm (𝕜:=ℝ) ((b.exteriorPower p) r) _
end SmoothObstruction.ExteriorStability

end

end OAI
