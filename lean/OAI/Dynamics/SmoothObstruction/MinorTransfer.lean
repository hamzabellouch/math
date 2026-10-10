import OAI.Dynamics.SmoothObstruction.SplittingStability

namespace OAI

section

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Actual endpoint-projected nonleading maximal minors on unit starting
columns. The inter-group conditioning is paid only by the finite gauge. -/
theorem projected_nonleading_minor
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (i₀ : Fin S.card) (hw : w i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    |projectedMinor b S.card r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w|≤
      C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖ := by
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have htr := transition_nonleading_volume U V lam hUV hVU S hst hg hK hC
    hfast hslow hU hV hpoly w i₀ hw
  apply (projectedMinor_norm_le b S.card r _ w).trans
  rw [exterior_mul,mul_apply_eq_comp]
  calc
    _ ≤ ‖exterior S.card W.starProjection‖*
      ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))
        (exteriorPower.ιMulti ℝ S.card w)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*((C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*‖exteriorPower.ιMulti ℝ S.card w‖) :=
      mul_le_mul hQ htr (norm_nonneg _) hC
    _ ≤ C*((C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))*
        ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖) := by
      gcongr
      exact unit_wedge_bound S.card w hnorm
    _ = _ := by ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Actual fast determinant-line bound for arbitrary starting vectors in
the fast group. This permits projection of a common orthonormal frame onto
the actual group without a polar-decomposition choice of bases. -/
theorem fast_minor_volume_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (s t p : ℕ) (q : powersetCard (Fin d) p)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=p)
    (hclose : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) q.val).starProjection-W.starProjection‖≤1/2)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) p)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (w : Fin p → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i,w i∈groupSpace (U s) (V s) (hUV s) (hVU s) q.val)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    Real.exp (((t:ℝ)-s)*(∑ j∈q.val,lam j))*‖exteriorPower.ιMulti ℝ p w‖≤
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
      (exteriorPower.ιMulti ℝ p v)‖=‖exteriorPower.ιMulti ℝ p w‖ := by
    rw [exterior_apply,exteriorPower.map_apply_ιMulti]
    change ‖exteriorPower.ιMulti ℝ p (fun i => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s) (v i))‖=‖exteriorPower.ιMulti ℝ p w‖
    simp_rw [huv]

  have hm : projectedMinor b p r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
        Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U s)) v=
      projectedMinor b p r
        (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w := by
    rw [projectedMinor_eq_det,projectedMinor_eq_det]
    simp only [mul_apply_eq_comp,huv]
  simpa only [abs_of_pos (Real.exp_pos _),hn,hm] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma projected_frame_distance (p : ℕ) (F G : Submodule ℝ E)
    (w : Fin p → E) (hw : ∀ i,w i∈G) (hnorm : ∀ i,‖w i‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ‖F.starProjection-G.starProjection‖≤δ) :
    ‖(fun i => F.starProjection (w i))-w‖≤δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  have he : F.starProjection (w i)-w i=(F.starProjection-G.starProjection) (w i) := by
    rw [_root_.sub_apply,G.starProjection_eq_self_iff.mpr (hw i)]
  change ‖F.starProjection (w i)-w i‖≤δ
  rw [he]
  exact ((F.starProjection-G.starProjection).le_opNorm (w i)).trans
    ((mul_le_mul hclose (hnorm i) (norm_nonneg _) hδ).trans_eq (mul_one _))

/-- One dimension-dependent uniform constant controls projected common
frames. This bypasses choosing a continuously varying orthonormal basis:
project the reference columns and use their determinant volume directly. -/
theorem exists_common_frame_wedge_control (p : ℕ) :
    ∃ L : ℝ,1≤L ∧ ∀ (F G : Submodule ℝ E) (w : Fin p → E)
      (δ : ℝ), (∀ i,w i∈G) → (∀ i,‖w i‖≤1) → 0≤δ →
      ‖F.starProjection-G.starProjection‖≤δ →
      ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
        exteriorPower.ιMulti ℝ p w‖≤L*δ := by
  obtain ⟨L,hL,hbound⟩ := exists_wedge_lipschitz (E:=E) p 1
  refine ⟨max L 1,le_max_right _ _,?_⟩
  intro F G w δ hw hnorm hδ hclose
  have hp : ‖fun i => F.starProjection (w i)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    exact (F.norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hw' : ‖w‖≤1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hnorm
  exact (hbound _ w hp hw').trans
    (mul_le_mul (le_max_left _ _) (projected_frame_distance p F G w hw hnorm hδ hclose)
      (norm_nonneg _) (le_trans hL (le_max_left _ _)))

lemma projected_orthonormal_volume_lower (p : ℕ) (F : Submodule ℝ E)
    (w : Fin p → E) (horth : Orthonormal ℝ w) {ε : ℝ}
    (herror : ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤ε) :
    1-ε≤‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))‖ := by
  have ht := norm_sub_norm_le (exteriorPower.ιMulti ℝ p w)
    (exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i)))
  rw [norm_sub_rev,norm_wedge_orthonormal p w horth] at ht
  linarith

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
/-- Column replacement is paid against the TRUE exterior norm of the old
propagator, hence it is valid even if the determinant line contracts. -/
lemma projectedMinor_column_error (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v w : Fin p → E)
    {ε : ℝ} (hε : ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤ε) :
    |projectedMinor b p r A v-projectedMinor b p r A w|≤‖exterior p A‖*ε := by
  have hh := projectedMinor_basis_transfer b p r A A w v
  simp only [sub_self,ContinuousLinearMap.opNorm_zero,zero_mul,zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hε (ContinuousLinearMap.opNorm_nonneg _))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Actual old endpoint minors have the relative fast/slow separation needed
for switching. Neither leading lower bounds nor suppressed minor bounds are
hypotheses: both are derived from the finite gauge and endpoint geometry. -/
theorem old_fast_minor_separation
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hclose : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈groupSpace (U s) (V s) (hUV s) (hVU s) S)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (i₀ : Fin S.card) (hw : w i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A v≠0 ∧
      |projectedMinor b S.card r A w|≤
        N₀*L₀*Real.exp (-2*g*((t:ℝ)-s))*|projectedMinor b S.card r A v| := by
  dsimp only
  have hl := orthonormal_fast_minor_lower U V lam hUV hVU s t S.card ⟨S,rfl⟩
    W hdim hclose b r hcoords v horth hv hK hC hpoly hUs hVt
  have hu := projected_nonleading_minor U V lam hUV hVU S hst hg hK hC hfast hslow
    hUt hVs hpoly W b r w hnorm i₀ hw
  refine ⟨?_,?_⟩
  · intro hh
    rw [hh,abs_zero,mul_zero] at hl
    exact (not_le_of_gt (Real.exp_pos _)) hl
  · have he : Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))=
        Real.exp (-2*g*((t:ℝ)-s))*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he] at hu
    let B : ℝ := C*(C*(Real.exp K)^S.card)^2*
      (Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖*Real.exp (-2*g*((t:ℝ)-s))
    have hB : 0≤B := by dsimp [B]; positivity
    have hh := mul_le_mul_of_nonneg_left hl hB
    dsimp [B] at hh
    nlinarith [hu]
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def frameWedgeConstant (p : ℕ) : ℝ :=
  (exists_common_frame_wedge_control (E:=E) p).choose

lemma one_le_frameWedgeConstant (p : ℕ) : 1≤frameWedgeConstant (E:=E) p :=
  (exists_common_frame_wedge_control (E:=E) p).choose_spec.1

lemma frameWedgeConstant_bound (p : ℕ) (F G : Submodule ℝ E)
    (w : Fin p → E) (δ : ℝ) (hw : ∀ i,w i∈G) (hnorm : ∀ i,‖w i‖≤1)
    (hδ : 0≤δ) (hclose : ‖F.starProjection-G.starProjection‖≤δ) :
    ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤frameWedgeConstant (E:=E) p*δ :=
  (exists_common_frame_wedge_control (E:=E) p).choose_spec.2 F G w δ hw hnorm hδ hclose
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- A common-bin orthonormal reference frame has a nonzero leading minor
at the TRUE sum-rate scale. The proof projects its columns onto the actual
fast space and estimates their wedge; it requires no continuous choice of
Lyapunov bases or unproved orthonormal basis alignment. -/
theorem common_fast_minor_lower
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ w)
    (hw : ∀ i,w i∈G)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))/2≤
      ((C*(Real.exp K)^S.card)^2*(C*2^S.card))*|projectedMinor b S.card r A w| ∧
      projectedMinor b S.card r A w≠0 := by
  let F := groupSpace (U s) (V s) (hUV s) (hVU s) S
  let u := fun i => F.starProjection (w i)
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let ε := frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  have hR : 0<R := Real.exp_pos _
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hN₀ : 0≤N₀ := by dsimp [N₀]; positivity
  have hε : 0≤ε := mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (one_le_frameWedgeConstant _)) hδ
  have he := frameWedgeConstant_bound S.card F G w δ hw (fun i => (horth.norm_eq_one i).le) hδ hstart
  have hv := projected_orthonormal_volume_lower S.card F w horth he
  have hl := fast_minor_volume_lower U V lam hUV hVU s t S.card ⟨S,rfl⟩ W hdim hend b r hcoords
    u (fun _ => by simp [u,F]) hK hC hpoly hUs hVt
  have htr := transition_exterior_bound U V lam S hst hg hK hC hfast hslow hUt hVs hpoly
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hA : ‖exterior S.card A‖≤N₀*R := by
    dsimp only [A]
    rw [exterior_mul]
    calc
      _ ≤ ‖exterior S.card W.starProjection‖*
          ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*R) :=
        mul_le_mul hQ htr (ContinuousLinearMap.opNorm_nonneg _) hC
      _ = N₀*R := by dsimp only [N₀]; ring
  have hm : |projectedMinor b S.card r A u-projectedMinor b S.card r A w|≤N₀*R*ε :=
    (projectedMinor_column_error b S.card r A u w he).trans
      (mul_le_mul_of_nonneg_right hA hε)
  have ht : |projectedMinor b S.card r A u|≤|projectedMinor b S.card r A w|+N₀*R*ε := by
    have hh := abs_sub_le (projectedMinor b S.card r A u) (projectedMinor b S.card r A w) 0
    simp only [sub_zero] at hh
    linarith
  have hcalc : R/2≤L₀*|projectedMinor b S.card r A w| := by
    have h1 := mul_le_mul_of_nonneg_left hv hR.le
    have h2 := mul_le_mul_of_nonneg_left ht hL₀
    have h3 := mul_le_mul_of_nonneg_left hsmall hR.le
    change R*‖exteriorPower.ιMulti ℝ S.card u‖≤L₀*|projectedMinor b S.card r A u| at hl
    change R*(1-ε)≤R*‖exteriorPower.ιMulti ℝ S.card u‖ at h1
    change R*(ε*(1+L₀*N₀))≤R*(1/2) at h3
    nlinarith
  refine ⟨hcalc,?_⟩
  intro hz
  change projectedMinor b S.card r A w=0 at hz
  rw [hz,abs_zero,mul_zero] at hcalc
  linarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def unitWedgeConstant (p : ℕ) : ℝ :=
  max (exists_wedge_lipschitz (E:=E) p 1).choose 1

lemma one_le_unitWedgeConstant (p : ℕ) : 1≤unitWedgeConstant (E:=E) p := le_max_right _ _

lemma unit_wedge_difference (p : ℕ) (v w : Fin p → E)
    (hv : ∀ i,‖v i‖≤1) (hw : ∀ i,‖w i‖≤1) :
    ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤unitWedgeConstant (E:=E) p*‖v-w‖ := by
  have hbound := (exists_wedge_lipschitz (E:=E) p 1).choose_spec.2
  apply (hbound v w ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hv)
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hw)).trans
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- The common product frame may mix both groups. Each column is projected
onto its OWN actual group; one uniform wedge constant still suffices. -/
lemma mixed_projected_wedge_difference (p : ℕ) (F G : Fin p → Submodule ℝ E)
    (w : Fin p → E) (hw : ∀ i,w i∈G i) (hnorm : ∀ i,‖w i‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ∀ i,‖(F i).starProjection-(G i).starProjection‖≤δ) :
    ‖exteriorPower.ιMulti ℝ p (fun i => (F i).starProjection (w i))-
      exteriorPower.ιMulti ℝ p w‖≤unitWedgeConstant (E:=E) p*δ := by
  have hp : ∀ i,‖(F i).starProjection (w i)‖≤1 :=
    fun i => ((F i).norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hd : ‖(fun i => (F i).starProjection (w i))-w‖≤δ := by
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro i
    have he : (F i).starProjection (w i)-w i=
        ((F i).starProjection-(G i).starProjection) (w i) := by
      rw [_root_.sub_apply,(G i).starProjection_eq_self_iff.mpr (hw i)]
    change ‖(F i).starProjection (w i)-w i‖≤δ
    rw [he]
    exact (((F i).starProjection-(G i).starProjection).le_opNorm (w i)).trans
      ((mul_le_mul (hclose i) (hnorm i) (norm_nonneg _) hδ).trans_eq (mul_one _))
  exact (unit_wedge_difference p _ w hp hnorm).trans
    (mul_le_mul_of_nonneg_left hd ((by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant p)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Every nonleading minor in the common starting product frame has the
true relative gap term plus a controlled common-subspace replacement term.
No determinant-line rate is assumed nonnegative. -/
theorem common_nonleading_minor
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUt : ‖U t‖≤Real.exp K) (hVs : ‖V s‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (F G : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(G i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈G i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ) :
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    |projectedMinor b S.card r
      (W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)) w|≤
      (N₁*Real.exp (-2*g*((t:ℝ)-s))+
        N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
        Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j)) := by
  let u := fun i => (F i).starProjection (w i)
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  have hε : 0≤ε := mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant _)) hδ
  have hu : ∀ i,‖u i‖≤1 := fun i => ((F i).norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hus : u i₀∈groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ := by
    dsimp [u]
    rw [←hFi]
    simp
  have he := mixed_projected_wedge_difference S.card F G w hw hnorm hδ hclose
  have hold := projected_nonleading_minor U V lam hUV hVU S hst hg hK hC hfast hslow
    hUt hVs hpoly W b r u hu i₀ hus
  have htr := transition_exterior_bound U V lam S hst hg hK hC hfast hslow hUt hVs hpoly
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hA : ‖exterior S.card A‖≤N₀*R := by
    dsimp only [A]
    rw [exterior_mul]
    calc
      _ ≤ ‖exterior S.card W.starProjection‖*
          ‖exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*R) :=
        mul_le_mul hQ htr (ContinuousLinearMap.opNorm_nonneg _) hC
      _ = N₀*R := by dsimp only [N₀]; ring
  have hm : |projectedMinor b S.card r A u-projectedMinor b S.card r A w|≤N₀*R*ε :=
    (projectedMinor_column_error b S.card r A u w he).trans
      (mul_le_mul_of_nonneg_right hA hε)
  have hs : Real.exp (((t:ℝ)-s)*((∑ j∈S,lam j)-2*g))=
      Real.exp (-2*g*((t:ℝ)-s))*R := by
    dsimp [R]
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hs] at hold
  have ht := abs_sub_le (projectedMinor b S.card r A w) (projectedMinor b S.card r A u) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm] at hm
  change |projectedMinor b S.card r A w|≤
    (N₁*Real.exp (-2*g*((t:ℝ)-s))+N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*R
  change |projectedMinor b S.card r A u|≤
    C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      (Real.exp (-2*g*((t:ℝ)-s))*R)*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖ at hold
  dsimp only [N₁,ε] at *
  nlinarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Genuine common-frame minors: the old leading minor is nonzero and every
mixed minor has a relative bound obtained from the actual gauge products.
All smallness requirements refer to subspace distances, not to conclusions
about minors. Rates may be negative and no uniform determinant floor is used. -/
theorem common_minor_separation
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (F H : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(H i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈H i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A v≠0 ∧
      |projectedMinor b S.card r A w|≤
        (2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
          N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ))*
            |projectedMinor b S.card r A v| := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  have hu := common_nonleading_minor U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUt hVs hpoly W b r F H hclose w hnorm hw i₀ hFi
  refine ⟨hl.2,?_⟩
  dsimp only at hl hu ⊢
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
  let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let D := N₁*Real.exp (-2*g*((t:ℝ)-s))+
    N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ
  have hD : 0≤D := by
    have hp := (one_le_unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card)
    dsimp [D,N₀,N₁]
    positivity
  have hh := mul_le_mul_of_nonneg_left hl.1
    (show 0≤2*D from mul_nonneg (by norm_num) hD)
  dsimp [D,N₀,N₁] at hh
  nlinarith
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Filter Topology Set Asymptotics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Relative transfer of the actual signed projected minor, even when its
leading determinant tends to zero. The bound is against the OLD leading
minor, and hence does not accidentally divide by a perturbed or vanishing
quantity. -/
theorem relative_projected_minor (p : ℕ) (b : ℕ → OrthonormalBasis ι ℝ E)
    (s : ℕ → powersetCard ι p) (A B : ℕ → E →L[ℝ] E)
    (v : ℕ → Fin p → E) (r L : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ᶠ k in atTop, ‖exteriorPower.ιMulti ℝ p (v k)‖ ≤ W)
    (hL : ∀ᶠ k in atTop, |r k| ≤ |L k|)
    (he : (fun k => exterior p (B k)-exterior p (A k)) =o[atTop] r) :
    (fun k => projectedMinor (b k) p (s k) (B k) (v k)-
      projectedMinor (b k) p (s k) (A k) (v k)) =o[atTop] L := by
  rw [isLittleO_iff] at he ⊢
  intro ε hε
  filter_upwards [he (div_pos hε (by positivity : 0 < W+1)),hw,hL] with k hk hkw hkL
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖exterior p (B k)-exterior p (A k)‖*W :=
      (projectedMinor_transfer (b k) p (s k) (A k) (B k) (v k)).trans
        (mul_le_mul_of_nonneg_left hkw (norm_nonneg (exterior p (B k)-exterior p (A k))))
    _ ≤ (ε/(W+1)*‖r k‖)*W := mul_le_mul_of_nonneg_right hk hW
    _ ≤ ε*‖L k‖ := by
      rw [Real.norm_eq_abs,Real.norm_eq_abs]
      have hd : ε/(W+1) ≥ 0 := (div_pos hε (by positivity)).le
      have heq : ε/(W+1)*(W+1)=ε := div_mul_cancel₀ _ (by positivity)
      have hb := mul_le_mul_of_nonneg_left hkL (mul_nonneg hd hW)
      nlinarith [abs_nonneg (L k)]

/-- Relative errors preserve nonzero leading minors and all other ratios.
There is no lower absolute bound on `a`. -/
lemma relative_minor_ratios {a a' c c' ε δ : ℝ} (ha : a ≠ 0)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ)
    (haa : |a'-a| ≤ ε*|a|) (hc : |c| ≤ δ*|a|)
    (hcc : |c'-c| ≤ ε*|a|) :
    a' ≠ 0 ∧ |c'|/|a'| ≤ (δ+ε)/(1-ε) := by
  have hapos := abs_pos.mpr ha
  have hal : (1-ε)*|a| ≤ |a'| := by
    have ht := abs_sub_abs_le_abs_sub a a'
    rw [abs_sub_comm a a'] at ht
    nlinarith
  have hap : 0 < |a'| := lt_of_lt_of_le (mul_pos (by linarith) hapos) hal
  refine ⟨abs_pos.mp hap, (div_le_iff₀ hap).mpr ?_⟩
  have hcup : |c'| ≤ (δ+ε)*|a| := by
    have ht := abs_sub_le c' c 0
    simp only [sub_zero] at ht
    linarith
  apply hcup.trans
  have hd : 0 ≤ (δ+ε)/(1-ε) := div_nonneg (add_nonneg hδ hε) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hal hd
  have he : (δ+ε)/(1-ε)*((1-ε)*|a|)=(δ+ε)*|a| := by
    rw [←mul_assoc,div_mul_cancel₀ _ (by linarith : 1-ε ≠ 0)]
  rwa [he] at hh
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Fixed endpoint projections preserve the all-subinterval exterior error.
The multiplier is a dimension constant even for a nonpositive rate sum. -/
lemma projected_postcomposition_transfer (b : OrthonormalBasis ι ℝ E)
    (p : ℕ) (r : powersetCard ι p) (Q A B : E →L[ℝ] E)
    (v : Fin p → E) (hv : ∀ i,‖v i‖≤1) {C ε : ℝ} (hC : 0≤C)
    (hQ : ‖exterior p Q‖≤C) (he : ‖exterior p B-exterior p A‖≤ε) :
    |projectedMinor b p r (Q*B) v-projectedMinor b p r (Q*A) v|≤
      C*ε*‖continuousWedge (E:=E) p‖ := by
  have hd : exterior p (Q*B)-exterior p (Q*A)=
      exterior p Q*(exterior p B-exterior p A) := by
    rw [exterior_mul,exterior_mul,mul_sub]
  have hn : ‖exterior p (Q*B)-exterior p (Q*A)‖≤C*ε := by
    rw [hd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hQ he (ContinuousLinearMap.opNorm_nonneg _) hC)
  exact (projectedMinor_transfer b p r (Q*A) (Q*B) v).trans
    (mul_le_mul hn (unit_wedge_bound p v hv) (norm_nonneg _)
      (mul_nonneg hC ((ContinuousLinearMap.opNorm_nonneg _).trans he)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Finite, quantitative relative-minor control for a perturbed derivative in
common starting/endpoint frames. Old minor bounds are DERIVED from actual
finite gauges and close subspaces. The exterior perturbation is measured at
the true sum-rate scale, not at an absolute determinant floor. -/
theorem common_minor_perturbation
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (F H : Fin S.card → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hclose : ∀ i,‖(F i).starProjection-(H i).starProjection‖≤δ)
    (w : Fin S.card → EuclideanSpace ℝ (Fin d)) (hnorm : ∀ i,‖w i‖≤1)
    (hw : ∀ i,w i∈H i) (i₀ : Fin S.card)
    (hFi : F i₀=groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A' := W.starProjection*B
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
      N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A' v≠0 ∧
      |projectedMinor b S.card r A' w|/|projectedMinor b S.card r A' v|≤(θ+ε)/(1-ε) := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  have hs := common_minor_separation U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv
    F H hclose w hnorm hw i₀ hFi hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*A₀
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r A v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r A v| := hl.1
    linarith
  have he (u : Fin S.card → EuclideanSpace ℝ (Fin d)) (hu : ∀ i,‖u i‖≤1) :
      |projectedMinor b S.card r (W.starProjection*B) u-projectedMinor b S.card r A u|≤
        ε*|projectedMinor b S.card r A v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B u hu hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r A v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r A v| := by dsimp [ε]; ring
  apply relative_minor_ratios hs.1 hε hpert _
    (he v (fun i => (horth.norm_eq_one i).le)) hs.2 (he w hnorm)
  have hp := one_le_unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card
  positivity
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ExteriorStability
open Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Actual endpoint-coordinate matrix; columns are the represented starting
vectors. Unlike the exterior-coordinate scalar formula, this uses the usual
matrix convention (output row, input column). -/
noncomputable def endpointMatrix (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) {n : ℕ} (v : Fin n → E) :
    Matrix (Fin p) (Fin n) ℝ :=
  fun i j => b.repr (A (v j)) (powersetCard.ofFinEmbEquiv.symm r i)

lemma endpointMatrix_det (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) :
    (endpointMatrix b p r A v).det=projectedMinor b p r A v := by
  rw [projectedMinor_eq_det]
  exact (Matrix.det_transpose _).symm

omit [FiniteDimensional ℝ E] in
lemma endpointMatrix_update (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E)
    (i : Fin p) (z : E) :
    endpointMatrix b p r A (Function.update v i z)=
      (endpointMatrix b p r A v).updateCol i
        (fun j => b.repr (A z) (powersetCard.ofFinEmbEquiv.symm r j)) := by
  ext j k
  by_cases hk : k=i
  · subst k
    simp [endpointMatrix,Matrix.updateCol]
  · simp [endpointMatrix,Matrix.updateCol,hk]

/-- The Cramer minor is the genuine maximal minor with one common starting
fast column replaced by a common slow column. There is no symbolic-minor
proxy in the comparison. -/
lemma endpointMatrix_cramer (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E)
    {n : ℕ} (w : Fin n → E) (i : Fin p) (j : Fin n) :
    ((endpointMatrix b p r A v).updateCol i (fun k => endpointMatrix b p r A w k j)).det=
      projectedMinor b p r A (Function.update v i (w j)) := by
  calc
    _ = (endpointMatrix b p r A (Function.update v i (w j))).det :=
      congrArg Matrix.det (endpointMatrix_update b p r A v i (w j)).symm
    _ = _ := endpointMatrix_det b p r A _
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.MinorGraph
open Matrix Set Metric
open scoped Matrix.Norms.Elementwise
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma cramer_ratio (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hA : A.det≠0) (i : m) (j : n) :
    (A⁻¹*B) i j=(A.updateCol i (fun r => B r j)).det/A.det := by
  have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (fun r => B r j)
    (isUnit_iff_ne_zero.mpr hA)) i
  change A.det*(A⁻¹*B) i j=(A.updateCol i (fun r => B r j)).det at h
  exact (eq_div_iff hA).mpr (by simpa only [mul_comm] using h)

omit [DecidableEq n] in
lemma graph_bound (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hA : A.det≠0) {δ : ℝ} (hδ : 0≤δ)
    (hm : ∀ i j,|(A.updateCol i (fun r => B r j)).det|≤δ*|A.det|) :
    ‖A⁻¹*B‖≤δ := by
  apply Matrix.norm_le_iff hδ |>.mpr
  intro i j
  rw [Real.norm_eq_abs,cramer_ratio A B hA,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hA)).mpr (hm i j)

lemma block_factorization (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (D : Matrix n n ℝ) (hA : A.det≠0) (hD : D.det≠0) :
    (fromBlocks A B C D).det=A.det*D.det*
      (fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1).det := by
  have he : fromBlocks A B C D = fromBlocks A 0 0 D *
      fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_one,Matrix.zero_mul,add_zero,zero_add,
      ←Matrix.mul_assoc,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD),Matrix.one_mul]
  rw [he,Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁]

/-- The modulus depends only on the two dimensions, never on the size or
sign of the leading determinants. -/
theorem normalized_close (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (B : Matrix m n ℝ) (C : Matrix n m ℝ),
      ‖B‖≤δ → ‖C‖≤δ → |(fromBlocks 1 B C 1).det-1|<ε := by
  have hc : ContinuousAt (fun Z : Matrix (m⊕n) (m⊕n) ℝ => Z.det) 1 :=
    continuous_id.matrix_det.continuousAt
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨r/2,by positivity,fun B C hB hC => ?_⟩
  have hn : ‖fromBlocks (1 : Matrix m m ℝ) B C (1 : Matrix n n ℝ)-1‖≤r/2 := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro i j
    cases i <;> cases j
    · simp [Matrix.fromBlocks,Matrix.one_apply]; positivity
    · simpa [Matrix.fromBlocks,Matrix.one_apply] using
        ((Matrix.norm_le_iff (by positivity)).mp hB _ _)
    · simpa [Matrix.fromBlocks,Matrix.one_apply] using
        ((Matrix.norm_le_iff (by positivity)).mp hC _ _)
    · simp [Matrix.fromBlocks,Matrix.one_apply]; positivity
  have h := hh (lt_of_le_of_lt (by simpa only [dist_eq_norm] using hn) (by linarith))
  simpa only [Matrix.det_one,Real.dist_eq] using h

/-- Relative determinant estimate from the genuine maximal minors. In
particular there is no lower bound on the leading volumes A.det and D.det. -/
theorem relative_joint_determinant (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (A : Matrix m m ℝ) (B : Matrix m n ℝ)
      (C : Matrix n m ℝ) (D : Matrix n n ℝ),
      A.det≠0 → D.det≠0 →
      (∀ i j,|(A.updateCol i (fun r => B r j)).det|≤δ*|A.det|) →
      (∀ i j,|(D.updateCol i (fun r => C r j)).det|≤δ*|D.det|) →
      |(fromBlocks A B C D).det/(A.det*D.det)-1|<ε := by
  obtain ⟨δ,hδ,hclose⟩ := normalized_close (m:=m) (n:=n) ε hε
  refine ⟨δ,hδ,fun A B C D hA hD hAB hDC => ?_⟩
  have h := hclose (A⁻¹*B) (D⁻¹*C) (graph_bound A B hA hδ.le hAB)
    (graph_bound D C hD hδ.le hDC)
  rw [block_factorization A B C D hA hD]
  simpa only [mul_div_cancel_left₀ _ (mul_ne_zero hA hD)] using h
end SmoothObstruction.MinorGraph

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- The genuine endpoint derivative graph in the common product basis.
Cramer ratios are obtained from actual projected fast/mixed minors, not
postulated as a graph-smallness assumption. Either column group may be empty. -/
theorem common_endpoint_graph_bound
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (Gslow : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hstartSlow : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let Afast := endpointMatrix b S.card r A v
    let Aslow := endpointMatrix b S.card r A z
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    Afast.det≠0 ∧ ∀ i j, |(Afast⁻¹*Aslow) i j|≤
      2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
        N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ) := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  have hdet : (endpointMatrix b S.card r A v).det≠0 := by
    rw [endpointMatrix_det]
    exact hl.2
  refine ⟨hdet,?_⟩
  intro i j
  let F := fun l : Fin S.card => if l=i then groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ
    else groupSpace (U s) (V s) (hUV s) (hVU s) S
  let H := fun l : Fin S.card => if l=i then Gslow else G
  let w := Function.update v i (z j)
  have hc : ∀ l,‖(F l).starProjection-(H l).starProjection‖≤δ := by
    intro l
    by_cases hl : l=i
    · simpa only [F,H,ite_eq_left hl] using hstartSlow
    · simpa only [F,H,ite_eq_right hl] using hstart
  have hwm : ∀ l,w l∈H l := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w,H] using hz j
    · simpa [w,H,hl] using hv l
  have hwn : ∀ l,‖w l‖≤1 := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w] using hznorm j
    · simpa [w,hl] using (horth.norm_eq_one l).le
  have hm := common_minor_separation U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv
    F H hc w hwn hwm i (by simp [F]) hsmall
  have hr := congrArg abs (MinorGraph.cramer_ratio (endpointMatrix b S.card r A v)
    (endpointMatrix b S.card r A z) hdet i j)
  simp only [abs_div,endpointMatrix_cramer,endpointMatrix_det] at hr
  exact hr.trans_le ((div_le_iff₀ (abs_pos.mpr hl.2)).mpr hm.2)
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- The genuine endpoint derivative graph in the common product basis.
The actual exterior perturbation, relative even on contracting determinant
lines, is transferred to Cramer ratios without postulating graph smallness.
Either column group may be empty. -/
theorem common_perturbed_endpoint_graph_bound
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (Gslow : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hstartSlow : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    {n : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A := W.starProjection*B
    let Afast := endpointMatrix b S.card r A v
    let Aslow := endpointMatrix b S.card r A z
    let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
    let N₀ := C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))
    let N₁ := C*(C*(Real.exp K)^S.card)^2*(Fintype.card (powersetCard (Fin d) S.card):ℝ)*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*((t:ℝ)-s))+
      N₀*unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    Afast.det≠0 ∧ ∀ i j, |(Afast⁻¹*Aslow) i j|≤(θ+ε)/(1-ε) := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*B
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := hl.1
    linarith
  have he : |projectedMinor b S.card r A v-
      projectedMinor b S.card r (W.starProjection*A₀) v|≤
        ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B v
      (fun i => (horth.norm_eq_one i).le) hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by dsimp [ε]; ring
  have hnon := (relative_minor_ratios (c:=0) (c':=0) (δ:=0)
    hl.2 hε hpert le_rfl he (by simp) (by simp; positivity)).1
  have hdet : (endpointMatrix b S.card r A v).det≠0 := by
    rw [endpointMatrix_det]
    exact hnon
  refine ⟨hdet,?_⟩
  intro i j
  let F := fun l : Fin S.card => if l=i then groupSpace (U s) (V s) (hUV s) (hVU s) Sᶜ
    else groupSpace (U s) (V s) (hUV s) (hVU s) S
  let H := fun l : Fin S.card => if l=i then Gslow else G
  let w := Function.update v i (z j)
  have hc : ∀ l,‖(F l).starProjection-(H l).starProjection‖≤δ := by
    intro l
    by_cases hl : l=i
    · simpa only [F,H,ite_eq_left hl] using hstartSlow
    · simpa only [F,H,ite_eq_right hl] using hstart
  have hwm : ∀ l,w l∈H l := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w,H] using hz j
    · simpa [w,H,hl] using hv l
  have hwn : ∀ l,‖w l‖≤1 := by
    intro l
    by_cases hl : l=i
    · subst l
      simpa [w] using hznorm j
    · simpa [w,hl] using (horth.norm_eq_one l).le
  have hm := common_minor_perturbation U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv
    F H hc w hwn hwm i (by simp [F]) hsmall B hζ hpert hdiff
  have hr := congrArg abs (MinorGraph.cramer_ratio (endpointMatrix b S.card r A v)
    (endpointMatrix b S.card r A z) hdet i j)
  simp only [abs_div,endpointMatrix_cramer,endpointMatrix_det] at hr
  exact hr.trans_le hm.2
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- Signed old-to-new leading-minor transfer. In combination with the proved
common perturbed graph bound, this supplies the actual factors used in
`MinorGraph.joint_relative_transfer`. It does not posit their relative error. -/
theorem common_leading_relative_transfer
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) {s t : ℕ} (hst : s≤t) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U s‖≤Real.exp K) (hUt : ‖U t‖≤Real.exp K)
    (hVs : ‖V s‖≤Real.exp K) (hVt : ‖V t‖≤Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖≤C*(max 1 ‖A‖)^S.card)
    (W G : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : Module.finrank ℝ W=S.card)
    (hend : ‖(groupSpace (U t) (V t) (hUV t) (hVU t) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U s) (V s) (hUV s) (hVU s) S).starProjection-G.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (r : powersetCard (Fin d) S.card)
    (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin S.card → EuclideanSpace ℝ (Fin d)) (horth : Orthonormal ℝ v)
    (hv : ∀ i,v i∈G)
    (hsmall : (frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) S.card*δ)*
      (1+((C*(Real.exp K)^S.card)^2*(C*2^S.card))*
        (C*(C^2*(Real.exp K)^(2*S.card)*(Fintype.card (powersetCard (Fin d) S.card):ℝ))))≤1/2)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖<1)
    (hdiff : ‖exterior S.card B-
      exterior S.card (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t))‖≤
        ζ*Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))) :
    let A := W.starProjection*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
    let A' := W.starProjection*B
    let ε := 2*((C*(Real.exp K)^S.card)^2*(C*2^S.card))*C*ζ*
      ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
    projectedMinor b S.card r A v≠0 ∧ projectedMinor b S.card r A' v≠0 ∧
      |projectedMinor b S.card r A' v/projectedMinor b S.card r A v-1|≤ε := by
  have hl := common_fast_minor_lower U V lam hUV hVU S hst hg hK hC hδ hfast hslow
    hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords v horth hv hsmall
  let A₀ := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let A := W.starProjection*B
  let R := Real.exp (((t:ℝ)-s)*(∑ j∈S,lam j))
  let L₀ := (C*(Real.exp K)^S.card)^2*(C*2^S.card)
  let V₀ := ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) S.card‖
  let ε := 2*L₀*C*ζ*V₀
  have hL₀ : 0≤L₀ := by dsimp [L₀]; positivity
  have hε : 0≤ε := by dsimp [ε,V₀]; positivity
  have hQ : ‖exterior S.card W.starProjection‖≤C := by
    apply (hpoly _).trans
    rw [max_eq_left W.starProjection_norm_le,one_pow,mul_one]
  have hl' : R≤2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh : R/2≤L₀*|projectedMinor b S.card r (W.starProjection*A₀) v| := hl.1
    linarith
  have he : |projectedMinor b S.card r A v-
      projectedMinor b S.card r (W.starProjection*A₀) v|≤
        ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by
    have hh := projected_postcomposition_transfer b S.card r W.starProjection A₀ B v
      (fun i => (horth.norm_eq_one i).le) hC hQ hdiff
    calc
      _ ≤ C*(ζ*R)*V₀ := hh
      _ = (C*ζ*V₀)*R := by ring
      _ ≤ (C*ζ*V₀)*(2*L₀*|projectedMinor b S.card r (W.starProjection*A₀) v|) :=
        mul_le_mul_of_nonneg_left hl' (by dsimp [V₀]; positivity)
      _ = ε*|projectedMinor b S.card r (W.starProjection*A₀) v| := by dsimp [ε]; ring
  have hnon := (relative_minor_ratios (c:=0) (c':=0) (δ:=0)
    hl.2 hε hpert le_rfl he (by simp) (by simp; positivity)).1
  refine ⟨hl.2,hnon,?_⟩
  have heq : projectedMinor b S.card r A v/projectedMinor b S.card r (W.starProjection*A₀) v-1=
      (projectedMinor b S.card r A v-projectedMinor b S.card r (W.starProjection*A₀) v)/
        projectedMinor b S.card r (W.starProjection*A₀) v := by
    rw [sub_div,div_self hl.2]
  rw [heq,abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hl.2)).mpr he
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.MinorGraph
open Matrix
open scoped Matrix.Norms.Elementwise
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Three signed relative errors compose without an absolute determinant
floor. The constants here leave room for the source's four-Jacobian bound. -/
lemma triple_relative_error {a b c ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (ha : |a-1|≤ε) (hb : |b-1|≤ε) (hc : |c-1|≤ε) :
    |a*b*c-1|≤7*ε := by
  have hbb : |b|≤2 := by
    have hh := abs_sub_le b 1 0
    norm_num at hh
    linarith
  have hcc : |c|≤2 := by
    have hh := abs_sub_le c 1 0
    norm_num at hh
    linarith
  calc
    _ = |(a-1)*b*c+(b-1)*c+(c-1)| := by congr 1; ring
    _ ≤ |(a-1)*b*c|+|(b-1)*c|+|c-1| := by
      linarith [abs_add_le ((a-1)*b*c+(b-1)*c) (c-1),
        abs_add_le ((a-1)*b*c) ((b-1)*c)]
    _ = |a-1| *|b| *|c|+|b-1| *|c|+|c-1| := by rw [abs_mul,abs_mul,abs_mul]
    _ ≤ ε*2*2+ε*2+ε := by
      gcongr
    _ = 7*ε := by ring

/-- The actual joint endpoint determinant, measured relative to the OLD
leading volumes. Off-diagonal hypotheses are actual inverse-block entries,
so `common_perturbed_endpoint_graph_bound` supplies precisely these bounds.
Both blocks may be empty and the old leading volumes may be arbitrarily
small or have either sign. -/
theorem joint_relative_transfer : ∃ δ : ℝ,0<δ ∧
    ∀ (A₀ : Matrix m m ℝ) (D₀ : Matrix n n ℝ)
      (A : Matrix m m ℝ) (B : Matrix m n ℝ)
      (C : Matrix n m ℝ) (D : Matrix n n ℝ),
      A₀.det≠0 → D₀.det≠0 →
      |A.det/A₀.det-1|≤(1/100:ℝ) → |D.det/D₀.det-1|≤(1/100:ℝ) →
      (∀ i j,|(A⁻¹*B) i j|≤δ) → (∀ i j,|(D⁻¹*C) i j|≤δ) →
      |(fromBlocks A B C D).det/(A₀.det*D₀.det)-1|≤(1/10:ℝ) := by
  obtain ⟨δ,hδ,hclose⟩ := normalized_close (m:=m) (n:=n) (1/100:ℝ) (by norm_num)
  refine ⟨δ,hδ,fun A₀ D₀ A B C D hA₀ hD₀ hA hD hAB hDC => ?_⟩
  have hAn : A.det≠0 := by intro ha; norm_num [ha] at hA
  have hDn : D.det≠0 := by intro hd; norm_num [hd] at hD
  have hab : ‖A⁻¹*B‖≤δ := (Matrix.norm_le_iff hδ.le).mpr (fun i j => by simpa using hAB i j)
  have hdc : ‖D⁻¹*C‖≤δ := (Matrix.norm_le_iff hδ.le).mpr (fun i j => by simpa using hDC i j)
  have hj := hclose (A⁻¹*B) (D⁻¹*C) hab hdc
  have he : (fromBlocks A B C D).det/(A₀.det*D₀.det)=
      A.det/A₀.det*(D.det/D₀.det)*(fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1).det := by
    rw [block_factorization A B C D hAn hDn]
    field_simp
  rw [he]
  have hh := triple_relative_error (by norm_num : (0:ℝ)≤1/100)
    (by norm_num : (1/100:ℝ)≤1) hA hD hj.le
  exact hh.trans (by norm_num)
end SmoothObstruction.MinorGraph

end

end OAI
