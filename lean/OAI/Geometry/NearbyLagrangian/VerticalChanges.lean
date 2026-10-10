import Mathlib
import OAI.Geometry.NearbyLagrangian.BalancedCoordinates
import OAI.Geometry.NearbyLagrangian.RestoredRestriction

namespace OAI

/-! Linear changes of fiber coordinates and restored tube endpoints. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def verticalChange (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) : ℝ := F (q.1,L q.2)

lemma verticalChange_fderiv (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) :
    fderiv ℝ (verticalChange L F) q = (fderiv ℝ F (q.1,L q.2)).comp
      (((ContinuousLinearEquiv.refl ℝ E).prodCongr L) : E × V →L[ℝ] E × W) :=
  ((ContinuousLinearEquiv.refl ℝ E).prodCongr L).comp_right_fderiv

lemma verticalChange_base (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) :
    baseDifferential (verticalChange L F) q.1 q.2 = baseDifferential F q.1 (L q.2) := by
  unfold baseDifferential
  rw [verticalChange_fderiv]
  ext v
  simp

lemma verticalChange_vertical (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) :
    verticalDifferential (verticalChange L F) q.1 q.2 =
      (verticalDifferential F q.1 (L q.2)).comp (L : V →L[ℝ] W) := by
  unfold verticalDifferential
  rw [verticalChange_fderiv]
  ext v
  simp

lemma verticalChange_critical_iff (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) :
    verticalDifferential (verticalChange L F) q.1 q.2 = 0 ↔
      verticalDifferential F q.1 (L q.2) = 0 := by
  rw [verticalChange_vertical]
  constructor
  · intro h
    ext w
    have := congrArg (fun a : V →L[ℝ] ℝ => a (L.symm w)) h
    simpa using this
  · intro h
    rw [h,zero_comp]

theorem TameOn.verticalChange {U : Set E} {F g : E × W → ℝ}
    (T : TameOn U F g) (L : V ≃L[ℝ] W) :
    TameOn U (verticalChange L F) (verticalChange L g) := by
  let J := (ContinuousLinearEquiv.refl ℝ E).prodCongr L
  have hj : ∀ q : E × V, J q = (q.1,L q.2) := fun _ => rfl
  obtain ⟨c,C,M₀,M₁,hc,hC,hM₀,hM₁,hv,hb,hval,hder⟩ := T.estimates
  let A := max 1 ‖(L : V →L[ℝ] W)‖
  let B := max 1 ‖(L.symm : W →L[ℝ] V)‖
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hL (v : V) : ‖L v‖ ≤ A*‖v‖ :=
    ((L : V →L[ℝ] W).le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
  have hLi (v : V) : ‖v‖ ≤ B*‖L v‖ := by
    calc
      _ = ‖L.symm (L v)‖ := by rw [L.symm_apply_apply]
      _ ≤ ‖(L.symm : W →L[ℝ] V)‖*‖L v‖ := (L.symm : W →L[ℝ] V).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)
  refine ⟨?_,?_,?_,c/B^2,C*A^2,M₀,M₁*‖(J : E × V →L[ℝ] E × W)‖,
    div_pos hc (sq_pos_of_pos hB),mul_nonneg hC (sq_nonneg _),hM₀,
    mul_nonneg hM₁ (norm_nonneg (J : E × V →L[ℝ] E × W)),?_,?_,?_,?_⟩
  · intro x hx v
    exact (T.smooth_F x hx (L v)).comp (x,v) J.contDiff.contDiffAt
  · intro x hx v
    exact (T.smooth_g x hx (L v)).comp (x,v) J.contDiff.contDiffAt
  · intro x hx r hr v
    change g (x,L (r • v)) = r^2*g (x,L v)
    rw [L.map_smul]
    exact T.homogeneous x hx r hr (L v)
  · intro x hx v
    rw [verticalChange_vertical L g (x,v)]
    let D := verticalDifferential g x (L v)
    have heq : D = (D.comp (L : V →L[ℝ] W)).comp (L.symm : W →L[ℝ] V) := by ext w; simp
    have hh : ‖D‖ ≤ ‖D.comp (L : V →L[ℝ] W)‖*B := by
      calc
        _ = ‖(D.comp (L : V →L[ℝ] W)).comp (L.symm : W →L[ℝ] V)‖ := congrArg norm heq
        _ ≤ ‖D.comp (L : V →L[ℝ] W)‖*‖(L.symm : W →L[ℝ] V)‖ := opNorm_comp_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right ..) (norm_nonneg _)
    have h1 : c*‖v‖ ≤ B*(c*‖L v‖) := by nlinarith [mul_le_mul_of_nonneg_left (hLi v) hc.le]
    have h2 : B*(c*‖L v‖) ≤ B*‖D‖ := mul_le_mul_of_nonneg_left (hv x hx (L v)) hB.le
    have h3 : B*‖D‖ ≤ B^2*‖D.comp (L : V →L[ℝ] W)‖ := by nlinarith [mul_le_mul_of_nonneg_left hh hB.le]
    have hfinal := h1.trans (h2.trans h3)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    nlinarith [hfinal]
  · intro x hx v
    rw [verticalChange_base L g (x,v)]
    calc
      _ ≤ C*‖L v‖^2 := hb x hx (L v)
      _ ≤ C*(A*‖v‖)^2 := by gcongr; exact hL v
      _ = _ := by ring
  · intro q hq
    exact hval (q.1,L q.2) hq
  · intro q hq
    change ‖fderiv ℝ (Transport.verticalChange L (F-g)) q‖ ≤ _
    rw [verticalChange_fderiv]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hder (q.1,L q.2) hq) (norm_nonneg _))

lemma verticalChange_hessian (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V) :
    (fderiv ℝ (fun q : E × V => verticalDifferential (verticalChange L F) q.1 q.2) q).comp
      (inr ℝ E V) =
    ((L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) : (W →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ)).comp
      (((fderiv ℝ (fun q : E × W => verticalDifferential F q.1 q.2) (q.1,L q.2)).comp
        (inr ℝ E W)).comp (L : V →L[ℝ] W)) := by
  let J := (ContinuousLinearEquiv.refl ℝ E).prodCongr L
  let P := L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  let D : E × W → (W →L[ℝ] ℝ) := fun q => verticalDifferential F q.1 q.2
  have he : (fun q : E × V => verticalDifferential (verticalChange L F) q.1 q.2) =
      P ∘ (D ∘ J) := by
    funext r
    rw [verticalChange_vertical L F r]
    rfl
  rw [he,P.comp_fderiv,J.comp_right_fderiv]
  ext v a
  rfl

lemma verticalChange_hessian_bijective (L : V ≃L[ℝ] W) (F : E × W → ℝ) (q : E × V)
    (h : Function.Bijective
      ((fderiv ℝ (fun q : E × W => verticalDifferential F q.1 q.2) (q.1,L q.2)).comp
        (inr ℝ E W))) :
    Function.Bijective
      ((fderiv ℝ (fun q : E × V => verticalDifferential (verticalChange L F) q.1 q.2) q).comp
        (inr ℝ E V)) := by
  rw [verticalChange_hessian]
  exact (L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).bijective.comp (h.comp L.bijective)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Tubes
open Set ContinuousMap
open scoped Topology
variable {B : Type*} [TopologicalSpace B]

def tubeCoe {k l : ℕ} : C(Tube k l,RegularHomogeneous (Euclidean (k+l))) :=
  ⟨Subtype.val,continuous_subtype_val⟩

theorem lift_tube_homotopy {k l : ℕ} (f : C(B,Tube k l))
    (g : C(B,RegularHomogeneous (Euclidean (k+l))))
    (hfg : (tubeCoe.comp f).Homotopic g) :
    ∃ g' : C(B,Tube k l), f.Homotopic g' ∧ ∀ b, (g' b).val = g b := by
  obtain ⟨H⟩ := hfg
  have hmem (t : unitInterval) (b : B) :
      H (t,b) ∈ pathComponent (standardForm k l) := by
    let P : Path ((f b).val) (H (t,b)) :=
      { toFun := fun s => H (s*t,b)
        continuous_toFun := H.continuous_toFun.comp
          ((continuous_id.mul continuous_const).prodMk continuous_const)
        source' := by
          simp only [zero_mul]
          exact H.apply_zero b
        target' := by simp }
    exact (show Joined ((f b).val) (H (t,b)) from ⟨P⟩).mem_pathComponent (f b).property
  let g' : C(B,Tube k l) :=
    ⟨fun b => ⟨H (1,b),hmem 1 b⟩,
      (H.continuous_toFun.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  have hH : f.Homotopic g' := by
    exact ⟨{ toFun := fun p => ⟨H p,hmem p.1 p.2⟩
             continuous_toFun := H.continuous_toFun.subtype_mk _
             map_zero_left := fun b => Subtype.ext (H.apply_zero b)
             map_one_left := fun _ => rfl }⟩
  exact ⟨g',hH,fun b => H.apply_one b⟩

theorem StablyNonNull.of_homotopic {m : ℕ} {a b : C(B,Tube m m)}
    (ha : StablyNonNull a) (hab : a.Homotopic b) : StablyNonNull b := by
  intro r h
  obtain ⟨v,hv⟩ := h
  exact ha r ⟨v,((Homotopic.refl (stabilizeFor m r)).comp hab).trans hv⟩

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Transport
open Tubes ContinuousLinearMap Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace
variable {V Z B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Z] {I : ModelWithCorners ℝ V Z}
  [TopologicalSpace B] [ChartedSpace Z B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_restored_tube_endpoint {m d n : ℕ}
    {U : Set (Euclidean d)}
    {F : Euclidean d × TransportFiber (Euclidean d) (Euclidean (m+m)) n → ℝ}
    {g : Euclidean d × Euclidean (m+m) → ℝ}
    (T : TameOn U F (iterReference g n))
    {s : Euclidean d → TransportFiber (Euclidean d) (Euclidean (m+m)) n}
    (hs : ∀ x ∈ U, ContDiffAt ℝ ∞ s x)
    (hc : ∀ x ∈ U, ∀ w, verticalDifferential F x w = 0 ↔ w = s x)
    (hh : ∀ x ∈ U, Function.Bijective
      ((fderiv ℝ (fun q => verticalDifferential F q.1 q.2) (x,s x)).comp
        (inr ℝ (Euclidean d) (TransportFiber (Euclidean d) (Euclidean (m+m)) n))))
    {j : B → Euclidean d} (hj : ContMDiff I 𝓘(ℝ,Euclidean d) ∞ j)
    (hU : ∀ b, j b ∈ U) (a : C(B,Tube m m))
    (hg : ∀ b w, g (j b,w) = (a b).val w) (R : ℝ) :
    ∃ (A : ℝ)
      (δ : C(B,Tube (transportIndex m d n) (transportIndex m d n)))
      (H : B × Euclidean (transportIndex m d n+transportIndex m d n) → ℝ)
      (σ : B → Euclidean (transportIndex m d n+transportIndex m d n)),
      1 ≤ A ∧ R < A ∧ ((addBalancedFor m d n).comp a).Homotopic δ ∧
      (∀ q : B × Euclidean (transportIndex m d n+transportIndex m d n), q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)))
          𝓘(ℝ,ℝ) ∞ (fun q => (δ q.1).val q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)))
        𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F (j q.1,transportCoordinates m d n q.2)) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = (δ q.1).val q.2) ∧
      ContMDiff I 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)) ∞ σ ∧
      (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = σ b) ∧
      (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (σ b))) := by
  let L := transportCoordinates m d n
  let s' := L.symm ∘ s
  have hs' : ∀ x ∈ U, ContDiffAt ℝ ∞ s' x := by
    intro x hx
    exact L.symm.contDiff.contDiffAt.comp x (hs x hx)
  have hc' : ∀ x ∈ U, ∀ w, verticalDifferential (verticalChange L F) x w = 0 ↔ w = s' x := by
    intro x hx w
    rw [verticalChange_critical_iff L F (x,w), hc x hx]
    exact ⟨fun h => by simpa [s'] using congrArg L.symm h,
      fun h => by rw [h]; simp [s']⟩
  have hh' : ∀ x ∈ U, Function.Bijective
      ((fderiv ℝ (fun q => verticalDifferential (verticalChange L F) q.1 q.2) (x,s' x)).comp
        (inr ℝ (Euclidean d) (Euclidean (transportIndex m d n+transportIndex m d n)))) := by
    intro x hx
    apply verticalChange_hessian_bijective
    simpa [s'] using hh x hx
  obtain ⟨A,γ,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,hss,hHc,hHh⟩ :=
    (T.verticalChange L).exists_restored_single_critical hj hU hs' hc' hh' R
  have href : (T.verticalChange L).restrictedReference hj.continuous hU =
      tubeCoe.comp ((addBalancedFor m d n).comp a) := by
    ext b w
    exact iterReference_transportCoordinates_at n (j b) (a b) (hg b) w
  rw [href] at hhom
  obtain ⟨δ,hδ,hδval⟩ := lift_tube_homotopy ((addBalancedFor m d n).comp a) γ hhom
  have he : (fun q : B × Euclidean (transportIndex m d n+transportIndex m d n) =>
      (δ q.1).val q.2) = fun q => γ q.1 q.2 := by
    funext q
    rw [hδval]
  refine ⟨A,δ,H,s' ∘ j,hA,hRA,hδ,?_,hHs,hHi,?_,hss,hHc,hHh⟩
  · simpa only [he] using hgs
  · intro q hq
    simpa only [hδval] using hHo q hq

end NearbyLagrangian.Transport

end

end OAI
