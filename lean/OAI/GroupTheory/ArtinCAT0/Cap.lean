import OAI.GroupTheory.ArtinCAT0.SectorCharts

namespace OAI

open scoped Classical

namespace ArtinCAT0.GridDisk
variable {H N : ℕ} [NeZero N]

lemma edges_bound {X : Type*} [PseudoMetricSpace X] (v : Vertex H N → X)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ r i, dist (v (Sum.inl (r,i))) (v (Sum.inl (r,i+1))) ≤ A)
    (hb : ∀ (r : Fin (H+1)) i, dist (v (Sum.inl (r.succ,i))) (v (Sum.inl (r.castSucc,i))) ≤ B)
    (hc : ∀ i, dist (v (Sum.inl (0,i))) (v (Sum.inr ())) ≤ B) :
    ∀ f k, dist (v (tail H N (f,k))) (v (tail H N (f,k+1))) ≤ A+B := by
  have hdiag (r : Fin (H+1)) (i : Fin N) :
      dist (v (Sum.inl (r.succ,i))) (v (Sum.inl (r.castSucc,i+1))) ≤ A+B :=
    (dist_triangle _ (v (Sum.inl (r.succ,i+1))) _).trans (add_le_add (ha _ _) (hb _ _))
  rintro (⟨r,i,b⟩ | i) k
  · cases b <;> fin_cases k
    · exact (ha _ _).trans (by linarith)
    · exact (hb _ _).trans (by linarith)
    · change dist (v (Sum.inl (r.castSucc,i+1))) (v (Sum.inl (r.succ,i))) ≤ A+B
      rw [dist_comm]
      exact hdiag r i
    · exact hdiag r i
    · change dist (v (Sum.inl (r.castSucc,i+1))) (v (Sum.inl (r.castSucc,i))) ≤ A+B
      rw [dist_comm]
      exact (ha r.castSucc i).trans (by linarith)
    · change dist (v (Sum.inl (r.castSucc,i))) (v (Sum.inl (r.succ,i))) ≤ A+B
      rw [dist_comm]
      exact (hb r i).trans (by linarith)
  · fin_cases k
    · exact (ha _ _).trans (by linarith)
    · exact (hc _).trans (by linarith)
    · change dist (v (Sum.inr ())) (v (Sum.inl (0,i))) ≤ A+B
      rw [dist_comm]
      exact (hc i).trans (by linarith)

end ArtinCAT0.GridDisk

namespace ArtinCAT0.TrianglePatch
variable {A U : Type*} [Fintype A] (P : TrianglePatch A U)

lemma sum_faces_boundary (w : A × Fin 3 → ℤ)
    (ha : ∀ d, ¬P.Boundary d → w (P.mate d) = -w d) :
    (∑ a, ∑ i, w (a,i)) = ∑ d, if P.Boundary d then w d else 0 := by
  classical
  let interior (d : A × Fin 3) := if P.Boundary d then 0 else w d
  have hb (d) : P.Boundary (P.mate d) ↔ P.Boundary d := by
    change P.mate (P.mate d)=P.mate d ↔ P.mate d=d
    rw [P.mate_mate]
    exact eq_comm
  have hi (d) : interior (P.mate d) = -interior d := by
    by_cases hd : P.Boundary d <;> simp only [interior,hb,hd,ite_true,ite_false,neg_zero]
    exact ha d hd
  have hz : ∑ d, interior d = 0 := by
    have h := Equiv.sum_comp P.mate interior
    simp only [hi,Finset.sum_neg_distrib] at h
    omega
  rw [← Fintype.sum_prod_type]
  have he (d) : w d = interior d+(if P.Boundary d then w d else 0) := by
    by_cases hd : P.Boundary d <;> simp [interior,hd]
  have hh : (∑ d, w d) = (∑ d, interior d)+(∑ d, if P.Boundary d then w d else 0) := by
    conv_lhs => arg 2; intro d; rw [he d]
    exact Finset.sum_add_distrib
  rw [hh,hz,zero_add]

namespace Sides
variable {K : ℕ} [NeZero K] (S : P.Sides K)

noncomputable def boundaryEquiv : (Fin 3 × Fin K) ≃ {d : A × Fin 3 // P.Boundary d} :=
  Equiv.ofBijective (fun e => ⟨S.dart e,S.fixed e⟩) ⟨
    fun _ _ h => S.dart_injective (congrArg Subtype.val h),by
      rintro ⟨d,hd⟩
      obtain ⟨e,he⟩ := S.complete d hd
      exact ⟨e,Subtype.ext he⟩⟩

omit [NeZero K] in
lemma sum_boundary (w : A × Fin 3 → ℤ) :
    (∑ d, if P.Boundary d then w d else 0) = ∑ i : Fin 3, ∑ j : Fin K, w (S.dart (i,j)) := by
  classical
  rw [← Finset.sum_filter,← Fintype.sum_prod_type (fun d : Fin 3 × Fin K => w (S.dart d))]
  symm
  apply Finset.sum_bij (fun e _ => S.dart e)
  · intro e _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.fixed e⟩
  · intro e _ f _ hef
    exact S.dart_injective hef
  · intro d hd
    obtain ⟨e,he⟩ := S.complete d (Finset.mem_filter.mp hd).2
    exact ⟨e,Finset.mem_univ _,he⟩
  · intro e _
    rfl

end Sides
end ArtinCAT0.TrianglePatch

namespace ArtinCAT0.TriangleMesh
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V)

lemma region_stokes (Q : F → Prop) [DecidablePred Q] (w : F × Fin 3 → ℤ)
    (hw : ∀ d, w (M.mate d) = -w d) :
    (∑ f, if Q f then ∑ i, w (f,i) else 0) =
      ∑ d, if Q d.1 ∧ ¬Q (M.mate d).1 then w d else 0 := by
  classical
  let interior (d : F × Fin 3) := if Q d.1 ∧ Q (M.mate d).1 then w d else 0
  have ha (d) : interior (M.mate d) = -interior d := by
    dsimp only [interior]
    rw [M.mate_mate]
    by_cases hf : Q d.1 <;> by_cases hg : Q (M.mate d).1 <;>
      simp only [hf,hg,and_self,and_true,and_false,ite_true,ite_false,neg_zero]
    exact hw d
  have hz : ∑ d, interior d = 0 := by
    have he := Equiv.sum_comp M.mate interior
    simp only [ha,Finset.sum_neg_distrib] at he
    omega
  have he : (∑ f, if Q f then ∑ i, w (f,i) else 0) = ∑ d, if Q d.1 then w d else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : Q f <;> simp [hf]
  rw [he]
  have hd (d) : (if Q d.1 then w d else 0) =
      interior d+(if Q d.1 ∧ ¬Q (M.mate d).1 then w d else 0) := by
    by_cases hf : Q d.1 <;> by_cases hg : Q (M.mate d).1 <;> simp [hf,hg,interior]
  simp only [hd,Finset.sum_add_distrib,hz,zero_add]

namespace Replacement
open RayIndex
variable {A U : Type*} [Fintype A] (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)

noncomputable def edgeFlux (p : Vertex M P S → RayIndex.Point) (f : F) (i : Fin 3) : ℤ :=
  ∑ j : Fin K, edge (p (vertex M P S (f,S.point (i,j.castSucc))))
    (p (vertex M P S (f,S.point (i,j.succ))))

omit [Fintype F] [Fintype A] [NeZero K] in
lemma point_seam (p : Vertex M P S → RayIndex.Point) (f : F) (i : Fin 3) (j : Fin (K+1)) :
    p (vertex M P S ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j))) =
      p (vertex M P S (f,S.point (i,j.rev))) := by
  have h := vertex_seam M P S f i j.rev
  rw [Fin.rev_rev] at h
  exact congrArg p h.symm

omit [Fintype F] [Fintype A] [NeZero K] in
lemma edgeFlux_mate (p : Vertex M P S → RayIndex.Point) (d : F × Fin 3) :
    edgeFlux M P S p (M.mate d).1 (M.mate d).2 = -edgeFlux M P S p d.1 d.2 := by
  rcases d with ⟨f,i⟩
  unfold edgeFlux
  calc
    _ = ∑ j : Fin K, -edge (p (vertex M P S (f,S.point (i,j.rev.castSucc))))
        (p (vertex M P S (f,S.point (i,j.rev.succ)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [point_seam M P S p f i j.castSucc,point_seam M P S p f i j.succ,
        Fin.rev_castSucc,Fin.rev_succ,edge_reverse]
    _ = _ := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact Equiv.sum_comp Fin.revPerm (fun j : Fin K =>
        edge (p (vertex M P S (f,S.point (i,j.castSucc))))
          (p (vertex M P S (f,S.point (i,j.succ)))))

omit [Fintype F] in
lemma fiber_index (p : Vertex M P S → RayIndex.Point) (f : F) :
    (∑ a, face (fun i => p ((mesh M P S).tail ((f,a),i)))) =
      ∑ i, edgeFlux M P S p f i := by
  let q : U → RayIndex.Point := fun u => p (vertex M P S (f,u))
  let w (d : A × Fin 3) := edge (q (P.tail d)) (q (P.tail (d.1,d.2+1)))
  have ha (d) (hd : ¬P.Boundary d) : w (P.mate d) = -w d := by
    dsimp only [w]
    rw [P.tail_mate d hd,P.tail_rotate_mate d hd]
    exact edge_reverse _ _
  change (∑ a, ∑ i, w (a,i)) = _
  rw [P.sum_faces_boundary w ha,S.sum_boundary]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [w]
  rw [S.tail,S.head]

lemma region_index (Q : F → Prop) [DecidablePred Q]
    (p : Vertex M P S → RayIndex.Point) (q : V → RayIndex.Point)
    (hb : ∀ f i, Q f → ¬Q (M.mate (f,i)).1 →
      edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1)))) :
    (∑ f : F × A, if Q f.1 then face (fun i => p ((mesh M P S).tail (f,i))) else 0) =
      ∑ f, if Q f then face (fun i => q (M.tail (f,i))) else 0 := by
  rw [Fintype.sum_prod_type]
  have he (f) : (∑ a, if Q f then face (fun i => p ((mesh M P S).tail ((f,a),i))) else 0) =
      if Q f then ∑ i, edgeFlux M P S p f i else 0 := by
    by_cases hf : Q f
    · simp only [hf,ite_true,fiber_index]
    · simp only [hf,ite_false,Finset.sum_const_zero]
  simp only [he]
  rw [M.region_stokes Q (fun d => edgeFlux M P S p d.1 d.2) (edgeFlux_mate M P S p),
    RayIndex.patch_boundary_sum M Q q]
  apply Finset.sum_congr rfl
  rintro ⟨f,i⟩ _
  by_cases h : Q f ∧ ¬Q (M.mate (f,i)).1
  · simp only [h]
    exact hb f i h.1 h.2
  · simp only [h,ite_false]

end Replacement
end ArtinCAT0.TriangleMesh

namespace ArtinCAT0

section ConeMetric
variable {X : Type*} [MetricSpace X]

lemma segment_dist_start {a b : X} {γ : ℝ→X} (h : Segment a b γ)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : dist (γ t) a = t*dist a b := by
  have hh := h.2.2 t ht 0 (by norm_num)
  simpa only [h.1,sub_zero,abs_of_nonneg ht.1] using hh

lemma segment_dist_end {a b : X} {γ : ℝ→X} (h : Segment a b γ)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : dist (γ t) b = (1-t)*dist a b := by
  have hh := h.2.2 t ht 1 (by norm_num)
  simpa only [h.2.1,abs_sub_comm t 1,abs_of_nonneg (sub_nonneg.mpr ht.2)] using hh

lemma segment_radius_lower {a b y : X} {γ : ℝ→X} (h : Segment a b γ)
    {t A L : ℝ} (ht : t∈Set.Icc 0 1) (ha : A≤dist y a) (hb : A≤dist y b)
    (hL : dist a b≤L) : A-L/2≤dist y (γ t) := by
  have h1 := dist_triangle y (γ t) a
  have h2 := dist_triangle y (γ t) b
  rw [segment_dist_start h ht] at h1
  rw [segment_dist_end h ht] at h2
  nlinarith

end ConeMetric

namespace GridDisk
variable {H N : ℕ} [NeZero N]

noncomputable def rowTime (r : Fin (H+2)) : ℝ := r.val/(H+1:ℕ)

lemma rowTime_mem (r : Fin (H+2)) : rowTime r∈Set.Icc 0 1 := by
  have hp : (0:ℝ)<(H+1:ℕ) := Nat.cast_pos.mpr (by omega)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp.le,?_⟩
  apply (div_le_iff₀ hp).mpr
  rw [one_mul]
  exact_mod_cast (show r.val≤H+1 by omega)

@[simp] lemma rowTime_zero : rowTime (0 : Fin (H+2)) = 0 := by simp [rowTime]
@[simp] lemma rowTime_last : rowTime (Fin.last (H+1)) = 1 := by
  simp only [rowTime,Fin.val_last]
  exact div_self (Nat.cast_ne_zero.mpr (by omega))

lemma rowTime_step (r : Fin (H+1)) : |rowTime r.succ-rowTime r.castSucc| = 1/(H+1:ℕ) := by
  have hp : (0:ℝ)<(H+1:ℕ) := Nat.cast_pos.mpr (by omega)
  simp only [rowTime,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,← sub_div,add_sub_cancel_left]
  rw [abs_div,abs_one,abs_of_pos (by positivity : (0:ℝ)<(H:ℝ)+1)]

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
variable (y : X) (base : G) (boundary : Fin N → G) (γ : Fin N → ℝ → X) (round : X→G)

noncomputable def conePoint : Vertex H N → X
  | Sum.inl (r,i) => γ i (rowTime r)
  | Sum.inr _ => base •y

noncomputable def coneLabel : Vertex H N → G
  | Sum.inl (r,i) => if r=Fin.last (H+1) then boundary i else round (γ i (rowTime r))
  | Sum.inr _ => base

omit [NeZero N] [Group G] [MetricSpace X] [MulAction G X] in
@[simp] lemma coneLabel_outer (i : Fin N) :
    coneLabel base boundary γ round (Sum.inl (Fin.last (H+1),i)) = boundary i := by
  simp [coneLabel]

variable (hγ : ∀ i, Segment (base•y) (boundary i•y) (γ i))
  {E : ℝ} (hE : 0≤E) (hround : ∀ x, dist x (round x•y)≤E)

include hγ hE hround in
omit [NeZero N] in
lemma cone_approx (p : Vertex H N) :
    dist (conePoint y base γ p) (coneLabel base boundary γ round p•y)≤E := by
  rcases p with ⟨r,i⟩|u
  · by_cases hr : r=Fin.last (H+1)
    · subst r
      simp only [conePoint,rowTime_last,hγ i |>.2.1,coneLabel_outer,dist_self]
      exact hE
    · simpa only [conePoint,coneLabel,ite_eq_right hr] using hround (γ i (rowTime r))
  · simpa only [conePoint,coneLabel,dist_self] using hE

include hγ in
lemma conePoint_horizontal (hX : CAT0 X) {A : ℝ}
    (ha : ∀ i, dist (boundary i•y) (boundary (i+1)•y)≤A)
    (r : Fin (H+2)) (i : Fin N) :
    dist (conePoint y base γ (Sum.inl (r,i))) (conePoint y base γ (Sum.inl (r,i+1)))≤A := by
  have hh := comparison_common_start hX (hγ i) (hγ (i+1)) (rowTime_mem r)
  exact hh.trans ((mul_le_mul_of_nonneg_right (rowTime_mem r).2 dist_nonneg).trans (by simpa using ha i))

include hγ in
omit [NeZero N] in
lemma conePoint_radial {B : ℝ}
    (hb : ∀ i, dist (base•y) (boundary i•y)≤(H+1:ℕ)*B)
    (r : Fin (H+1)) (i : Fin N) :
    dist (conePoint y base γ (Sum.inl (r.succ,i))) (conePoint y base γ (Sum.inl (r.castSucc,i)))≤B := by
  change dist (γ i (rowTime r.succ)) (γ i (rowTime r.castSucc))≤B
  rw [(hγ i).2.2 _ (rowTime_mem _) _ (rowTime_mem _),rowTime_step,one_div_mul_eq_div]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<H+1))).mpr (by simpa only [mul_comm] using hb i)

include hγ in
omit [NeZero N] in
lemma conePoint_center (i : Fin N) :
    conePoint y base γ (Sum.inl (0,i) : Vertex H N) = conePoint y base γ (Sum.inr () : Vertex H N) := by
  simp only [conePoint,rowTime_zero,(hγ i).1]

include hγ hE hround in
omit [NeZero N] in
lemma coneLabel_radius {A L : ℝ} (ha : A≤dist y (base•y))
    (hb : ∀ i, A≤dist y (boundary i•y)) (hL : ∀ i, dist (base•y) (boundary i•y)≤L)
    (hL0 : 0≤L) (p : Vertex H N) :
    A-L/2-E ≤ dist y (coneLabel base boundary γ round p•y) := by
  have hp : A-L/2≤dist y (conePoint y base γ p) := by
    rcases p with ⟨r,i⟩|u
    · exact segment_radius_lower (hγ i) (rowTime_mem r) ha (hb i) (hL i)
    · change A-L/2≤dist y (base•y)
      linarith
  have hq := cone_approx y base boundary γ round hγ hE hround p
  have hh := dist_triangle y (coneLabel base boundary γ round p•y) (conePoint y base γ p)
  rw [dist_comm (coneLabel base boundary γ round p•y)] at hh
  linarith

end GridDisk
end ArtinCAT0

open scoped Classical

namespace ArtinCAT0.GridDisk
variable (K : ℕ) [NeZero K]

lemma sideIndex_reverse (i : Fin 3) (j : Fin (K+1)) :
    sideIndex K (-i-1) j.rev = -sideIndex K i j := by
  have hK := NeZero.pos K
  have hj : j.val≤K := by omega
  fin_cases i
  · change sideIndex K 2 j.rev = -sideIndex K 0 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (2*K+(K+1-(j.val+1))) % (3*K) = (3*K-(0*K+j.val)%(3*K))%(3*K)
    rw [Nat.mod_eq_of_lt (show 0*K+j.val<3*K by omega)]
    congr 1
    omega
  · change sideIndex K 1 j.rev = -sideIndex K 1 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (1*K+(K+1-(j.val+1))) % (3*K) = (3*K-(1*K+j.val)%(3*K))%(3*K)
    rw [Nat.mod_eq_of_lt (show 1*K+j.val<3*K by omega)]
    congr 1
    omega
  · change sideIndex K 0 j.rev = -sideIndex K 2 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (0*K+(K+1-(j.val+1))) % (3*K) = (3*K-(2*K+j.val)%(3*K))%(3*K)
    by_cases h : j.val=K
    · simp [h,show 2*K+K=3*K by omega]
    · rw [Nat.mod_eq_of_lt (show 2*K+j.val<3*K by omega)]
      congr 1
      omega

end ArtinCAT0.GridDisk

namespace ArtinCAT0.GridSphere
open TriangleMesh
variable (H K : ℕ) [NeZero K]

abbrev Face := Bool × GridDisk.Face H (3*K)
abbrev Vertex := Replacement.Vertex doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)
noncomputable def mesh : TriangleMesh (Face H K) (Vertex H K) :=
  Replacement.mesh doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)

lemma exact : (mesh H K).Exact :=
  Replacement.exact doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)
    doubleTriangle_exact (GridDisk.exact H (3*K))

variable {Z : Type*} (u v : GridDisk.Vertex H (3*K) → Z)
  (hv : ∀ i, u (Sum.inl (Fin.last (H+1),i)) = v (Sum.inl (Fin.last (H+1),-i)))

noncomputable def label : Vertex H K → Z := Quot.lift
  (fun p => if p.1 then v p.2 else u p.2) (by
    rintro _ _ ⟨b,i,j,rfl,rfl⟩
    change (if b then v (GridDisk.sidePoint H K (i,j)) else u (GridDisk.sidePoint H K (i,j))) =
      (if !b then v (GridDisk.sidePoint H K (-i-1,j.rev)) else u (GridDisk.sidePoint H K (-i-1,j.rev)))
    simp only [GridDisk.sidePoint,GridDisk.sideIndex_reverse]
    cases b
    · exact hv _
    · simpa only [Bool.not_true,Bool.false_eq_true,ite_true,ite_false,neg_neg] using (hv (-GridDisk.sideIndex K i j)).symm)

@[simp] lemma label_vertex (b : Bool) (p : GridDisk.Vertex H (3*K)) :
    label H K u v hv (Replacement.vertex doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K) (b,p)) =
      if b then v p else u p := rfl

@[simp] lemma label_tail (b : Bool) (f : GridDisk.Face H (3*K)) (i : Fin 3) :
    label H K u v hv ((mesh H K).tail ((b,f),i)) =
      if b then v (GridDisk.tail H (3*K) (f,i)) else u (GridDisk.tail H (3*K) (f,i)) := rfl

lemma edges {X : Type*} [PseudoMetricSpace X] (a : Z → X) {B : ℝ}
    (hu : ∀ f i, dist (a (u (GridDisk.tail H (3*K) (f,i))))
      (a (u (GridDisk.tail H (3*K) (f,i+1))))≤B)
    (hv' : ∀ f i, dist (a (v (GridDisk.tail H (3*K) (f,i))))
      (a (v (GridDisk.tail H (3*K) (f,i+1))))≤B) :
    ∀ f i, dist (a (label H K u v hv ((mesh H K).tail (f,i))))
      (a (label H K u v hv ((mesh H K).tail (f,i+1))))≤B := by
  rintro ⟨b,f⟩ i
  cases b
  · exact hu f i
  · exact hv' f i

lemma frontier (f : Face H K) (i : Fin 3) :
    (f.1=false ∧ ((mesh H K).mate (f,i)).1.1 ≠ false) ↔
      f.1=false ∧ (GridDisk.patch H (3*K)).Boundary (f.2,i) := by
  rcases f with ⟨b,f⟩
  change (b=false ∧ (Replacement.mateFun doubleTriangle (GridDisk.patch H (3*K))
    (GridDisk.sides H K) ((b,f),i)).1.1≠false) ↔ _
  by_cases h : (GridDisk.patch H (3*K)).Boundary (f,i)
  · cases b <;> simp [Replacement.mateFun,h,doubleTriangle]
  · cases b <;> simp [Replacement.mateFun,h]

omit [NeZero K] in

lemma inner_sum (w : Face H K → ℤ) :
    (∑ f, if f.1=false then w f else 0) = ∑ f, w (false,f) := by
  rw [Fintype.sum_prod_type]
  simp

end ArtinCAT0.GridSphere

open scoped Classical
namespace ArtinCAT0.RayIndex

lemma det_pos_diagonal {p q : Point} (hp : 0<p.1+p.2) (hq : 0<q.1+q.2)
    (hy : p.2≤0) (hy' : 0<q.2) : 0<det p q := by
  have h1 := mul_pos hp hy'
  have h2 := mul_nonpos_of_nonneg_of_nonpos hq.le hy
  dsimp only [det]
  nlinarith

lemma edge_diagonal {p q : Point} (hp : 0<p.1+p.2) (hq : 0<q.1+q.2) :
    edge p q = above q-above p := by
  by_cases hy : p.2≤0 <;> by_cases hy' : q.2≤0
  · simp [edge,upward,above,not_lt.mpr hy,not_lt.mpr hy']
  · have hq' := lt_of_not_ge hy'
    have hd := det_pos_diagonal hp hq hy hq'
    simp [edge,upward,above,hy,hy',not_lt.mpr hy,hq',hd]
  · have hp' := lt_of_not_ge hy
    have hd := det_pos_diagonal hq hp hy' hp'
    simp [edge,upward,above,hy,hy',not_lt.mpr hy',hp',hd]
  · simp [edge,upward,above,hy,hy',lt_of_not_ge hy,lt_of_not_ge hy']

lemma sum_chain {K : ℕ} (p : Fin (K+1) → ℤ) :
    (∑ j : Fin K, (p j.succ-p j.castSucc)) = p (Fin.last K)-p 0 := by
  have h1 := Fin.sum_univ_succ p
  have h2 := Fin.sum_univ_castSucc p
  rw [Finset.sum_sub_distrib]
  omega

lemma edge_chain_diagonal {K : ℕ} (p : Fin (K+1) → Point)
    (hp : ∀ i, 0<(p i).1+(p i).2) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = above (p (Fin.last K))-above (p 0) := by
  simp_rw [edge_diagonal (hp _) (hp _)]
  exact sum_chain (fun i => above (p i))

lemma edge_chain_left {K : ℕ} (p : Fin (K+1) → Point) (hp : ∀ i, (p i).1<0) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = 0 := by
  simp [edge_left (hp _) (hp _)]

lemma edge_chain_low {K : ℕ} (p : Fin (K+1) → Point) (hp : ∀ i, (p i).2≤0) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = 0 := by
  simp [edge_low (hp _) (hp _)]

end ArtinCAT0.RayIndex

open scoped Classical
namespace ArtinCAT0

lemma mirrorPlane_close {g h : TriangleGroup} {D : ℝ}
    (hh : ∀ d, |mirrorVector g d-mirrorVector h d|≤D) :
    |(mirrorPlane g).1-(mirrorPlane h).1|≤D ∧
      |(mirrorPlane g).2-(mirrorPlane h).2|≤D := by
  have hd : 0≤D := (abs_nonneg _).trans (hh (sideMirror 0))
  have h1 := hh (sideMirror 0)
  have h2 := hh (extraMirror 0)
  simp only [mirrorPlane] at *
  rcases abs_le.mp h1 with ⟨h1a,h1b⟩
  rcases abs_le.mp h2 with ⟨h2a,h2b⟩
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

namespace SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

lemma chart_plane_first (y : X) (p : Point) :
    mirrorPlane (chart y 0 p) = ((⌊p.1/rayLength y 0⌋:ℝ),(⌊p.2/rayLength y 1⌋:ℝ)) := by
  unfold chart
  rw [lattice_plane]
  simp [planeRay]

lemma chart_plane_other (y : X) (i : Fin 6) (hi : i≠0) (p : Point) :
    (mirrorPlane (chart y i p)).1=0 ∨ (mirrorPlane (chart y i p)).2=0 := by
  unfold chart
  rw [lattice_plane]
  fin_cases i <;> simp_all [planeRay]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)

include hG hR
lemma chart_small {C : ℝ}
    (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
    (i : Fin 6) (p : Point) (hp : 0≤p.1 ∧ 0≤p.2) {w D : ℝ} (hw : D<w)
    (hx : |(mirrorPlane (chart y i p)).1-w|≤D)
    (hy : |(mirrorPlane (chart y i p)).2-w|≤D) :
    dist y (chart y i p•y) ≤ (rayLength y 0+rayLength y 1)*(w+D+1)+C := by
  have hi : i=0 := by
    by_contra hi
    rcases chart_plane_other y i hi p with h|h
    · rw [h] at hx
      linarith [(abs_le.mp hx).1]
    · rw [h] at hy
      linarith [(abs_le.mp hy).1]
  subst i
  rw [chart_plane_first] at hx hy
  have hL : 0<rayLength y 0 := ray_length_pos hG y hR 0
  have hM : 0<rayLength y 1 := ray_length_pos hG y hR 1
  have h1 := Int.lt_floor_add_one (p.1/rayLength y 0)
  have h2 := Int.lt_floor_add_one (p.2/rayLength y 1)
  have ha : p.1 < rayLength y 0*((⌊p.1/rayLength y 0⌋:ℝ)+1) := by
    have := (div_lt_iff₀ hL).mp h1
    nlinarith
  have hb : p.2 < rayLength y 1*((⌊p.2/rayLength y 1⌋:ℝ)+1) := by
    have := (div_lt_iff₀ hM).mp h2
    nlinarith
  have ha' : p.1≤rayLength y 0*(w+D+1) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hL.le
    dsimp only at hh
    nlinarith
  have hb' : p.2≤rayLength y 1*(w+D+1) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 hM.le
    dsimp only at hh
    nlinarith
  have hh := (abs_le.mp (hchart 0 (0,0) p)).2
  simp only [chart_zero,one_smul,sub_zero] at hh
  have hv := vec_bound (cosine y 0) (cosine_abs hG y hR 0) p
  rw [abs_of_nonneg hp.1,abs_of_nonneg hp.2] at hv
  nlinarith

lemma circle_nonnegative {R t : ℝ} (hR0 : 0≤R) (i : Fin 6) (ht : t∈Set.Icc 0 1) :
    0≤R*(unit (cosine y i) t).1 ∧ 0≤R*(unit (cosine y i) t).2 := by
  have hu := unit_nonneg (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht
  exact ⟨mul_nonneg hR0 hu.1,mul_nonneg hR0 hu.2⟩

lemma circle_first_sum {R t : ℝ} (hR0 : 0≤R) (ht : t∈Set.Icc 0 1) :
    R ≤ (rayLength y 0+rayLength y 1)*
      ((mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2+2) := by
  let p : Point := (R*(unit (cosine y 0) t).1,R*(unit (cosine y 0) t).2)
  have hp : 0≤p.1 ∧ 0≤p.2 := circle_nonnegative hG y hR hR0 0 ht
  have hL : 0<rayLength y 0 := ray_length_pos hG y hR 0
  have hM : 0<rayLength y 1 := ray_length_pos hG y hR 1
  let a : ℝ := ⌊p.1/rayLength y 0⌋
  let b : ℝ := ⌊p.2/rayLength y 1⌋
  have ha : 0≤a := by
    change (0:ℝ)≤(⌊p.1/rayLength y 0⌋:ℝ)
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hp.1 hL.le)
  have hb : 0≤b := by
    change (0:ℝ)≤(⌊p.2/rayLength y 1⌋:ℝ)
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hp.2 hM.le)
  have h1 : p.1< (a+1)*rayLength y 0 := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one _)
  have h2 : p.2< (b+1)*rayLength y 1 := (div_lt_iff₀ hM).mp (Int.lt_floor_add_one _)
  have hsum : R≤p.1+p.2 := by
    have hh := mul_le_mul_of_nonneg_left (unit_sum (cosine_lower hG y hR 0).le (cosine_le_one hG y hR 0) ht).1 hR0
    dsimp only [p]
    nlinarith
  change R ≤ (rayLength y 0+rayLength y 1)*
    ((mirrorPlane (chart y 0 p)).1+(mirrorPlane (chart y 0 p)).2+2)
  rw [chart_plane_first]
  change R≤(rayLength y 0+rayLength y 1)*(a+b+2)
  nlinarith [mul_nonneg hL.le hb,mul_nonneg hM.le ha]

end SixSector
end ArtinCAT0

end OAI
