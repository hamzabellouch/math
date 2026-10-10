import OAI.GroupTheory.ArtinCAT0.Cap

namespace OAI

open scoped Classical
namespace ArtinCAT0.GridDisk
variable {H N : ℕ} [NeZero N]
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

omit [NeZero N] in
lemma rounded_edge_bound (y : X) (q : Vertex H N → X) (v : Vertex H N → G)
    {E B : ℝ} (hq : ∀ p, dist (q p) (v p•y)≤E)
    {p r : Vertex H N} (hpr : dist (q p) (q r)≤B) :
    dist (v p•y) (v r•y)≤B+2*E := by
  have hh := dist_triangle4 (v p•y) (q p) (q r) (v r•y)
  have hp := hq p
  rw [dist_comm] at hp
  linarith [hq r]

lemma cone_fill (hX : CAT0 X) (y : X) (base : G) (boundary : Fin N → G)
    {E A B R L : ℝ} (hE : 0≤E) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L)
    (hdense : ∀ x, ∃ g : G, dist x (g•y)≤E)
    (hstep : ∀ i, dist (boundary i•y) (boundary (i+1)•y)≤A)
    (hspan : ∀ i, dist (base•y) (boundary i•y)≤(H+1:ℕ)*B)
    (hspan' : ∀ i, dist (base•y) (boundary i•y)≤L)
    (hbase : R≤dist y (base•y)) (hboundary : ∀ i, R≤dist y (boundary i•y)) :
    ∃ v : Vertex H N → G,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = boundary i) ∧
      (∀ f k, dist (v (tail H N (f,k))•y) (v (tail H N (f,k+1))•y)≤A+B+4*E) ∧
      (∀ p, R-L/2-E≤dist y (v p•y)) := by
  choose round hround using hdense
  choose γ hγ using fun i => hX.1 (base•y) (boundary i•y)
  let v : Vertex H N → G := coneLabel base boundary γ round
  let q : Vertex H N → X := conePoint y base γ
  have hq : ∀ p, dist (q p) (v p•y)≤E := cone_approx y base boundary γ round hγ hE hround
  refine ⟨v,coneLabel_outer base boundary γ round,?_,?_⟩
  · have hh : ∀ f k, dist (v (tail H N (f,k))•y) (v (tail H N (f,k+1))•y)≤
        (A+2*E)+(B+2*E) := by
      apply edges_bound (fun p => v p•y) (by linarith) (by linarith)
      · intro r i
        exact rounded_edge_bound y q v hq (conePoint_horizontal y base boundary γ hγ hX hstep r i)
      · intro r i
        exact rounded_edge_bound y q v hq (conePoint_radial y base boundary γ hγ hspan r i)
      · intro i
        apply rounded_edge_bound y q v hq
        change dist (conePoint y base γ (Sum.inl (0,i) : Vertex H N)) (conePoint y base γ (Sum.inr ()))≤B
        rw [conePoint_center y base boundary γ hγ,dist_self]
        exact hB
    intro f k
    exact (hh f k).trans_eq (by ring)
  · exact coneLabel_radius y base boundary γ round hγ hE hround hbase hboundary hspan' hL

end ArtinCAT0.GridDisk

namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

abbrev AngularSize (n : ℕ) := 3*(2*(n+1))

def angularEquiv (n : ℕ) : Fin (AngularSize n) ≃ Fin (6*(n+1)) := finCongr (by dsimp [AngularSize]; omega)

@[simp] lemma angularEquiv_val (n : ℕ) (i : Fin (AngularSize n)) : (angularEquiv n i).val=i.val := rfl
@[simp] lemma angularEquiv_add (n : ℕ) (i j : Fin (AngularSize n)) :
    angularEquiv n (i+j) = angularEquiv n i+angularEquiv n j := by
  apply Fin.ext
  change (i.val+j.val) % (3*(2*(n+1))) = (i.val+j.val) % (6*(n+1))
  congr 1; omega

@[simp] lemma angularEquiv_one (n : ℕ) : angularEquiv n 1=1 := by
  apply Fin.ext
  change 1%(3*(2*(n+1)))=1%(6*(n+1))
  congr 1; omega

noncomputable def circleAt (y : X) (n : ℕ) (R : ℝ) (i : Fin (AngularSize n)) : TriangleGroup :=
  ringCircle y (n+1) R (angularEquiv n i)

noncomputable def innerLabel (y : X) (n : ℕ) : GridDisk.Vertex n (AngularSize n) → TriangleGroup
  | Sum.inl (r,i) => circleAt y n r.val i
  | Sum.inr _ => 1

@[simp] lemma circleAt_zero (y : X) (n : ℕ) (i : Fin (AngularSize n)) : circleAt y n 0 i=1 := by
  simp [circleAt,ringCircle,circle,axis]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hC : 0≤C)
  (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
include hG hR hC hchart

omit hC in
lemma circleAt_step (n : ℕ) {R : ℝ} (hR0 : 0≤R) (i : Fin (AngularSize n)) :
    dist (circleAt y n R i•y) (circleAt y n R (i+1)•y)≤20*R/(n+1:ℕ)+C := by
  simp only [circleAt,angularEquiv_add,angularEquiv_one]
  exact ringCircle_step hG y hR hchart (n+1) hR0 _

lemma innerLabel_edges (n : ℕ) :
    ∀ f k, dist (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k))•y)
      (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k+1))•y)≤21+2*C := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (by omega)
  have hh : ∀ f k, dist (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k))•y)
      (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k+1))•y) ≤(20+C)+(1+C) := by
    apply GridDisk.edges_bound (fun p => innerLabel y n p•y) (by linarith) (by linarith)
    · intro r i
      have hh := circleAt_step hG y hR hchart n (Nat.cast_nonneg r.val) i
      have hr : (r.val:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show r.val≤n+1 by omega)
      change dist (circleAt y n r.val i•y) (circleAt y n r.val (i+1)•y)≤20+C
      apply hh.trans
      have hs : 20*(r.val:ℝ)/(n+1:ℕ)≤20 := (div_le_iff₀ hn).mpr (by nlinarith)
      linarith
    · intro r i
      have hh := ringCircle_radial hG y hR hchart (n+1) (r.succ.val) (r.castSucc.val) (angularEquiv n i)
      change dist (circleAt y n r.succ.val i•y) (circleAt y n r.castSucc.val i•y)≤1+C
      simpa only [circleAt,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,abs_one] using hh
    · intro i
      simp only [innerLabel,Fin.val_zero,Nat.cast_zero,circleAt_zero,one_smul,dist_self]
      linarith
  intro f k
  exact (hh f k).trans_eq (by ring)

omit hC hchart in
lemma innerLabel_chart (n : ℕ) (p : GridDisk.Vertex n (AngularSize n)) :
    ∃ i q, 0≤q.1 ∧ 0≤q.2 ∧ innerLabel y n p=chart y i q := by
  rcases p with ⟨r,j⟩|u
  · let e := finProdFinEquiv.symm (angularEquiv n j)
    let t : ℝ := e.2.val/(n+1:ℕ)
    have hp := unit_nonneg (cosine_lower hG y hR e.1).le (cosine_le_one hG y hR e.1)
      (angular_parameter e.2)
    exact ⟨e.1,((r.val:ℝ)*(unit (cosine y e.1) t).1,(r.val:ℝ)*(unit (cosine y e.1) t).2),
      mul_nonneg (Nat.cast_nonneg _) hp.1,mul_nonneg (Nat.cast_nonneg _) hp.2,rfl⟩
  · exact ⟨0,(0,0),le_rfl,le_rfl,(chart_zero y 0).symm⟩

end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0
namespace RayIndex
noncomputable def shifted (w : ℝ) (p : Point) : Point := (p.1-w,p.2-w)

lemma edge_chain_equal {K : ℕ} (p : Fin (K+1) → Point)
    (hp : (∀ i, 0<(p i).1+(p i).2) ∨ (∀ i, (p i).1<0) ∨ (∀ i, (p i).2≤0)) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = edge (p 0) (p (Fin.last K)) := by
  rcases hp with h|h|h
  · rw [edge_chain_diagonal p h,edge_diagonal (h 0) (h (Fin.last K))]
  · rw [edge_chain_left p h,edge_left (h 0) (h (Fin.last K))]
  · rw [edge_chain_low p h,edge_low (h 0) (h (Fin.last K))]
end RayIndex

namespace TriangleMesh.Replacement
open RayIndex
variable {F V A U : Type*} (M : TriangleMesh F V) (P : TrianglePatch A U)
  {K : ℕ} [NeZero K] (S : P.Sides K)
omit [NeZero K] in
lemma edgeFlux_equal (p : Vertex M P S → Point) (q : V → Point) (f : F) (i : Fin 3)
    (hc : ∀ j, p (vertex M P S (f,S.point (j,0))) = q (M.tail (f,j)))
    (hp : (∀ j, 0<(p (vertex M P S (f,S.point (i,j)))).1+(p (vertex M P S (f,S.point (i,j)))).2) ∨
      (∀ j, (p (vertex M P S (f,S.point (i,j)))).1<0) ∨
      (∀ j, (p (vertex M P S (f,S.point (i,j)))).2≤0)) :
    edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1))) := by
  rw [edgeFlux,edge_chain_equal _ hp,hc]
  rw [S.ends,hc]
end TriangleMesh.Replacement

namespace SixSector
open SectorMetric RayIndex
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

lemma chart_plane_other_uniform (y : X) (i : Fin 6) (hi : i≠0) :
    (∀ p, (mirrorPlane (chart y i p)).1=0) ∨ (∀ p, (mirrorPlane (chart y i p)).2=0) := by
  simp_rw [chart,lattice_plane]
  fin_cases i <;> simp_all [planeRay]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR

lemma ringCircle_next_product (N : ℕ) [NeZero N] (R : ℝ) (a : Fin 6) (j : Fin N) :
    ringCircle y N R (finProdFinEquiv (a,j)+1) = circle y R a ((j.val+1:ℕ)/N) := by
  rw [product_next]
  split_ifs with h
  · exact ringCircle_product y N R a ⟨j.val+1,h⟩
  · have hj : j.val+1=N := by omega
    rw [ringCircle_product,hj,div_self (by exact_mod_cast (NeZero.ne N)),circle_one hG y hR]
    simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]

lemma circle_shift_diagonal {R w t : ℝ} (hR0 : 0≤R) (ht : t∈Set.Icc 0 1)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    0<(shifted w (mirrorPlane (circle y R 0 t))).1+
      (shifted w (mirrorPlane (circle y R 0 t))).2 := by
  have hh := circle_first_sum hG y hR hR0 ht
  have hL : 0<rayLength y 0+rayLength y 1 := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
  dsimp only [shifted]
  have hs : 2*w < (mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2 := by
    nlinarith
  linarith

lemma circle_chain_index (N : ℕ) [NeZero N] {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) (a : Fin 6) :
    (∑ j : Fin N, edge (shifted w (mirrorPlane (circle y R a (j.val/N))))
      (shifted w (mirrorPlane (circle y R a ((j.val+1:ℕ)/N))))) = if a=0 then 1 else 0 := by
  let p : Fin (N+1) → RayIndex.Point := fun j => shifted w (mirrorPlane (circle y R a (j.val/N)))
  have ht (j : Fin (N+1)) : (j.val/(N:ℝ))∈Set.Icc 0 1 := by
    have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
    exact ⟨div_nonneg (Nat.cast_nonneg _) hN.le,(div_le_iff₀ hN).mpr (by rw [one_mul]; exact_mod_cast (show j.val≤N by omega))⟩
  change (∑ j : Fin N, edge (p j.castSucc) (p j.succ)) = _
  by_cases ha : a=0
  · subst a
    rw [ite_eq_left rfl,edge_chain_diagonal p (fun j => circle_shift_diagonal hG y hR hR0 (ht j) hlarge)]
    have hp0 : (p 0).2 = -w := by
      dsimp only [p,shifted]
      simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]
      rw [← chart_axis1 y 0 R,chart_plane_first]
      simp
    have hplast : (p (Fin.last N)).1 = -w := by
      dsimp only [p,shifted]
      rw [Fin.val_last,div_self (by exact_mod_cast (NeZero.ne N)),circle_one hG y hR]
      rw [← chart_axis2 y 0 R,chart_plane_first]
      simp
    have hd := circle_shift_diagonal hG y hR hR0 (ht (Fin.last N)) hlarge
    change 0<(p (Fin.last N)).1+(p (Fin.last N)).2 at hd
    rw [hplast] at hd
    have hp : 0<(p (Fin.last N)).2 := by linarith
    simp [above,hp,hp0,hw.le]
  · rw [ite_eq_right ha]
    rcases chart_plane_other_uniform y a ha with h|h
    · apply edge_chain_left p
      intro j
      change (mirrorPlane (chart y a _)).1-w<0
      rw [h]
      linarith
    · apply edge_chain_low p
      intro j
      change (mirrorPlane (chart y a _)).2-w≤0
      rw [h]
      linarith

lemma ringCircle_index (N : ℕ) [NeZero N] {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    (∑ j : Fin (6*N), edge (shifted w (mirrorPlane (ringCircle y N R j)))
      (shifted w (mirrorPlane (ringCircle y N R (j+1))))) = 1 := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp_rw [ringCircle_product,ringCircle_next_product hG y hR]
  simp_rw [circle_chain_index hG y hR N hR0 hw hlarge]
  simp

end SixSector
end ArtinCAT0

namespace ArtinCAT0.GridDisk
open RayIndex
variable (H N : ℕ) [NeZero N]
lemma sum_index_boundary (p : Vertex H N → Point) :
    (∑ f, face (fun i => p (tail H N (f,i)))) = ∑ j : Fin N,
      edge (p (Sum.inl (Fin.last (H+1),j))) (p (Sum.inl (Fin.last (H+1),j+1))) := by
  classical
  let w (d : Face H N × Fin 3) := edge (p (tail H N d)) (p (tail H N (d.1,d.2+1)))
  have ha (d) (hd : ¬(patch H N).Boundary d) : w ((patch H N).mate d) = -w d := by
    dsimp only [w]
    change edge (p ((patch H N).tail ((patch H N).mate d)))
      (p ((patch H N).tail (((patch H N).mate d).1,((patch H N).mate d).2+1))) = _
    rw [(patch H N).tail_mate d hd,(patch H N).tail_rotate_mate d hd]
    exact edge_reverse _ _
  change (∑ f, ∑ i, w (f,i)) = _
  rw [(patch H N).sum_faces_boundary w ha,← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => (A H N (Fin.last H) j,0))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(boundary_iff H N _).mpr ⟨j,rfl⟩⟩
  · intro j _ k _ hjk
    simpa only [Prod.mk.injEq,A,Sum.inl.injEq,true_and,and_true] using hjk
  · intro d hd
    obtain ⟨j,rfl⟩ := (boundary_iff H N _).mp (Finset.mem_filter.mp hd).2
    exact ⟨j,Finset.mem_univ _,rfl⟩
  · intro j _
    rfl
end ArtinCAT0.GridDisk

namespace ArtinCAT0.SixSector
open SectorMetric RayIndex
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR
lemma circleAt_index (n : ℕ) {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    (∑ j : Fin (AngularSize n), edge (shifted w (mirrorPlane (circleAt y n R j)))
      (shifted w (mirrorPlane (circleAt y n R (j+1))))) = 1 := by
  have hh := Equiv.sum_comp (angularEquiv n) (fun j => edge (shifted w (mirrorPlane (ringCircle y (n+1) R j)))
    (shifted w (mirrorPlane (ringCircle y (n+1) R (j+1)))))
  simp only [circleAt,angularEquiv_add,angularEquiv_one]
  exact hh.trans (ringCircle_index hG y hR (n+1) hR0 hw hlarge)

lemma innerLabel_index (n : ℕ) {w : ℝ} (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<(n+1:ℕ)) :
    (∑ f, face (fun i => shifted w (mirrorPlane (innerLabel y n (GridDisk.tail n (AngularSize n) (f,i)))))) = 1 := by
  rw [GridDisk.sum_index_boundary n (AngularSize n) (fun p => shifted w (mirrorPlane (innerLabel y n p)))]
  simpa only [innerLabel,Fin.val_last] using circleAt_index hG y hR n (Nat.cast_nonneg (n+1)) hw hlarge
end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C E d : ℝ} (hC : 0≤C) (hE : 0≤E) (hd : 0≤d) (hd2 : d<2)
  (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
  (hdense : ∀ x, ∃ g : TriangleGroup, dist x (g•y)≤E)
  (hdetour : ∀ R : ℝ, 0≤R → ∀ i t, t∈Set.Icc 0 1 →
    dist (axis y 0 R•y) (circle y R i t•y)≤d*R+3*C)
include hG hR hC hE hd hd2 hchart hdense hdetour

lemma cap_exists (n : ℕ) :
    ∃ v : GridDisk.Vertex n (AngularSize n) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (n+1),i)) = circleAt y n (n+1:ℕ) (-i)) ∧
      (∀ f k, dist (v (GridDisk.tail n (AngularSize n) (f,k))•y)
        (v (GridDisk.tail n (AngularSize n) (f,k+1))•y)≤22+4*C+4*E) ∧
      (∀ p, (1-d/2)*(n+1:ℕ)-5*C/2-E≤dist y (v p•y)) := by
  let R : ℝ := (n+1:ℕ)
  have hR1 : 1≤R := by dsimp [R]; exact_mod_cast (show 1≤n+1 by omega)
  have hR0 : 0≤R := by linarith
  let b : Fin (AngularSize n) → TriangleGroup := fun i => circleAt y n R (-i)
  have hstep (i) : dist (b i•y) (b (i+1)•y)≤20+C := by
    have hh := circleAt_step hG y hR hchart n hR0 (-i-1)
    have he : -i-1+1 = -i := sub_add_cancel _ _
    rw [he] at hh
    change dist (circleAt y n R (-i)•y) (circleAt y n R (-(i+1))•y)≤20+C
    rw [dist_comm]
    have hz : -(i+1) = -i-1 := by abel
    rw [hz]
    apply hh.trans
    have hRp : R ≠ 0 := by linarith
    change 20*R/R+C≤20+C
    rw [mul_div_cancel_right₀ 20 hRp]
  have hspan' (i) : dist (axis y 0 R•y) (b i•y)≤d*R+3*C :=
    hdetour R hR0 _ _ (angular_parameter _)
  have hspan (i) : dist (axis y 0 R•y) (b i•y)≤(n+1:ℕ)*(2+3*C) := by
    have hh := hspan' i
    have hmul := mul_nonneg (sub_nonneg.mpr hR1) hC
    dsimp only [R] at *
    nlinarith
  have hbase : R-C≤dist y (axis y 0 R•y) := by
    have hh := (abs_le.mp (axis_radius hG y hR hchart hR0 0)).1
    linarith
  have hb (i) : R-C≤dist y (b i•y) := by
    have hh := (abs_le.mp (ringCircle_radius hG y hR hchart (n+1) hR0 (angularEquiv n (-i)))).1
    change -(C) ≤ dist y (b i•y)-R at hh
    linarith
  obtain ⟨v,hv,he,hr⟩ := GridDisk.cone_fill (H:=n) hG.1 y (axis y 0 R) b hE
    (by linarith : 0≤20+C) (by linarith : 0≤2+3*C) (by positivity : 0≤d*R+3*C)
    hdense hstep hspan hspan' hbase hb
  refine ⟨v,hv,?_,?_⟩
  · intro f k
    exact (he f k).trans_eq (by ring)
  · intro p
    have hh := hr p
    change R-C-(d*R+3*C)/2-E≤dist y (v p•y) at hh
    dsimp only [R] at hh
    linarith

end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0
noncomputable def mirrorAt (w : ℝ) (g : TriangleGroup) : RayIndex.Point :=
  ((mirrorPlane g).1-w,(mirrorPlane g).2-w)

namespace SixSector
open SectorMetric TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
variable {F V A U : Type*} [Fintype F] [Fintype A]
  (M : TriangleMesh F V) (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)
  (z : V → TriangleGroup) (L : (Replacement.mesh M P S).SimplicialLabeling)
  (Q : F → Prop) [DecidablePred Q]

include hG hR
lemma refined_index_zero (hM : M.Exact) (hP : P.Exact)
    {C C₀ D w R : ℝ} (hw : D+1<w)
    (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
    (hmetric : ∀ f p, dist (L.vertex (Replacement.vertex M P S (f,p))•y) (z (M.tail (f,0))•y)≤C₀)
    (hmirror : ∀ f p d, |mirrorVector (L.vertex (Replacement.vertex M P S (f,p))) d-
      mirrorVector (z (M.tail (f,0))) d|≤D)
    (hinner : ∀ f, Q f → ∃ i p, 0≤p.1 ∧ 0≤p.2 ∧ z (M.tail (f,0))=chart y i p)
    (houter : ∀ f, ¬Q f → R≤dist y (z (M.tail (f,0))•y))
    (hgap : (rayLength y 0+rayLength y 1)*(w+D+2)+C+2*C₀<R) :
    (∑ f : F × A, if Q f.1 then RayIndex.occurrence (Replacement.mesh M P S) L (mirrorAt w) f else 0) = 0 := by
  apply RayIndex.localized_zero _ L (mirrorAt w) (Replacement.exact M P S hM hP) (fun f => Q f.1)
  intro f g hf hn he hg
  by_contra hng
  let b := z (M.tail (f.1,0))
  have hclose (i : Fin 3) :
      |(mirrorAt w (L.vertex ((Replacement.mesh M P S).tail (f,i)))).1-(mirrorAt w b).1|<D+1 ∧
      |(mirrorAt w (L.vertex ((Replacement.mesh M P S).tail (f,i)))).2-(mirrorAt w b).2|<D+1 := by
    have hh := mirrorPlane_close (hmirror f.1 (P.tail (f.2,i)))
    dsimp only [mirrorAt]
    simp only [sub_sub_sub_cancel_right]
    exact ⟨lt_of_le_of_lt hh.1 (by linarith),lt_of_le_of_lt hh.2 (by linarith)⟩
  have hloc := RayIndex.face_local hn (mirrorAt w b) hclose
  obtain ⟨i,p,hp,hp',hb⟩ := hinner f.1 hf
  have hb' : b=chart y i p := hb
  have hsmall : dist y (b•y)≤(rayLength y 0+rayLength y 1)*(w+D+2)+C := by
    have hx : |(mirrorPlane (chart y i p)).1-w|≤D+1 := by
      simpa only [mirrorAt,hb'] using hloc.1.le
    have hy : |(mirrorPlane (chart y i p)).2-w|≤D+1 := by
      simpa only [mirrorAt,hb'] using hloc.2.le
    rw [hb']
    have hh := chart_small hG y hR hchart i p ⟨hp,hp'⟩ hw hx hy
    convert hh using 1
    ring
  obtain ⟨j,hj⟩ := Finite.surjective_of_injective hg (L.corner f 0)
  have hv : L.vertex ((Replacement.mesh M P S).tail (f,0)) =
      L.vertex ((Replacement.mesh M P S).tail (g,j)) := by
    rw [L.vertex_tail,L.vertex_tail,he,hj]
  have hmf := hmetric f.1 (P.tail (f.2,0))
  have hmg := hmetric g.1 (P.tail (g.2,j))
  have htri := dist_triangle y (L.vertex ((Replacement.mesh M P S).tail (f,0))•y) (z (M.tail (g.1,0))•y)
  have htri' := dist_triangle y (b•y) (L.vertex ((Replacement.mesh M P S).tail (f,0))•y)
  change dist (L.vertex ((Replacement.mesh M P S).tail (f,0))•y) (b•y)≤C₀ at hmf
  change dist (L.vertex ((Replacement.mesh M P S).tail (g,j))•y) (z (M.tail (g.1,0))•y)≤C₀ at hmg
  rw [← hv] at hmg
  rw [dist_comm (b•y)] at htri'
  have ho := houter g.1 hng
  linarith

end SixSector
end ArtinCAT0
open scoped Classical
namespace ArtinCAT0.SixSector
open SectorMetric RayIndex TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR

lemma circle_refined_side {R w D : ℝ} (hR0 : 0≤R) (hw : D<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2*D+2)<R)
    (a : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1)
    {I : Type*} (v : I → TriangleGroup)
    (hv : ∀ j d, |mirrorVector (v j) d-mirrorVector (circle y R a t) d|≤D) :
    (∀ j, 0<(mirrorAt w (v j)).1+(mirrorAt w (v j)).2) ∨
      (∀ j, (mirrorAt w (v j)).1<0) ∨ (∀ j, (mirrorAt w (v j)).2≤0) := by
  have hc j := mirrorPlane_close (hv j)
  by_cases ha : a=0
  · subst a
    left
    intro j
    have hh := circle_first_sum hG y hR hR0 ht
    have hL := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
    change 0<rayLength y 0+rayLength y 1 at hL
    have hs : 2*w+2*D < (mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2 := by
      nlinarith
    have hx := (abs_le.mp (hc j).1).1
    have hy := (abs_le.mp (hc j).2).1
    dsimp only [mirrorAt]
    linarith
  · right
    rcases chart_plane_other y a ha (R*(unit (cosine y a) t).1,R*(unit (cosine y a) t).2) with hx|hy
    · left
      intro j
      have hh := (abs_le.mp (hc j).1).2
      change (mirrorPlane (circle y R a t)).1=0 at hx
      rw [hx] at hh
      dsimp only [mirrorAt]
      linarith
    · right
      intro j
      have hh := (abs_le.mp (hc j).2).2
      change (mirrorPlane (circle y R a t)).2=0 at hy
      rw [hy] at hh
      dsimp only [mirrorAt]
      linarith

lemma refined_inner_index (n : ℕ)
    (v : GridDisk.Vertex n (AngularSize n) → TriangleGroup)
    (hv : ∀ i, innerLabel y n (Sum.inl (Fin.last (n+1),i)) = v (Sum.inl (Fin.last (n+1),-i)))
    {A U : Type*} [Fintype A] (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)
    (L : (Replacement.mesh (GridSphere.mesh n (2*(n+1))) P S).SimplicialLabeling)
    {D w : ℝ} (hD : 0≤D) (hw : D<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2*D+2)<(n+1:ℕ))
    (hmirror : ∀ f p d, |mirrorVector (L.vertex (Replacement.vertex (GridSphere.mesh n (2*(n+1))) P S (f,p))) d-
      mirrorVector (GridSphere.label n (2*(n+1)) (innerLabel y n) v hv ((GridSphere.mesh n (2*(n+1))).tail (f,0))) d|≤D)
    (hcorner : ∀ f i, L.vertex (Replacement.vertex (GridSphere.mesh n (2*(n+1))) P S (f,S.point (i,0))) =
      GridSphere.label n (2*(n+1)) (innerLabel y n) v hv ((GridSphere.mesh n (2*(n+1))).tail (f,i))) :
    (∑ f : GridSphere.Face n (2*(n+1)) × A, if f.1.1=false then
      occurrence (Replacement.mesh (GridSphere.mesh n (2*(n+1))) P S) L (mirrorAt w) f else 0) = 1 := by
  let M := GridSphere.mesh n (2*(n+1))
  let z := GridSphere.label n (2*(n+1)) (innerLabel y n) v hv
  let p := fun u => mirrorAt w (L.vertex u)
  let q := fun u => mirrorAt w (z u)
  have hb (f) (i) (hf : f.1=false) (hgf : (M.mate (f,i)).1.1≠false) :
      Replacement.edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1))) := by
    rcases f with ⟨b,f⟩
    change b=false at hf
    subst b
    have hbd := (GridSphere.frontier n (2*(n+1)) (false,f) i).mp ⟨rfl,hgf⟩
    obtain ⟨j,hj⟩ := (GridDisk.boundary_iff n (AngularSize n) (f,i)).mp hbd.2
    cases hj
    apply Replacement.edgeFlux_equal M P S p q
    · intro k
      exact congrArg (mirrorAt w) (hcorner _ k)
    · let e := finProdFinEquiv.symm (angularEquiv n j)
      apply circle_refined_side hG y hR (Nat.cast_nonneg (n+1)) hw hlarge e.1 (angular_parameter e.2)
        (fun k => L.vertex (Replacement.vertex M P S ((false,GridDisk.A n (AngularSize n) (Fin.last n) j),S.point (0,k))))
      intro k d
      exact hmirror _ _ d
  have he := Replacement.region_index M P S (fun f => f.1=false) p q hb
  change (∑ f : GridSphere.Face n (2*(n+1)) × A, if f.1.1=false then
    face (fun i => p ((Replacement.mesh M P S).tail (f,i))) else 0) = 1
  rw [he,GridSphere.inner_sum]
  have hwin := innerLabel_index hG y hR n (lt_of_le_of_lt hD hw)
    (show (rayLength y 0+rayLength y 1)*(2*w+2)<(n+1:ℕ) from by
      have hL := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
      nlinarith)
  exact hwin

end ArtinCAT0.SixSector

namespace ArtinCAT0.SixSector
open SectorMetric TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

theorem no_strict_ratios (hG : GeometricAction TriangleGroup X) (y : X) : ¬StrictRatios y := by
  classical
  intro hR
  obtain ⟨C,hC,hchart⟩ := chart_uniform hG y hR
  obtain ⟨E,hE,hdense⟩ := orbit_uniformly_dense hG y
  obtain ⟨c,hc,hc1,hcos⟩ := common_cosine hG y hR
  obtain ⟨r,hr,_,_,hd2⟩ := detour_gap hc hc1
  let d : ℝ := 2*Real.sqrt (1+r^2-2*c*r)+r
  have hd : 0≤d := by dsimp [d]; positivity
  have hdetour : ∀ R : ℝ, 0≤R → ∀ i t, t∈Set.Icc 0 1 →
      dist (axis y 0 R•y) (circle y R i t•y)≤d*R+3*C := by
    intro R hR0 i t ht
    exact circle_detour hG y hR hC hchart hcos hr.le hR0 i ht
  let B := 22+4*C+4*E
  have hB : 0≤B := by dsimp [B]; positivity
  obtain ⟨K,H,hK,hlib⟩ := WordDiagram.controlled_refinement hG y B hB
  let : NeZero K := ⟨by omega⟩
  obtain ⟨C₀,D,hC₀,hD,hlib⟩ := hlib
  let w := D+2
  let a := 1-d/2
  let T := rayLength y 0+rayLength y 1
  have ha : 0<a := by dsimp [a,d]; linarith
  have hT : 0<T := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
  obtain ⟨n,hn⟩ := exists_nat_gt (max (T*(2*w+2*D+2)) ((T*(w+D+2)+C+2*C₀+5*C/2+E)/a))
  have hn1 : T*(2*w+2*D+2)<(n+1:ℕ) := by
    have hh := lt_of_le_of_lt (le_max_left (T*(2*w+2*D+2)) _) hn
    push_cast
    linarith
  have hn2 : T*(w+D+2)+C+2*C₀ < (1-d/2)*(n+1:ℕ)-5*C/2-E := by
    have hh := lt_of_le_of_lt (le_max_right (T*(2*w+2*D+2)) _) hn
    have hh' := (div_lt_iff₀ ha).mp hh
    dsimp only [a] at ha hh'
    push_cast
    nlinarith
  obtain ⟨v,hv,hve,hvr⟩ := cap_exists hG y hR hC hE hd hd2 hchart hdense hdetour n
  have hagree (i) : innerLabel y n (Sum.inl (Fin.last (n+1),i)) = v (Sum.inl (Fin.last (n+1),-i)) := by
    rw [hv]
    simp only [neg_neg,innerLabel,Fin.val_last]
  let M := GridSphere.mesh n (2*(n+1))
  let z := GridSphere.label n (2*(n+1)) (innerLabel y n) v hagree
  have hedge : ∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y)≤B := by
    apply GridSphere.edges n (2*(n+1)) (innerLabel y n) v hagree (fun g => g•y)
    · intro f i
      exact (innerLabel_edges hG y hR hC hchart n f i).trans (by dsimp [B]; linarith)
    · exact hve
  obtain ⟨L,hmetric,hmirror,hcorner⟩ := hlib _ _ M z hedge
  let P := GridDisk.patch H (3*K)
  let S := GridDisk.sides H K
  have hone := refined_inner_index hG y hR n v hagree P S L hD
    (show D<w by dsimp [w]; linarith) hn1 hmirror hcorner
  have hinner (f : GridSphere.Face n (2*(n+1))) (hf : f.1=false) :
      ∃ i p, 0≤p.1 ∧ 0≤p.2 ∧ z (M.tail (f,0))=chart y i p := by
    rcases f with ⟨b,f⟩
    change b=false at hf
    subst b
    exact innerLabel_chart hG y hR n (GridDisk.tail n (AngularSize n) (f,0))
  have houter (f : GridSphere.Face n (2*(n+1))) (hf : ¬f.1=false) :
      (1-d/2)*(n+1:ℕ)-5*C/2-E≤dist y (z (M.tail (f,0))•y) := by
    rcases f with ⟨b,f⟩
    cases b
    · exact False.elim (hf rfl)
    · exact hvr (GridDisk.tail n (AngularSize n) (f,0))
  have hzero := refined_index_zero hG y hR M P S z L (fun f => f.1=false)
    (GridSphere.exact n (2*(n+1))) (GridDisk.exact H (3*K))
    (show D+1<w by dsimp [w]; linarith) hchart hmetric hmirror hinner houter hn2
  have hs : (1:ℤ)=0 := hone.symm.trans hzero
  norm_num at hs

end ArtinCAT0.SixSector

end OAI
