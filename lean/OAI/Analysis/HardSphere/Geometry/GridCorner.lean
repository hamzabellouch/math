import Mathlib
import OAI.Analysis.HardSphere.Geometry.CenteredCircleLift
import OAI.Analysis.HardSphere.Geometry.StarGraph

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma torusDistance_lift_le_two {L : Length} {x y : Point} {b : ℝ} (hb : 0 ≤ b)
    (hxy : ∀ i, |x i - y i| ≤ b) :
    torusDistance L (liftPoint L x) (liftPoint L y) ≤ 2*b := by
  have hcoord (i : Fin 3) : dist ((x i : ℝ) : AddCircle L.val) (y i : AddCircle L.val) ≤ b := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact (QuotientAddGroup.norm_mk_le_norm (m := x i-y i)).trans (by simpa only [Real.norm_eq_abs] using hxy i)
  unfold torusDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 3, b^2 := Finset.sum_le_sum fun i _ ↦
      sq_le_sq₀ dist_nonneg hb |>.mpr (hcoord i)
    _ ≤ (2*b)^2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num only [Nat.cast_ofNat]; nlinarith [sq_nonneg b]

def gridCorner (L : Length) (h : ℝ) (z : Vertex) : Torus L :=
  liftPoint L (fun i ↦ h*(z i : ℝ)-1/2)

lemma microCube_dist_corner {L : Length} {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d)
    {z w : Vertex} (hw : ∀ i, h * |(w i : ℝ)-z i| ≤ d)
    {x : Torus L} (hx : x ∈ microCube L h w) :
    torusDistance L x (gridCorner L h z) ≤ 2*(d+h) := by
  obtain ⟨u,hu,rfl⟩ := hx
  apply torusDistance_lift_le_two (add_nonneg hd hh)
  intro i
  have hab : |h*((w i : ℝ)-z i)| ≤ d := by
    simpa only [abs_mul, abs_of_nonneg hh] using hw i
  have hl := hu.1 i
  have hr := hu.2 i
  change h*(w i : ℝ)-1/2 ≤ u i at hl
  change u i ≤ h*((w i : ℝ)+1)-1/2 at hr
  obtain ⟨ha,hb⟩ := abs_le.mp hab
  apply abs_le.mpr
  constructor <;> nlinarith

lemma microCube_dist_adjacent {L : Length} {h : ℝ} (hh : 0 ≤ h)
    {z w : Vertex} (hzw : starStep z w) {x y : Torus L}
    (hx : x ∈ microCube L h z) (hy : y ∈ microCube L h w) :
    torusDistance L x y ≤ 4*h := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  have hc := torusDistance_lift_le_two (L := L) (x := u) (y := v) (b := 2*h) (by positivity)
  rw [show 4*h = 2*(2*h) by ring]
  apply hc
  intro i
  have he : |(z i : ℝ)-w i| ≤ 1 := by exact_mod_cast hzw.2 i
  have hmul := mul_le_mul_of_nonneg_left he hh
  have hab : |h*((z i : ℝ)-w i)| ≤ h := by
    simpa only [abs_mul, abs_of_nonneg hh, mul_one] using hmul
  obtain ⟨ha,hb⟩ := abs_le.mp hab
  have huz := hu.1 i
  have huz' := hu.2 i
  have hvw := hv.1 i
  have hvw' := hv.2 i
  dsimp [liftedCube] at huz huz' hvw hvw'
  apply abs_le.mpr
  constructor <;> nlinarith

lemma adjacent_witnesses_close {n : ℕ} {L : Length} {h r : ℝ} (hh : 0 ≤ h) (hr : h ≤ r)
    (Y : Configuration n L) {z w : Vertex} (hzw : starStep z w) {i j : Fin n}
    (hi : ∃ x ∈ microCube L h z, torusDistance L x (Y i) ≤ r)
    (hj : ∃ y ∈ microCube L h w, torusDistance L y (Y j) ≤ r) :
    torusDistance L (Y i) (Y j) ≤ 6*r := by
  obtain ⟨x,hx,hxi⟩ := hi
  obtain ⟨y,hy,hyj⟩ := hj
  have hc := microCube_dist_adjacent hh hzw hx hy
  have ht := torusDistance_triangle' L (Y i) x (Y j)
  have ht' := torusDistance_triangle' L x y (Y j)
  rw [torusDistance_comm L (Y i) x] at ht
  linarith

end HardSphere.BathSlice

namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk

lemma label_boundary {α β : Type*} {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (f : α → β) {a : β} (hu : f u = a) (hv : f v ≠ a) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ f x = a ∧ f y ≠ a := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u v w huv p ih =>
    by_cases he : f v = a
    · obtain ⟨x,hx,y,hy,hxy,hfx,hfy⟩ := ih he hv
      exact ⟨x,by simp [hx],y,by simp [hy],hxy,hfx,hfy⟩
    · exact ⟨u,by simp,v,by simp [p.start_mem_support],huv,hu,he⟩

lemma each_label_has_boundary {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (f : α → β)
    (hc : 1 < (p.support.toFinset.image f).card) {a : β}
    (ha : a ∈ p.support.toFinset.image f) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ f x = a ∧ f y ≠ a := by
  obtain ⟨x,hx,hxa⟩ := Finset.mem_image.mp ha
  obtain ⟨b,hb,c,hc',hbc⟩ := Finset.one_lt_card.mp hc
  have hd : ∃ d ∈ p.support.toFinset.image f, d ≠ a := by
    by_cases he : b = a
    · exact ⟨c,hc',by simpa [he] using Ne.symm hbc⟩
    · exact ⟨b,hb,he⟩
  obtain ⟨d,hd,hda⟩ := hd
  obtain ⟨y,hy,hyd⟩ := Finset.mem_image.mp hd
  have hx' : x ∈ p.support := List.mem_toFinset.mp hx
  have hy' : y ∈ p.support := List.mem_toFinset.mp hy
  obtain ⟨q⟩ := p.connected_induce_support.preconnected ⟨x,hx'⟩ ⟨y,hy'⟩
  obtain ⟨s,_,t,_,hst,hsa,hta⟩ := _root_.OAI.SimpleGraph.Walk.label_boundary q
    (fun z ↦ f z.val) hxa (by simpa [hyd] using hda)
  exact ⟨s.val,s.property,t.val,t.property,hst,hsa,hta⟩

end SimpleGraph.Walk

namespace HardSphere.BathSlice
open HardSphere.Lattice

theorem first_exit_witnesses {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhr : h ≤ r) (hrh : r ≤ 2*h) (hr : r ≤ 1/4096)
    (hperiod : L.val = h * J) (hL : 10 < L.val)
    (Y : Configuration n L) {z w : Vertex}
    (hz : z ∈ bad h r Y) (hp : withinReach starStep (bad h r Y) z w)
    (hw : ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i|) :
    ∃ A : Finset (Fin n),
      (1:ℝ)/1372 ≤ r * A.card ∧
      (∀ i ∈ A, torusDistance L (Y i) (gridCorner L h z) ≤ 1) ∧
      (∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) := by
  classical
  obtain ⟨v,p,hlocal,ih,hspan⟩ := star_first_exit hh (by norm_num : (0:ℝ)<1/4) hz hp hw
  let S := p.support.toFinset
  have hS : ∀ x ∈ S, x ∈ bad h r Y := fun x hx ↦ (hlocal x (List.mem_toFinset.mp hx)).1
  obtain ⟨x0,hx0,j0,hj0⟩ := hz
  have hex (x : Vertex) : ∃ j : Fin n, x ∈ S →
      ∃ u ∈ microCube L h x, torusDistance L u (Y j) ≤ r := by
    by_cases hx : x ∈ S
    · obtain ⟨u,hu,j,hj⟩ := hS x hx
      exact ⟨j,fun _ ↦ ⟨u,hu,hj⟩⟩
    · exact ⟨j0,fun h ↦ (hx h).elim⟩
  choose f hf using hex
  let A := S.image f
  have hinj : Set.InjOn (torusProjection J) (↑S : Set Vertex) := by
    apply (local_projection_injective hh (d := (1:ℝ)/4+h) (z := z) ?_).mono
    · intro x hx
      exact (hlocal x (List.mem_toFinset.mp hx)).2
    · linarith
  have hcount : S.card ≤ 343*A.card := by
    apply Finset.card_le_mul_card_image S 343
    intro j _
    apply card_witness_sites_le hh hperiod hrh Y _ (hinj.mono (Finset.filter_subset _ _)) j
    intro x hx
    obtain ⟨hxS,hfx⟩ := Finset.mem_filter.mp hx
    simpa only [hfx] using hf x hxS
  have hpSpan : |(v ih : ℝ)-z ih| ≤ (S.card : ℝ)-1 := by
    have he := star_path_span p ih
    rw [abs_sub_comm] at he
    exact_mod_cast he
  have hcR : (S.card : ℝ) ≤ 343*(A.card : ℝ) := by exact_mod_cast hcount
  have hlarge : (1:ℝ)/1372 ≤ r*A.card := by
    have ht := mul_le_mul_of_nonneg_left hpSpan hh.le
    have hcount' := mul_le_mul_of_nonneg_left hcR hh.le
    have hhr' := mul_le_mul_of_nonneg_right hhr (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
    nlinarith
  have htwo : 1 < A.card := by
    by_contra hn
    have hc : (A.card : ℝ) ≤ 1 := by exact_mod_cast (show A.card ≤ 1 by omega)
    have h0 : 0 ≤ r := hh.le.trans hhr
    have ht := mul_le_mul_of_nonneg_left hc h0
    nlinarith
  refine ⟨A,hlarge,?_,?_⟩
  · intro i hi
    obtain ⟨x,hx,hxi⟩ := Finset.mem_image.mp hi
    obtain ⟨u,hu,huf⟩ := hf x hx
    rw [hxi] at huf
    have hd := microCube_dist_corner hh.le (show (0:ℝ)≤1/4+h by positivity)
      (hlocal x (List.mem_toFinset.mp hx)).2 hu
    have ht := torusDistance_triangle' L (Y i) u (gridCorner L h z)
    rw [torusDistance_comm L (Y i) u] at ht
    linarith
  · intro i hi
    obtain ⟨x,hx,y,hy,hxy,hfi,hfj⟩ := _root_.OAI.SimpleGraph.Walk.each_label_has_boundary p f htwo hi
    refine ⟨f y,Finset.mem_image.mpr ⟨y,List.mem_toFinset.mpr hy,rfl⟩,hfj,?_⟩
    rw [← hfi]
    exact adjacent_witnesses_close hh.le hhr Y hxy (hf x (List.mem_toFinset.mpr hx))
      (hf y (List.mem_toFinset.mpr hy))

end HardSphere.BathSlice

end

end OAI
