import OAI.MathematicalPhysics.Heisenberg.HullRouting

namespace OAI

noncomputable section

open scoped Classical

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents Heisenberg.LatticeHull
variable {d : ℕ}

lemma component_exit (Z : Set (Site d)) {x y : Site d} (s : Finset (Site d))
    (hx : x ∈ s) (hy : y ∈ Component Z x) (hyout : y ∉ s) :
    ∃ u ∈ s, ∃ v ∈ Component Z x, v ∉ s ∧ v ∈ Ball 8 u := by
  have hr := hy.2
  have h : y ∈ s ∨ ∃ u ∈ s, ∃ v ∈ Component Z x, v ∉ s ∧ v ∈ Ball 8 u := by
    clear hyout
    induction hr with
    | refl => exact Or.inl hx
    | @tail u v hxu huv ih =>
      rcases ih ⟨huv.2.1,hxu⟩ with hu | he
      · by_cases hv : v ∈ s
        · exact Or.inl hv
        · exact Or.inr ⟨u,hu,v,⟨huv.2.2,hxu.tail huv⟩,hv,huv.1⟩
      · exact Or.inr he
  exact h.resolve_left hyout

lemma component_witness (Z : Set (Site d)) (hZ : Z.Finite) {x : Site d} (hx : x ∈ Z)
    (n : ℕ) (hn : n+1 ≤ (component_finite Z hZ x).toFinset.card) :
    ∃ s : Finset (Site d), x ∈ s ∧ s.card = n+1 ∧
      (∀ z ∈ s, z ∈ Component Z x) ∧ ∀ z ∈ s, z ∈ Ball (8*(n : ℤ)) x := by
  induction n with
  | zero =>
    refine ⟨{x},by simp,by simp,?_,?_⟩
    · intro z hz; simpa only [Finset.mem_singleton.mp hz] using self_mem_component Z hx
    · intro z hz; rw [Finset.mem_singleton.mp hz]; exact ball_self (by omega) x
  | succ n ih =>
    obtain ⟨s,hxs,hcard,hsC,hsball⟩ := ih (by omega)
    have hns : ¬ (component_finite Z hZ x).toFinset ⊆ s := by
      intro hsub
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨y,hyC,hys⟩ := Finset.not_subset.mp hns
    obtain ⟨u,hus,v,hvC,hvs,hvu⟩ := component_exit Z s hxs
      ((component_finite Z hZ x).mem_toFinset.mp hyC) hys
    refine ⟨insert v s,Finset.mem_insert_of_mem hxs,by simp [hvs,hcard],?_,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hvC
      · exact hsC z hz
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [Nat.cast_succ,mul_add,mul_one] using ball_triangle (hsball u hus) hvu
      · exact ball_mono (by push_cast; omega) x (hsball z hz)

theorem small_component_of_local_count (Z : Set (Site d)) (hZ : Z.Finite)
    {x : Site d} (hx : x ∈ Z) (N : ℕ) (hN : 1 ≤ N)
    (hcount : (hZ.toFinset.filter (fun z => z ∈ Ball (8*((N-1 : ℕ) : ℤ)) x)).card < N) :
    (component_finite Z hZ x).toFinset.card < N := by
  by_contra h
  have hlarge : (N-1)+1 ≤ (component_finite Z hZ x).toFinset.card := by omega
  obtain ⟨s,_,hcard,hsC,hsB⟩ := component_witness Z hZ hx (N-1) hlarge
  have hs : s ⊆ hZ.toFinset.filter (fun z => z ∈ Ball (8*((N-1 : ℕ) : ℤ)) x) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨hZ.mem_toFinset.mpr (hsC z hz).1,hsB z hz⟩
  have hc := Finset.card_le_card hs
  have hlt : s.card < N := lt_of_le_of_lt hc hcount
  omega

theorem component_radius (Z : Set (Site d)) (hZ : Z.Finite)
    {x : Site d} (hx : x ∈ Z) :
    Component Z x ⊆ Ball (8*(((component_finite Z hZ x).toFinset.card-1 : ℕ) : ℤ)) x := by
  let C := (component_finite Z hZ x).toFinset
  have hpos : 1 ≤ C.card := by
    apply Finset.one_le_card.mpr
    exact ⟨x,(component_finite Z hZ x).mem_toFinset.mpr (self_mem_component Z hx)⟩
  obtain ⟨s,_,hcard,hsC,hsB⟩ := component_witness Z hZ hx (C.card-1) (by change C.card-1+1 ≤ C.card; omega)
  have hs : s ⊆ C := fun z hz => (component_finite Z hZ x).mem_toFinset.mpr (hsC z hz)
  have he : s = C := Finset.eq_of_subset_of_card_le hs (by omega)
  intro z hz
  apply hsB z
  rw [he]
  exact (component_finite Z hZ x).mem_toFinset.mpr hz

end Heisenberg.LatticeRegular

namespace Heisenberg.Geometry
lemma dist_le_iff_mem_ball {d r : ℕ} (x y : Site d) :
    dist x y ≤ (r:ℝ) ↔ y ∈ Ball r x := by
  rw [dist_pi_le_iff (by positivity)]
  change (∀ j, dist (x j) (y j) ≤ (r:ℝ)) ↔ ∀ j, |y j-x j| ≤ (r:ℤ)
  simp only [Int.dist_eq', abs_sub_comm (x _) (y _)]
  exact forall_congr' (fun j => by exact_mod_cast (Iff.rfl :
    ((|y j-x j|:ℤ):ℝ) ≤ (r:ℝ) ↔ ((|y j-x j|:ℤ):ℝ) ≤ (r:ℝ)))

lemma step_dist_le_one {d : ℕ} {u v : Site d} (h : Step u v) : dist u v ≤ 1 := by
  simpa only [Nat.cast_one] using (dist_le_iff_mem_ball (r:=1) u v).mpr (step_ball_one h)
end Heisenberg.Geometry

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents
variable {d : ℕ}

def Regular (Z : Set (Site d)) (x : Site d) (R M : ℕ) (ν : ℝ) : Prop :=
  (∀ z ∈ Ball (11*R : ℕ) x, ((ballFinset d M z).filter (· ∈ Z)).card < 2*d) ∧
  (∀ z ∈ Z, z ∉ Ball (10*R : ℕ) x → ∀ w ∈ Component Z z,
    dist z w ≤ (1+dist z x)^ν)

theorem regular_component_envelope (hd : 1 ≤ d) (Z : Set (Site d)) (hZ : Z.Finite)
    (x y : Site d) (R M : ℕ) (hM : 8*(2*d) ≤ M) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hy : y ∈ Ball (R:ℤ) x)
    (hreg : Regular Z x R M ν) :
    ∀ z ∈ Z, ∀ w ∈ Component Z z,
      dist z w ≤ (16*(d:ℝ)+2)*(1+dist z y)^ν := by
  intro z hz w hw
  have hp : 1 ≤ (1+dist z y)^ν := Real.one_le_rpow (by linarith [dist_nonneg (x:=z) (y:=y)]) hν0
  by_cases hnear : z ∈ Ball (10*R : ℕ) x
  · have hz11 : z ∈ Ball (11*R : ℕ) x := ball_mono (by omega) x hnear
    have hcount : (hZ.toFinset.filter (fun w => w ∈ Ball (8*((2*d-1 : ℕ):ℤ)) z)).card < 2*d := by
      apply lt_of_le_of_lt (Finset.card_le_card ?_) (hreg.1 z hz11)
      intro a ha
      obtain ⟨haZ,haB⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨(mem_ballFinset ..).mpr ?_,hZ.mem_toFinset.mp haZ⟩
      apply ball_mono _ z haB
      have hh : 8*(2*d-1) ≤ M := (Nat.mul_le_mul_left 8 (Nat.sub_le ..)).trans hM
      exact_mod_cast hh
    have hc := small_component_of_local_count Z hZ hz (2*d) (by omega) hcount
    have hb := component_radius Z hZ hz hw
    have hb' : w ∈ Ball (16*d : ℕ) z := by
      apply ball_mono _ z hb
      have : 8*((component_finite Z hZ z).toFinset.card-1) ≤ 16*d := by omega
      exact_mod_cast this
    have hdist := (dist_le_iff_mem_ball z w).mpr hb'
    have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg _
    push_cast at hdist
    have := mul_le_mul_of_nonneg_left hp (show 0 ≤ 16*(d:ℝ)+2 by positivity)
    nlinarith
  · have hremote := hreg.2 z hz hnear w hw
    have hfar : (10*R:ℕ) < dist x z := lt_of_not_ge (mt (dist_le_iff_mem_ball x z).mp hnear)
    have hxy : dist x y ≤ (R:ℝ) := (dist_le_iff_mem_ball x y).mpr hy
    have hzx : dist z x ≤ dist z y + (R:ℝ) := by
      have h := dist_triangle z y x
      rw [dist_comm y x] at h
      linarith
    have hcmp : 1+dist z x ≤ 2*(1+dist z y) := by
      rw [dist_comm x z] at hfar
      push_cast at hfar
      linarith [Nat.cast_nonneg (α:=ℝ) R]
    have hpow : (1+dist z x)^ν ≤ 2*(1+dist z y)^ν := by
      calc
        _ ≤ (2*(1+dist z y))^ν := Real.rpow_le_rpow (by positivity) hcmp hν0
        _ = (2:ℝ)^ν*(1+dist z y)^ν := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2*(1+dist z y)^ν := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hν1.le) (Real.rpow_nonneg (by positivity) _)
    exact hremote.trans (hpow.trans (mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) d])
      (Real.rpow_nonneg (by positivity) _)))

end Heisenberg.LatticeRegular

open scoped Classical
open Filter Topology
namespace Heisenberg.RoutingDecay

lemma eventually_half {ν C : ℝ} (hν : ν < 1) :
    ∃ T ≥ 1, ∀ t ≥ T, C*t^ν ≤ t/2 := by
  have hlim : Tendsto (fun t : ℝ => C*t^(ν-1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hν)).const_mul C
    simpa only [neg_sub,mul_zero] using h
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max 1 T,le_max_left ..,?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left ..).trans ht
  have hsmall := hT t ((le_max_right ..).trans ht)
  have he : t^ν = t^(ν-1)*t := by
    calc
      t^ν = t^((ν-1)+1) := by congr 1; ring
      _ = t^(ν-1)*t := by rw [Real.rpow_add (by linarith : 0<t),Real.rpow_one]
  rw [he]
  nlinarith

theorem comparable_radii {ν C : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ K ≥ 1, ∀ h t : ℝ, 0 ≤ h → 0 ≤ t →
      |h-t| ≤ C*(1+t)^ν →
      (1+t ≤ K*(1+h)) ∧ (1+h ≤ K*(1+t)) ∧
      C*(1+t)^ν ≤ (C*K^ν)*(1+h)^ν := by
  obtain ⟨T,hT,htail⟩ := eventually_half (C:=C) hν1
  let K := max (max 2 T) (C+1)
  have hK2 : 2 ≤ K := (le_max_left 2 T).trans (le_max_left ..)
  have hKT : T ≤ K := (le_max_right 2 T).trans (le_max_left ..)
  have hKC : C+1 ≤ K := le_max_right ..
  refine ⟨K,by linarith,?_⟩
  intro h t hh ht he
  have hab := abs_le.mp he
  have hlow : 1+t ≤ K*(1+h) := by
    by_cases hlarge : T ≤ 1+t
    · have hhalf := htail (1+t) hlarge
      have hrel : 1+t ≤ 2*(1+h) := by linarith
      exact hrel.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))
    · have hsmall : 1+t ≤ K := (le_of_lt (lt_of_not_ge hlarge)).trans hKT
      exact hsmall.trans ((le_mul_iff_one_le_right (by linarith : 0<K)).mpr (by linarith))
  have hp : (1+t)^ν ≤ 1+t := Real.rpow_le_self_of_one_le (by linarith) hν1.le
  have hupp : 1+h ≤ K*(1+t) := by
    have hc := mul_le_mul_of_nonneg_left hp hC
    have hk := mul_le_mul_of_nonneg_right hKC (by linarith : 0≤1+t)
    nlinarith
  refine ⟨hlow,hupp,?_⟩
  calc
    _ ≤ C*(K*(1+h))^ν := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hlow hν0) hC
    _ = _ := by rw [Real.mul_rpow (by linarith) (by linarith)]; ring

variable {V : Type*} [PseudoMetricSpace V]

theorem neighborhood_displacement {ν C : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 1 ≤ C) :
    ∃ D ≥ 1, ∀ y u q c z : V,
      dist u q ≤ 1 →
      dist q c + 1 ≤ C*(1+dist c y)^ν →
      dist z c ≤ C*(1+dist c y)^ν →
      dist u z ≤ D*(1+dist u y)^ν := by
  obtain ⟨K,hK,hcomp⟩ := comparable_radii hν0 hν1 (by linarith : 0 ≤ C)
  let D := 2*(C*K^ν)
  have hKp : 1 ≤ K^ν := Real.one_le_rpow hK hν0
  have hCK : 1 ≤ C*K^ν := one_le_mul_of_one_le_of_one_le hC hKp
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro y u q c z huq hqc hzc
  have huc : dist u c ≤ C*(1+dist c y)^ν :=
    (dist_triangle u q c).trans (by linarith)
  have hab : |dist u y-dist c y| ≤ C*(1+dist c y)^ν :=
    (abs_dist_sub_le u c y).trans huc
  have hp := (hcomp (dist u y) (dist c y) dist_nonneg dist_nonneg hab).2.2
  calc
    dist u z ≤ dist u c + dist c z := dist_triangle ..
    _ ≤ 2*(C*(1+dist c y)^ν) := by rw [dist_comm c z]; linarith
    _ ≤ 2*((C*K^ν)*(1+dist u y)^ν) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = D*(1+dist u y)^ν := by dsimp [D]; ring

theorem inverse_displacement {ν D : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hD : 0 ≤ D) :
    ∃ (K : ℝ), 1 ≤ K ∧ ∀ y u v : V,
      dist u v ≤ D*(1+dist u y)^ν →
      1+dist v y ≤ K*(1+dist u y) ∧
      dist u v ≤ (D*K^ν)*(1+dist v y)^ν := by
  obtain ⟨K,hK,hcomp⟩ := comparable_radii hν0 hν1 hD
  refine ⟨K,hK,?_⟩
  intro y u v huv
  have hab : |dist v y-dist u y| ≤ D*(1+dist u y)^ν := by
    exact (abs_dist_sub_le v u y).trans (by simpa only [dist_comm v u] using huv)
  have h := hcomp (dist v y) (dist u y) dist_nonneg dist_nonneg hab
  exact ⟨h.2.1,huv.trans h.2.2⟩

end Heisenberg.RoutingDecay

end

end OAI
