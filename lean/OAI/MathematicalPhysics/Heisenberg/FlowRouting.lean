import OAI.MathematicalPhysics.Heisenberg.LatticeFlows

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

theorem lattice_flow_finite_energy {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun e : Fin (k + 1) × ZSite k => latticeFlow e.2 e.1 ^ 2) := by
  apply Heisenberg.LatticeSum.finite_energy_of_envelope
    (fun e => latticeFlow e.2 e.1) 0 (k.factorial : ℝ) (k : ℝ) (by positivity)
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  · intro e
    have h := lattice_flow_envelope e.2 e.1
    simp only [sub_zero]
    change |latticeFlow e.2 e.1| ≤ (k.factorial : ℝ) *
      ((radius e.2 : ℝ) + 1) ^ (-(k : ℝ))
    rw [Real.rpow_neg (by positivity : 0 ≤ (radius e.2 : ℝ) + 1),
      Real.rpow_natCast]
    simpa only [div_eq_mul_inv] using h

open RoutedFlow
variable {k : ℕ}

def next (x : ZSite k) (j : Fin (k+1)) : ZSite k := Function.update x j (x j+1)

@[simp] lemma next_down (x : ZSite k) (j : Fin (k+1)) : next (down x j) j = x := by
  ext i
  by_cases hi : i=j <;> simp [next,down,hi]

@[simp] lemma down_next (x : ZSite k) (j : Fin (k+1)) : down (next x j) j = x := by
  ext i
  by_cases hi : i=j <;> simp [next,down,hi]

lemma next_ne (x : ZSite k) (j : Fin (k+1)) : next x j ≠ x := by
  intro h
  have hj := congrFun h j
  simp [next] at hj

lemma down_ne (x : ZSite k) (j : Fin (k+1)) : down x j ≠ x := by
  intro h
  have hj := congrFun h j
  simp [down] at hj

def latticeNetwork (k : ℕ) : Network (ZSite k) (ZSite k × Fin (k+1)) where
  src e := e.1
  dst e := next e.1 e.2
  incidentFinite v := by
    apply ((Set.finite_range (fun j : Fin (k+1) => (v,j))).union
      (Set.finite_range (fun j : Fin (k+1) => (down v j,j)))).subset
    rintro ⟨x,j⟩ (h|h)
    · change x = v at h
      exact Or.inl ⟨j,by rw [h]⟩
    · change next x j = v at h
      exact Or.inr ⟨j,by dsimp; rw [← h,down_next]⟩

lemma incident_set (v : ZSite k) :
    ((latticeNetwork k).incidentFinite v).toFinset =
      (Finset.univ.image (fun j => (v,j))) ∪ (Finset.univ.image (fun j => (down v j,j))) := by
  ext ⟨x,j⟩
  simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,latticeNetwork,Finset.mem_union,
    Finset.mem_image,Finset.mem_univ,true_and,Prod.mk.injEq]
  constructor
  · rintro (h|h)
    · exact Or.inl ⟨j,h.symm,rfl⟩
    · exact Or.inr ⟨j,by rw [← h,down_next],rfl⟩
  · rintro (⟨i,h,rfl⟩|⟨i,h,rfl⟩)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h,next_down])

lemma incident_disjoint (v : ZSite k) :
    Disjoint (Finset.univ.image (fun j : Fin (k+1) => (v,j)))
      (Finset.univ.image (fun j : Fin (k+1) => (down v j,j))) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hf
  have hji := congrArg Prod.snd hj
  change j = i at hji
  subst j
  exact down_ne v i (congrArg Prod.fst hj)

lemma latticeNetwork_divergence (F : ZSite k × Fin (k+1) → ℝ) (v : ZSite k) :
    (latticeNetwork k).divergence F v =
      (∑ j, F (v,j)) - ∑ j, F (down v j,j) := by
  rw [Network.divergence,incident_set,Finset.sum_union (incident_disjoint v)]
  rw [Finset.sum_image (by intro i _ j _ h; exact congrArg Prod.snd h),
    Finset.sum_image (by intro i _ j _ h; exact congrArg Prod.snd h)]
  simp [Network.boundary,latticeNetwork,next_ne,down_ne,sub_eq_add_neg]

theorem latticeNetwork_unit :
    (latticeNetwork k).UnitFlow (fun e => latticeFlow e.1 e.2) 0 := by
  apply Network.unit_of_divergence
  intro v
  rw [latticeNetwork_divergence]
  by_cases hv : v = 0 <;> simpa [hv] using lattice_divergence v

end Heisenberg.Flow

namespace Heisenberg.Geometry
lemma lattice_neighbor_finite {d : ℕ} (U : Set (Site d)) (v : Site d) :
    ((latticeGraph U).neighborSet v).Finite := by
  apply (ballFinset d 1 v).finite_toSet.subset
  intro z hz
  apply (mem_ballFinset ..).mpr
  apply (dist_le_iff_mem_ball v z).mp
  simpa only [Nat.cast_one] using step_dist_le_one hz.1
end Heisenberg.Geometry

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.HullRouting Heisenberg.RoutedFlow
variable {k : ℕ}

lemma next_step (x : ZSite k) (j : Fin (k+1)) : Step x (next x j) := by
  refine ⟨j,Or.inl ?_,?_⟩
  · simp [next]
  · intro i hi
    simp [next,hi]

lemma down_sub (x y : ZSite k) (j : Fin (k+1)) : down x j-y = down (x-y) j := by
  ext i
  by_cases hi : i=j <;> simp [down,hi]
  omega

lemma translated_unit (y : ZSite k) :
    (latticeNetwork k).UnitFlow (fun e => latticeFlow (e.1-y) e.2) y := by
  apply Network.unit_of_divergence
  intro v
  rw [latticeNetwork_divergence]
  simp_rw [down_sub]
  have h := lattice_divergence (v-y)
  by_cases hv : v = y <;> simpa [sub_eq_zero,hv] using h

theorem routed_lattice (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ A ≥ 0, ∃ K ≥ 1, ∃ D ≥ 1, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ ψ : ZSite k → ZSite k,
        (∀ u, ψ u ∉ Z) ∧ (∀ u, dist u (ψ u) ≤ D*(1+dist u y)^ν) ∧ (∀ w, (ψ ⁻¹' {w}).Finite) ∧
        ∃ R : Routing (latticeNetwork k) (graphNetwork (latticeGraph Zᶜ)
          (lattice_neighbor_finite Zᶜ)) ψ,
          (∀ e t, |R.current e t| ≤ 1) ∧
          (∀ t, ((R.locallyFinite t).toFinset.card : ℝ) ≤
            (k+1:ℝ)*(2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^ (k+1)) ∧
          (∀ e t, R.current e t ≠ 0 → 1+dist t.fst y ≤ K*(1+dist e.1 y)) ∧
          (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow
            (R.push (fun e => latticeFlow (e.1-y) e.2)) (ψ y) := by
  obtain ⟨D,hD,hroutes⟩ := radial_routing (d:=k+1) (by omega) ν C hν0 hν1 hC
  obtain ⟨K,hK,hreverse⟩ := RoutingDecay.inverse_displacement (V:=ZSite k) hν0 hν1 (by linarith : 0≤D)
  let A := D*K^ν
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,hA,K,hK,D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨ψ,hψ,hfib,hP⟩ := hroutes Z hZ y hcomp
  choose P hsimple hdisp using fun e : ZSite k × Fin (k+1) => hP e.1 (next e.1 e.2) (next_step e.1 e.2)
  have hinverse (e : ZSite k × Fin (k+1)) (t : (latticeGraph Zᶜ).Dart) (ht : t ∈ (P e).darts) :
      1+dist t.fst y ≤ K*(1+dist e.1 y) ∧ dist e.1 t.fst ≤ A*(1+dist t.fst y)^ν :=
    hreverse y e.1 t.fst (hdisp e t.fst ((P e).dart_fst_mem_support_of_mem_darts ht))
  let B (t : (latticeGraph Zᶜ).Dart) :=
    (ballFinset (k+1) ⌈A*(1+dist t.fst y)^ν⌉₊ t.fst) ×ˢ (Finset.univ : Finset (Fin (k+1)))
  have hB (e : ZSite k × Fin (k+1)) (t : (latticeGraph Zᶜ).Dart) (ht : t ∈ (P e).darts) : e ∈ B t := by
    apply Finset.mem_product.mpr
    refine ⟨(mem_ballFinset ..).mpr ((dist_le_iff_mem_ball ..).mp ?_),Finset.mem_univ _⟩
    rw [dist_comm]
    exact (hinverse e t ht).2.trans (Nat.le_ceil _)
  have hfin (t : (latticeGraph Zᶜ).Dart) : {e | t ∈ (P e).darts}.Finite :=
    (B t).finite_toSet.subset (fun e he => hB e t he)
  let R := routingOfPaths (lattice_neighbor_finite Zᶜ) (latticeNetwork k) ψ P hfin
  refine ⟨ψ,hψ,?_,hfib,R,?_,?_,?_,?_⟩
  · intro u
    exact hdisp (u,0) (ψ u) (P (u,0)).start_mem_support
  · exact routingOfPaths_abs_le_one _ _ _ _ _ (fun e => (hsimple e).isTrail)
  · intro t
    have hsub : (R.locallyFinite t).toFinset ⊆ B t := by
      intro e he
      have h : R.current e t ≠ 0 := (R.locallyFinite t).mem_toFinset.mp he
      apply hB e t
      exact (pathCurrent_ne_zero_iff (P e) t).mp h
    have hc := Finset.card_le_card hsub
    have hbcard : (B t).card = (2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^(k+1)*(k+1) := by
      dsimp [B]
      rw [Finset.card_product,ballFinset_card,Finset.card_univ,Fintype.card_fin]
    rw [hbcard] at hc
    rw [mul_comm] at hc
    exact_mod_cast hc
  · intro e t ht
    apply (hinverse e t ((pathCurrent_ne_zero_iff (P e) t).mp ht)).1
  · exact R.push_unit hfib _ _ (translated_unit y)

end

open Heisenberg.RoutedFlow Heisenberg.Geometry
variable {k : ℕ}

lemma radius_eq_norm (x : ZSite k) : (radius x : ℝ) = ‖x‖ := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty) (fun j : Fin (k+1) => (x j).natAbs)
    change ((Finset.univ.sup (fun j => (x j).natAbs) : ℕ) : ℝ) ≤ ‖x‖
    rw [he]
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using norm_le_pi_norm x j
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have h : (x j).natAbs ≤ radius x := Finset.le_sup (f:=fun j => (x j).natAbs) (Finset.mem_univ j)
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast h)

lemma lattice_flow_dist_bound (x y : ZSite k) (j : Fin (k+1)) :
    |latticeFlow (x-y) j| ≤ (k.factorial : ℝ) / (1+dist x y)^k := by
  simpa only [radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using lattice_flow_envelope (x-y) j

lemma congestion_bound (d : ℕ) {A ν r : ℝ} (hA : 0 ≤ A) (hν : 0 ≤ ν) (hr : 1 ≤ r) :
    (d:ℝ)*(2*⌈A*r^ν⌉₊+1)^d ≤ ((d:ℝ)*(2*A+3)^d)*r^((d:ℝ)*ν) := by
  have hp : 1 ≤ r^ν := Real.one_le_rpow hr hν
  have hn := Nat.ceil_lt_add_one (show 0 ≤ A*r^ν by positivity)
  have hbase : 2*(⌈A*r^ν⌉₊:ℝ)+1 ≤ (2*A+3)*r^ν := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(⌈A*r^ν⌉₊:ℝ)+1) hbase d
  have he : ((2*A+3)*r^ν)^d = (2*A+3)^d*r^((d:ℝ)*ν) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (r^ν),← Real.rpow_mul (by linarith : 0≤r),mul_comm ν]
  rw [he] at hpow
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg d)

lemma inverse_power_bound {K q r : ℝ} (_hk : 0 ≤ K) (hq : 0 < q) (hr : 0 < r)
    (h : r ≤ K*q) (n : ℕ) : 1/q^n ≤ K^n/r^n := by
  rw [div_le_div_iff₀ (pow_pos hq n) (pow_pos hr n),one_mul]
  simpa only [mul_pow] using pow_le_pow_left₀ hr.le h n

theorem routed_envelope (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ B ≥ 0, ∃ D ≥ 1, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ a, a ∉ Z ∧ dist y a ≤ D ∧ ∃ J : (latticeGraph Zᶜ).Dart → ℝ,
        (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J a ∧
        ∀ t, |J t| ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
  obtain ⟨A,hA,K,hK,D,hD,hroute⟩ := routed_lattice hk ν C hν0 hν1 hC
  let B := ((k+1:ℝ)*(2*A+3)^(k+1))*((k.factorial:ℝ)*K^k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨ψ,hψ,hψdist,_hfib,R,hcur,hcount,hcompare,hunit⟩ := hroute Z hZ y hcomp
  refine ⟨ψ y,hψ y,by simpa using hψdist y,R.push (fun e => latticeFlow (e.1-y) e.2),hunit,?_⟩
  intro t
  let r := 1+dist t.fst y
  have hr : 1 ≤ r := by dsimp [r]; linarith [dist_nonneg (x:=t.fst) (y:=y)]
  let F := (k.factorial:ℝ)*K^k/r^k
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFe (e : ZSite k × Fin (k+1)) (he : R.current e t ≠ 0) : |latticeFlow (e.1-y) e.2| ≤ F := by
    have hq : 0 < 1+dist e.1 y := by linarith [dist_nonneg (x:=e.1) (y:=y)]
    have hi := inverse_power_bound (by linarith : 0≤K) hq (by linarith : 0<r) (hcompare e t he) k
    have hi' := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg k.factorial)
    exact (lattice_flow_dist_bound e.1 y e.2).trans (by simpa only [F,div_eq_mul_inv,mul_assoc,one_mul] using hi')
  calc
    |R.push (fun e => latticeFlow (e.1-y) e.2) t| ≤ ((R.locallyFinite t).toFinset.card:ℝ)*F :=
      R.abs_push_le _ t F hF hFe (fun e => hcur e t)
    _ ≤ ((k+1:ℝ)*(2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^(k+1))*F := mul_le_mul_of_nonneg_right (hcount t) hF
    _ ≤ (((k+1:ℝ)*(2*A+3)^(k+1))*r^((k+1:ℝ)*ν))*F :=
      mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add,Nat.cast_one,r] using congestion_bound (k+1) hA hν0 hr) hF
    _ = B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
      dsimp [B,F,r]
      rw [Real.rpow_sub (by positivity),Real.rpow_natCast]
      ring

end Heisenberg.Flow

end

end OAI
