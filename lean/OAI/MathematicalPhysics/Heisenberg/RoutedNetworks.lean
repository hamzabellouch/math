import OAI.MathematicalPhysics.Heisenberg.RegularComponents

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents
variable {d : ℕ}

theorem radial_hull_bounds (hd : 2 ≤ d) (Z : Set (Site d)) (hZ : Z.Finite)
    (y : Site d) (ν C : ℝ) (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hcomp : ∀ z ∈ Z, ∀ w ∈ Component Z z, dist z w ≤ C*(1+dist z y)^ν) :
    ∃ (b : Site d) (c : Set (Site d) → Site d) (r : Set (Site d) → ℕ),
      b ∉ Thick 4 Z ∧
      ∀ H ∈ maxHulls Z hZ b,
        H ⊆ Ball (r H : ℤ) (c H) ∧
        (r H : ℝ)+1 ≤ (C+6)*(1+dist (c H) y)^ν := by
  let ρ (z : Site d) : ℕ := ⌈C*(1+dist z y)^ν⌉₊+4
  have hrad (z : Site d) : (ρ z : ℝ)+1 ≤ (C+6)*(1+dist z y)^ν := by
    have hp : 1 ≤ (1+dist z y)^ν := Real.one_le_rpow (by linarith [dist_nonneg (x:=z) (y:=y)]) hν
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ C*(1+dist z y)^ν from mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    dsimp [ρ]
    push_cast
    nlinarith
  have hthick (z : Site d) (hz : z ∈ Z) : Thick 4 (Component Z z) ⊆ Ball (ρ z : ℤ) z := by
    rintro w ⟨a,ha,hwa⟩
    have haB : a ∈ Ball (⌈C*(1+dist z y)^ν⌉₊ : ℤ) z :=
      (dist_le_iff_mem_ball z a).mp ((hcomp z hz a ha).trans (Nat.le_ceil _))
    simpa only [ρ,Nat.cast_add,Nat.cast_ofNat] using ball_triangle haB hwa
  let U : Set (Site d) := ⋃ z ∈ Z, Ball (ρ z : ℤ) z
  have hU : U.Finite := hZ.biUnion (fun z _ => ball_finite (ρ z) z)
  obtain ⟨N,hN⟩ := finite_contained_box U hU
  let b : Site d := fun _ => (N:ℤ)+1
  have hbN : b ∉ Box (N:ℤ) := by
    intro h
    have h0 := h ⟨0,by omega⟩
    simp only [b,abs_of_nonneg (by positivity : (0:ℤ) ≤ (N:ℤ)+1)] at h0
    omega
  have hb (z : Site d) (hz : z ∈ Z) : b ∉ Ball (ρ z : ℤ) z := by
    intro h
    apply hbN (hN ?_)
    exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,h⟩⟩
  have hbZ : b ∉ Thick 4 Z := by
    rintro ⟨z,hz,hbz⟩
    apply hb z hz
    exact ball_mono (by dsimp [ρ]; omega) z hbz
  have hroot : ∀ H ∈ maxHulls Z hZ b, ∃ z ∈ Z, Hull (Thick 4 (Component Z z)) b = H := by
    intro H hH
    exact (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
  let c (H : Set (Site d)) : Site d := if h : H ∈ maxHulls Z hZ b then (hroot H h).choose else 0
  have hc (H : Set (Site d)) (hH : H ∈ maxHulls Z hZ b) :
      c H ∈ Z ∧ Hull (Thick 4 (Component Z (c H))) b = H := by
    simpa only [c,dite_eq_left hH] using (hroot H hH).choose_spec
  refine ⟨b,c,fun H => ρ (c H),hbZ,?_⟩
  intro H hH
  refine ⟨?_,hrad (c H)⟩
  simpa only [(hc H hH).2] using hull_subset_ball hd _ _ _ (by positivity) (hthick _ (hc H hH).1) (hb _ (hc H hH).1)

lemma collapse_finite_fibers (F : Finset (Set (Site d))) (rep : Set (Site d) → Site d)
    (hfin : ∀ H ∈ F, H.Finite) (w : Site d) : (collapse F rep ⁻¹' {w}).Finite := by
  apply ((F.finite_toSet.biUnion hfin).union (Set.finite_singleton w)).subset
  intro z hz
  by_cases h : ∃ H ∈ F, z ∈ H
  · obtain ⟨H,hH,hzH⟩ := h
    exact Or.inl (Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,hzH⟩⟩)
  · exact Or.inr (by simpa only [Set.mem_preimage,Set.mem_singleton_iff,collapse_free rep h] using hz)

end Heisenberg.HullRouting

namespace Heisenberg.Geometry
lemma walk_support_mem {d : ℕ} {U : Set (Site d)} {u v : Site d}
    (p : (latticeGraph U).Walk u v) (hu : u ∈ U) : ∀ z ∈ p.support, z ∈ U := by
  induction p with
  | nil => simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using (fun z hz => hz ▸ hu)
  | @cons u v w huv p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih huv.2.2 z hz
end Heisenberg.Geometry

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents
variable {d : ℕ}

lemma collapse_mem_region (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (rep c : Set (Site d) → Site d) (r : Set (Site d) → ℕ)
    (hrep : ∀ H ∈ F, rep H ∈ Boundary H)
    (hbound : ∀ H ∈ F, H ⊆ Ball (r H:ℤ) (c H))
    (hsurvive : ∀ u, collapse F rep u ∉ Z) (u v : Site d) :
    collapse F rep u ∈ RouteRegion Z F (fun H => Ball ((r H:ℤ)+1) (c H)) u v := by
  refine ⟨?_,hsurvive u⟩
  by_cases h : ∃ H ∈ F, u ∈ H
  · unfold collapse
    rw [dite_eq_left h]
    exact Or.inr (Or.inr ⟨h.choose,h.choose_spec.1,Or.inl h.choose_spec.2,
      boundary_subset_ball _ _ _ (hbound _ h.choose_spec.1) (hrep _ h.choose_spec.1)⟩)
  · exact Or.inl (collapse_free rep h)

theorem radial_routing (hd : 2 ≤ d) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ D ≥ 1, ∀ (Z : Set (Site d)) (_hZ : Z.Finite) (y : Site d),
      (∀ z ∈ Z, ∀ w ∈ Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ ψ : Site d → Site d,
        (∀ u, ψ u ∉ Z) ∧ (∀ w, (ψ ⁻¹' {w}).Finite) ∧
        ∀ u v, Step u v → ∃ p : (latticeGraph Zᶜ).Walk (ψ u) (ψ v),
          p.IsPath ∧ ∀ z ∈ p.support, dist u z ≤ D*(1+dist u y)^ν := by
  obtain ⟨D,hD,hdisp⟩ := RoutingDecay.neighborhood_displacement (V:=Site d) hν0 hν1 (show 1 ≤ C+6 by linarith)
  refine ⟨D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨b,c,r,hb,hbound⟩ := radial_hull_bounds hd Z hZ y ν C hν0 hC hcomp
  obtain ⟨rep,hrep,hsurvive,hpaths⟩ := finite_hull_routing Z hZ b hb
  let F := maxHulls Z hZ b
  let ψ := collapse F rep
  refine ⟨ψ,hsurvive,?_,?_⟩
  · apply collapse_finite_fibers
    intro H hH
    exact (ball_finite (r H) (c H)).subset (hbound H hH).1
  · intro u v huv
    let U := RouteRegion Z F (fun H => Ball ((r H:ℤ)+1) (c H)) u v
    obtain ⟨p,hp⟩ := hpaths c (fun H => r H) (fun H hH => (hbound H hH).1) u v huv
    have hG : latticeGraph U ≤ latticeGraph Zᶜ := by
      intro a b hab
      exact ⟨hab.1,hab.2.1.2,hab.2.2.2⟩
    refine ⟨p.mapLe hG,hp.mapLe hG,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
    have hstart : ψ u ∈ U := collapse_mem_region Z F rep c r hrep
      (fun H hH => (hbound H hH).1) hsurvive u v
    have hzU := walk_support_mem p hstart z hz
    have hunit : 1 ≤ D*(1+dist u y)^ν := one_le_mul_of_one_le_of_one_le hD
      (Real.one_le_rpow (by linarith [dist_nonneg (x:=u) (y:=y)]) hν0)
    rcases hzU.1 with rfl | rfl | ⟨H,hH,hincident,hzH⟩
    · exact (by simp : dist z z ≤ 1).trans hunit
    · exact (step_dist_le_one huv).trans hunit
    · have hzc : dist z (c H) ≤ (C+6)*(1+dist (c H) y)^ν := by
        have h := (dist_le_iff_mem_ball (r:=r H+1) (c H) z).mpr (by simpa only [Nat.cast_add,Nat.cast_one] using hzH)
        rw [dist_comm (c H) z] at h
        push_cast at h
        exact h.trans (hbound H hH).2
      have hqc (q : Site d) (hq : q ∈ H) : dist q (c H)+1 ≤ (C+6)*(1+dist (c H) y)^ν := by
        have h := (dist_le_iff_mem_ball (c H) q).mpr ((hbound H hH).1 hq)
        rw [dist_comm (c H) q] at h
        linarith [(hbound H hH).2]
      rcases hincident with huH | hvH
      · exact hdisp y u u (c H) z (by simp) (hqc u huH) hzc
      · exact hdisp y u v (c H) z (step_dist_le_one huv) (hqc v hvH) hzc

end Heisenberg.HullRouting

open scoped Classical
namespace Heisenberg.RoutedFlow

lemma sum_eq_of_zero_off {E : Type*} (s t : Finset E) (f : E → ℝ)
    (hs : ∀ e ∈ s, e ∉ t → f e = 0) (ht : ∀ e ∈ t, e ∉ s → f e = 0) :
    (∑ e ∈ s, f e) = ∑ e ∈ t, f e := by
  calc
    _ = ∑ e ∈ s ∩ t, f e := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro e he hne
      exact hs e he (fun h => hne (Finset.mem_inter.mpr ⟨he,h⟩))
    _ = ∑ e ∈ t, f e := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro e he hne
      exact ht e he (fun h => hne (Finset.mem_inter.mpr ⟨h,he⟩))

structure Network (V E : Type*) where
  src : E → V
  dst : E → V
  incidentFinite : ∀ v, {e | src e = v ∨ dst e = v}.Finite

namespace Network
variable {V E : Type*} (N : Network V E)

def gradient (g : V → ℝ) (e : E) : ℝ := g (N.src e) - g (N.dst e)

def edges (g : V →₀ ℝ) : Finset E :=
  g.support.biUnion (fun v => (N.incidentFinite v).toFinset)

lemma mem_edges (g : V →₀ ℝ) (e : E) :
    e ∈ N.edges g ↔ N.src e ∈ g.support ∨ N.dst e ∈ g.support := by
  simp only [edges,Finset.mem_biUnion,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v,hv,h|h⟩
    · exact Or.inl (h ▸ hv)
    · exact Or.inr (h ▸ hv)
  · rintro (h|h)
    · exact ⟨N.src e,h,Or.inl rfl⟩
    · exact ⟨N.dst e,h,Or.inr rfl⟩

lemma gradient_zero_of_not_mem (g : V →₀ ℝ) {e : E} (he : e ∉ N.edges g) :
    N.gradient g e = 0 := by
  have h := mt (N.mem_edges g e).mpr he
  push Not at h
  simp only [Finsupp.notMem_support_iff] at h
  simp [gradient,h.1,h.2]

def pairing (F : E → ℝ) (g : V →₀ ℝ) : ℝ :=
  ∑ e ∈ N.edges g, F e * N.gradient g e

lemma pairing_eq_sum (F : E → ℝ) (g : V →₀ ℝ) (s : Finset E)
    (hs : ∀ e, N.gradient g e ≠ 0 → e ∈ s) :
    N.pairing F g = ∑ e ∈ s, F e * N.gradient g e := by
  unfold pairing
  apply sum_eq_of_zero_off
  · intro e he hne
    rw [show N.gradient g e = 0 from by_contra (fun h => hne (hs e h)),mul_zero]
  · intro e he hne
    rw [N.gradient_zero_of_not_mem g hne,mul_zero]

def UnitFlow (F : E → ℝ) (y : V) : Prop := ∀ g : V →₀ ℝ, N.pairing F g = g y

lemma pairing_finsupp (F : E →₀ ℝ) (g : V →₀ ℝ) :
    N.pairing F g = ∑ e ∈ F.support, F e * N.gradient g e := by
  unfold pairing
  apply sum_eq_of_zero_off
  · intro e he hne
    rw [Finsupp.notMem_support_iff.mp hne,zero_mul]
  · intro e he hne
    rw [N.gradient_zero_of_not_mem g hne,mul_zero]

end Network

variable {V E W T : Type*}

def pullback (ψ : V → W) (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (g : W →₀ ℝ) : V →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => g (ψ v)) (by
    apply Set.Finite.subset (Set.Finite.biUnion g.support.finite_toSet (fun w _ => hψ w))
    intro v hv
    simp only [Set.mem_iUnion]
    exact ⟨ψ v,Finsupp.mem_support_iff.mpr hv,rfl⟩)

@[simp] lemma pullback_apply (ψ : V → W) (hψ : ∀ w, (ψ ⁻¹' {w}).Finite)
    (g : W →₀ ℝ) (v : V) : pullback ψ hψ g v = g (ψ v) := rfl

structure Routing (S : Network V E) (N : Network W T) (ψ : V → W) where
  current : E → T →₀ ℝ
  locallyFinite : ∀ t, {e | current e t ≠ 0}.Finite
  telescopes : ∀ e (g : W →₀ ℝ), N.pairing (current e) g = g (ψ (S.src e)) - g (ψ (S.dst e))

namespace Routing
variable {S : Network V E} {N : Network W T} {ψ : V → W} (R : Routing S N ψ)

def sources (s : Finset T) : Finset E := s.biUnion (fun t => (R.locallyFinite t).toFinset)

lemma mem_sources (s : Finset T) (e : E) : e ∈ R.sources s ↔ ∃ t ∈ s, R.current e t ≠ 0 := by
  simp [sources]

def push (F : E → ℝ) (t : T) : ℝ :=
  ∑ e ∈ (R.locallyFinite t).toFinset, F e * R.current e t

lemma push_eq_sum (F : E → ℝ) (s : Finset T) {t : T} (ht : t ∈ s) :
    R.push F t = ∑ e ∈ R.sources s, F e * R.current e t := by
  unfold push
  apply Finset.sum_subset
  · intro e he
    exact (R.mem_sources s e).mpr ⟨t,ht,(R.locallyFinite t).mem_toFinset.mp he⟩
  · intro e he hne
    rw [show R.current e t = 0 from by simpa using hne, mul_zero]

lemma pairing_push (F : E → ℝ) (g : W →₀ ℝ) :
    N.pairing (R.push F) g =
      ∑ e ∈ R.sources (N.edges g), F e * N.pairing (R.current e) g := by
  unfold Network.pairing
  calc
    _ = ∑ t ∈ N.edges g, ∑ e ∈ R.sources (N.edges g),
          F e * R.current e t * N.gradient g t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [R.push_eq_sum F _ ht,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

lemma source_gradient_zero (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (g : W →₀ ℝ)
    {e : E} (he : e ∉ R.sources (N.edges g)) : S.gradient (pullback ψ hψ g) e = 0 := by
  have hzero : N.pairing (R.current e) g = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hct : R.current e t = 0 := by
      by_contra h
      exact he ((R.mem_sources _ e).mpr ⟨t,ht,h⟩)
    rw [hct,zero_mul]
  rw [R.telescopes] at hzero
  exact hzero

theorem push_unit (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (F : E → ℝ) (y : V)
    (hF : S.UnitFlow F y) : N.UnitFlow (R.push F) (ψ y) := by
  intro g
  rw [R.pairing_push]
  have hsum := S.pairing_eq_sum F (pullback ψ hψ g) (R.sources (N.edges g))
    (fun e he => by_contra (fun h => he (R.source_gradient_zero hψ g h)))
  rw [show (∑ e ∈ R.sources (N.edges g), F e * N.pairing (R.current e) g) =
      S.pairing F (pullback ψ hψ g) from by
        rw [hsum]
        apply Finset.sum_congr rfl
        intro e _
        rw [R.telescopes]
        rfl]
  exact hF _

end Routing
end Heisenberg.RoutedFlow

end

end OAI
