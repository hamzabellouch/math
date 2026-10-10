import OAI.MathematicalPhysics.Heisenberg.RoutedNetworks

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical

namespace Heisenberg.RoutedFlow.Network
variable {V E : Type*} (N : Network V E)

def boundary (e : E) (v : V) : ℝ :=
  (if N.src e = v then 1 else 0) - (if N.dst e = v then 1 else 0)

def divergence (F : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ (N.incidentFinite v).toFinset, F e * N.boundary e v

lemma vertex_sum (g : V →₀ ℝ) (e : E) :
    (∑ v ∈ g.support, g v * N.boundary e v) = N.gradient g e := by
  simp only [boundary,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq]
  rw [show (if N.src e ∈ g.support then g (N.src e) else 0) = g (N.src e) by
    split_ifs with h; rfl; exact (Finsupp.notMem_support_iff.mp h).symm]
  rw [show (if N.dst e ∈ g.support then g (N.dst e) else 0) = g (N.dst e) by
    split_ifs with h; rfl; exact (Finsupp.notMem_support_iff.mp h).symm]
  rfl

lemma boundary_zero {e : E} {v : V} (he : e ∉ (N.incidentFinite v).toFinset) :
    N.boundary e v = 0 := by
  have h : ¬(N.src e = v ∨ N.dst e = v) := by simpa using he
  simp [boundary,not_or.mp h |>.1,not_or.mp h |>.2]

lemma divergence_eq_sum (F : E → ℝ) (g : V →₀ ℝ) {v : V} (hv : v ∈ g.support) :
    N.divergence F v = ∑ e ∈ N.edges g, F e * N.boundary e v := by
  apply Finset.sum_subset
  · intro e he
    rcases (N.incidentFinite v).mem_toFinset.mp he with h|h
    · exact (N.mem_edges g e).mpr (Or.inl (h ▸ hv))
    · exact (N.mem_edges g e).mpr (Or.inr (h ▸ hv))
  · intro e _ he
    rw [N.boundary_zero he,mul_zero]

theorem pairing_divergence (F : E → ℝ) (g : V →₀ ℝ) :
    N.pairing F g = ∑ v ∈ g.support, g v * N.divergence F v := by
  unfold pairing
  simp_rw [← N.vertex_sum g]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [N.divergence_eq_sum F g hv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem unit_of_divergence (F : E → ℝ) (y : V)
    (h : ∀ v, N.divergence F v = if v = y then 1 else 0) : N.UnitFlow F y := by
  intro g
  rw [N.pairing_divergence]
  simp_rw [h,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hy
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hy).symm

lemma pairing_single (e : E) (g : V →₀ ℝ) :
    N.pairing (Finsupp.single e 1) g = N.gradient g e := by
  rw [N.pairing_finsupp]
  simp

lemma pairing_add (F H : E → ℝ) (g : V →₀ ℝ) :
    N.pairing (F+H) g = N.pairing F g + N.pairing H g := by
  simp [pairing,add_mul,Finset.sum_add_distrib]

end Heisenberg.RoutedFlow.Network

namespace Heisenberg.RoutedFlow.Routing
variable {V E W T : Type*} {S : Network V E} {N : Network W T} {ψ : V → W}

theorem abs_push_le (R : Routing S N ψ) (F : E → ℝ) (t : T) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ e, R.current e t ≠ 0 → |F e| ≤ A)
    (hR : ∀ e, |R.current e t| ≤ 1) :
    |R.push F t| ≤ ((R.locallyFinite t).toFinset.card : ℝ) * A := by
  unfold push
  calc
    _ ≤ ∑ e ∈ (R.locallyFinite t).toFinset, |F e * R.current e t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ (R.locallyFinite t).toFinset, A := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact (mul_le_mul (hF e ((R.locallyFinite t).mem_toFinset.mp he)) (hR e)
        (abs_nonneg _) hA).trans_eq (mul_one A)
    _ = _ := by simp

end Heisenberg.RoutedFlow.Routing

namespace Heisenberg.RoutedFlow
variable {V : Type*} (G : SimpleGraph V) (hG : ∀ v, (G.neighborSet v).Finite)

def graphNetwork : Network V G.Dart where
  src e := e.fst
  dst e := e.snd
  incidentFinite v := by
    have hi : Function.Injective (fun e : G.Dart => e.toProd) := by
      intro e f h
      exact SimpleGraph.Dart.ext e f h
    apply (((Set.finite_singleton v).prod (hG v)).union
      ((hG v).prod (Set.finite_singleton v))).preimage hi.injOn |>.subset
    intro e he
    rcases he with h|h
    · exact Or.inl ⟨h,by simpa only [← h,SimpleGraph.mem_neighborSet] using e.adj⟩
    · exact Or.inr ⟨by simpa [← h] using e.adj.symm,h⟩

variable {G}

def pathCurrent {u v : V} : G.Walk u v → G.Dart →₀ ℝ
  | .nil => 0
  | .cons h p => Finsupp.single ⟨(u,_),h⟩ 1 + pathCurrent p

lemma pathCurrent_pairing {u v : V} (p : G.Walk u v) (g : V →₀ ℝ) :
    (graphNetwork G hG).pairing (pathCurrent p) g = g u - g v := by
  induction p with
  | nil => simp [pathCurrent,Network.pairing]
  | @cons u v w h p ih =>
    rw [pathCurrent,Finsupp.coe_add,Network.pairing_add,Network.pairing_single,ih]
    change (g u-g v)+(g v-g w) = g u-g w
    ring

omit hG in
lemma pathCurrent_eq_count {u v : V} (p : G.Walk u v) (e : G.Dart) :
    pathCurrent p e = (p.darts.count e : ℝ) := by
  induction p with
  | nil => simp [pathCurrent]
  | @cons u v w h p ih =>
    simp only [pathCurrent,Finsupp.add_apply,ih,SimpleGraph.Walk.darts_cons,
      List.count_cons]
    by_cases he : (⟨(u,v),h⟩ : G.Dart) = e
    · subst e; simp [add_comm]
    · simp [he,Ne.symm he]

omit hG in
lemma pathCurrent_abs_le_one {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (e : G.Dart) :
    |pathCurrent p e| ≤ 1 := by
  rw [pathCurrent_eq_count,abs_of_nonneg (by positivity)]
  have hd : p.darts.Nodup := List.Nodup.of_map SimpleGraph.Dart.edge hp.edges_nodup
  exact_mod_cast List.nodup_iff_count_le_one.mp hd e

omit hG in
lemma pathCurrent_ne_zero_iff {u v : V} (p : G.Walk u v) (e : G.Dart) :
    pathCurrent p e ≠ 0 ↔ e ∈ p.darts := by
  rw [pathCurrent_eq_count,Nat.cast_ne_zero,← Nat.pos_iff_ne_zero,List.count_pos_iff]

def routingOfPaths {W E : Type*} (S : Network W E) (ψ : W → V)
    (P : ∀ e, G.Walk (ψ (S.src e)) (ψ (S.dst e)))
    (hP : ∀ t, {e | t ∈ (P e).darts}.Finite) : Routing S (graphNetwork G hG) ψ where
  current e := pathCurrent (P e)
  locallyFinite t := by simpa only [pathCurrent_ne_zero_iff] using hP t
  telescopes e g := pathCurrent_pairing hG (P e) g

lemma routingOfPaths_abs_le_one {W E : Type*} (S : Network W E) (ψ : W → V)
    (P : ∀ e, G.Walk (ψ (S.src e)) (ψ (S.dst e)))
    (hP : ∀ t, {e | t ∈ (P e).darts}.Finite) (hsimple : ∀ e, (P e).IsTrail)
    (e : E) (t : G.Dart) : |(routingOfPaths hG S ψ P hP).current e t| ≤ 1 :=
  pathCurrent_abs_le_one (P e) (hsimple e) t

end Heisenberg.RoutedFlow

open scoped Classical
open Module
namespace Heisenberg.LatticeSum

abbrev Site (d : ℕ) := Fin d → ℤ

def radius {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup (fun j => (x j).natAbs)

def integerLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

instance (d : ℕ) : DiscreteTopology (integerLattice d) := by
  unfold integerLattice
  infer_instance

instance (d : ℕ) : IsZLattice ℝ (integerLattice d) := by
  unfold integerLattice
  infer_instance

def embed {d : ℕ} (x : Site d) : integerLattice d :=
  ⟨fun j => (x j : ℝ), by
    apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
    intro j
    exact ⟨x j, by simp⟩⟩

lemma embed_injective (d : ℕ) : Function.Injective (embed (d := d)) := by
  intro x y h
  ext j
  have hj := congrFun (congrArg Subtype.val h) j
  change (x j : ℝ) = (y j : ℝ) at hj
  exact_mod_cast hj

lemma embed_norm_le {d : ℕ} (x : Site d) : ‖embed x‖ ≤ (radius x : ℝ) := by
  change ‖fun j => (x j : ℝ)‖ ≤ (radius x : ℝ)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hj : (x j).natAbs ≤ radius x := by
    exact Finset.le_sup (α := ℕ) (f := fun j => (x j).natAbs) (Finset.mem_univ j)
  simpa only [Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs] using
    (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast hj)

lemma embed_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) : embed x ≠ 0 := by
  intro he
  apply hx
  apply embed_injective d
  convert he using 1
  apply Subtype.ext
  funext j
  simp [embed]

theorem summable_radius_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun x : Site d => ((radius x : ℝ) + 1) ^ r) := by
  have hrank : Module.finrank ℤ (integerLattice d) = d := by
    rw [ZLattice.rank ℝ]
    simp
  have hs := ZLattice.summable_norm_rpow (integerLattice d) r (by simpa [hrank] using hr)
  have ht : Summable (fun x : Site d => ‖embed x‖ ^ r) :=
    hs.comp_injective (embed_injective d)
  apply Summable.of_norm_bounded_eventually ht
  apply Set.Finite.subset (Set.finite_singleton (0 : Site d))
  intro x hx
  by_contra hn
  have hpos : 0 < ‖embed x‖ := norm_pos_iff.mpr (embed_ne_zero hn)
  have hle : ‖((radius x : ℝ) + 1) ^ r‖ ≤ ‖embed x‖ ^ r := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith [embed_norm_le x]) (by linarith)
  exact hx hle

theorem summable_radius_sub_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) (y : Site d) :
    Summable (fun x : Site d => ((radius (x - y) : ℝ) + 1) ^ r) := by
  exact (Equiv.subRight y).summable_iff.mpr (summable_radius_rpow d r hr)

theorem finite_energy_of_envelope {d : ℕ} {I : Type*} [Fintype I]
    (J : I × Site d → ℝ) (y : Site d) (C k : ℝ) (hC : 0 ≤ C)
    (hk : (d : ℝ) < 2 * k)
    (hJ : ∀ e, |J e| ≤ C * ((radius (e.2 - y) : ℝ) + 1) ^ (-k)) :
    Summable (fun e => J e ^ 2) := by
  have hs := summable_radius_sub_rpow d (-2 * k) (by linarith) y
  have hs' : Summable (fun e : I × Site d =>
      C ^ 2 * ((radius (e.2 - y) : ℝ) + 1) ^ (-2 * k)) := by
    apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
    refine ⟨fun _ => hs.mul_left _, ?_⟩
    exact .of_finite
  apply Summable.of_nonneg_of_le (fun e => sq_nonneg _) _ hs'
  intro e
  have he := sq_le_sq₀ (abs_nonneg (J e))
    (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) |>.mpr (hJ e)
  have hr : (((radius (e.2 - y) : ℝ) + 1) ^ (-k)) ^ 2 =
      ((radius (e.2 - y) : ℝ) + 1) ^ (-2 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  simpa only [sq_abs, mul_pow, hr] using he

end Heisenberg.LatticeSum

end

end OAI
