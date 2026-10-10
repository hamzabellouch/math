import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Gluing.RelayGeometry
import OAI.Probability.CriticalPercolation.Gluing.CorridorGraph
import OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma open_induced_adj (S : Set V) (ω : Set E) (u v : V) :
    (G.openGraph (ω∩G.inducedEdges S)).Adj u v ↔
    (G.openGraph ω).Adj u v ∧ u∈S ∧ v∈S := by
  constructor
  · rintro ⟨⟨b,hb,hend⟩,hne⟩
    exact ⟨⟨⟨b,hb.1,hend⟩,hne⟩,hb.2 u (by rw [hend]; simp),
      hb.2 v (by rw [hend]; simp)⟩
  · rintro ⟨⟨⟨b,hb,hend⟩,hne⟩,hu,hv⟩
    refine ⟨⟨b,⟨hb,?_⟩,hend⟩,hne⟩
    intro w hw
    rw [hend] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl|rfl <;> assumption

lemma walk_reachable_induced (S : Set V) (ω : Set E) {a b : V}
    (w : (G.openGraph ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.openGraph (ω∩G.inducedEdges S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.open_induced_adj S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))

def coordinateMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ 100 ∧ |z x-z y| ≤ 100) ∧
    |t b-(t y+1)| ≤ e/4 ∧ |z b-(z y+s)| ≤ e/4}

def relayRegion (t z : V → ℝ) (σ e : ℝ) (i : ℕ) : Set V :=
  {v | |t v-(i : ℝ)| ≤ (i+1)*e ∧ |z v-σ*(i : ℝ)/4| ≤ Relay.width i}

def relayMark (t z : V → ℝ) (T σ ρ : ℝ) : Set V :=
  {v | T ≤ t v ∧ t v ≤ T+ρ ∧ |z v-σ*T/4| ≤ 210}

def relayDomain (t z : V → ℝ) (J T σ : ℝ) : Set V :=
  (fun v => (t v,z v)) ⁻¹' Relay.domain J T σ

lemma relay_collar_bounds (t z : V → ℝ) (σ e ρ : ℝ) (hρ : 0 ≤ ρ)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (R i : ℕ) {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    |t y-(i : ℝ)| ≤ (i+1)*e+R*ρ ∧ |z y-σ*(i : ℝ)/4| ≤ Relay.width i+R*ρ := by
  exact ⟨G.coordinate_collar_bound t ρ hρ ht _ _ _ (fun _ h => h.1) hy,
    G.coordinate_collar_bound z ρ hρ hz _ _ _ (fun _ h => h.2) hy⟩

lemma full_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i<L) (hsmall : (L+1)*e+R*ρ<1)
    (hheight : R*ρ+e/4 ≤ 1/4) (htime : R*ρ+e/4 ≤ e)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    coordinateMove G t z m e y (Relay.selectedSign (z y-σ*(i : ℝ)/4)) ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1))} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,hbz⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  have hb : b∈relayRegion t z σ e (i+1) := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        Relay.full_step_time i (t y) (t b) (R*ρ) e hy'.1 hbt htime
    have hh := Relay.full_step_height i (z y-σ*(i : ℝ)/4) σ (R*ρ) e
      (z b-(z y+Relay.selectedSign (z y-σ*(i : ℝ)/4))) hσ hy'.2
      (mul_nonneg (Nat.cast_nonneg _) hρ) hheight hbz
    convert hh using 1
    push_cast
    ring_nf
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,b,G.walk_reachable_induced _ ω w ?_,hb⟩
  intro x hx
  exact Relay.move_path_contained J L i hi.le hJ (t y,z y) (t x,z x)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 (hw x hx).1 (hw x hx).2

lemma last_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hL : 416 ≤ L) (hsmall : (L+1)*e+(R+m)*ρ+e/4<1/2)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e L) R) (s : ℝ) :
    coordinateMove G t z m e y s ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ)} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,_⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R L hy
  have hma : |t a-t y| ≤ m*ρ := G.coordinate_ball_bound t ρ hρ ht ha
  have hnR : 0 ≤ (R : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnm : 0 ≤ (m : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnL : 0 ≤ (L+1 : ℝ)*e := mul_nonneg (by positivity) he
  have hyt := abs_le.mp hy'.1
  have hbt' := abs_le.mp hbt
  have hma' := abs_le.mp hma
  have haT : t a<L+1/2 := by linarith
  have hbT : (L : ℝ)+1/2 ≤ t b := by linarith
  have hadj : ∀ ⦃u v⦄, (G.openGraph ω).Adj u v → |t u-t v| ≤ ρ :=
    fun _ _ h => ht (G.openGraph_mono (Set.subset_univ _) h)
  obtain ⟨x,hx,hx₁,hx₂⟩ := _root_.OAI.SimpleGraph.Walk.exists_first_crossing t ρ (L+1/2) hadj w haT hbT
  have hxz : |z x-σ*(L+1/2)/4|<210 := by
    apply Relay.last_crossing_height L (t y,z y) (t x,z x) (R*ρ) σ hσ
    · simpa only [Relay.width_last L hL] using hy'.2
    · exact (hw x hx).2
    · linarith
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,?_,⟨hx₁,hx₂,hxz.le⟩⟩
  apply G.walk_reachable_induced _ ω (w.takeUntil x hx)
  intro v hv
  have hv' : v∈w.support := (w.isSubwalk_takeUntil hx).support_subset hv
  apply Relay.move_path_contained J L L le_rfl hJ (t y,z y) (t v,z v)
    (R*ρ) e σ hσ he _ hy'.1 hy'.2 (hw v hv').1 (hw v hv').2
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
