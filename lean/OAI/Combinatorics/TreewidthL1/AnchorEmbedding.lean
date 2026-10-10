import OAI.Combinatorics.TreewidthL1.AnchorGeometry

namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

noncomputable def graphPath (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (hdist : ∀ u v, dist u v = shortestPathDistance G ℓ u v)
    (hne : ∀ i, (B i).Nonempty)
    (hD : ∀ i, D i = bagDistance G ℓ (B i) (hne i))
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (hbag : ∀ i, (B i).card ≤ k) (hbound : ∀ i v, D i v ≤ P.Δ)
    (X Y : Fin (n+1)) (x y : V) (hx : x ∈ B X) (hy : y ∈ B Y) (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (hpos : 0 < D ((downPath T hT root X).getVert s) x) : PathGeometry P := by
  let q := downPath T hT root X
  have hgeo (a t : ℕ) (hat : a ≤ t) :
      D (q.getVert t) x ≤ D (q.getVert a) x ∧
      ∃ v ∈ B (q.getVert t), D (q.getVert a) v+dist x v = D (q.getVert a) x := by
    have hp : q.getVert t ∈ (q.drop a).support := by
      simpa only [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hat] using (q.drop a).getVert_mem_support (t-a)
    have hh := separator_bag_geometry G ℓ hG hℓ T B hne hT hedge hrun (q.drop a)
      ((downPath_isPath T hT root X).drop a) hp hx
    rw [hD,hD]
    refine ⟨hh.1,?_⟩
    obtain ⟨v,hv,hhv⟩ := hh.2
    refine ⟨v,hv,?_⟩
    rw [hdist,shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le) x v]
    exact hhv
  refine {
    X := X, Y := Y, x := x, y := y, start := s, start_le := hsx, hx := hx, hy := hy,
    positive := hpos, bounded := hbound, bag_bound := hbag
    nonneg := ?_, lipschitz := ?_, zero := ?_, monotone := ?_, near := ?_, geodesic := ?_, suffix := ?_ }
  · intro i v
    rw [hD]
    exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro i u v
    rw [hD,hdist]
    exact bagDistance_lipschitz G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) u v
  · intro i v hv
    rw [hD]
    apply le_antisymm
    · have hh := bagDistance_le G ℓ (B i) (hne i) v hv
      rw [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)] at hh
      exact hh
    · exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro a t hat
    exact (hgeo a t hat).1
  · intro t
    obtain ⟨p,hp,hpdist⟩ := bagDistance_attained G ℓ (B (q.getVert t)) (hne _) x
    exact ⟨p,hp,by rw [hD,hdist]; exact hpdist.symm⟩
  · intro a t hat ht
    exact (hgeo a t hat).2
  · intro e hse he
    exact ⟨(forest T hT root).depth Y-s,join_prefix_data T hT root X Y s hsx hsy hs hmax e hse he⟩

namespace PathGeometry
variable {P} (A : PathGeometry P)
noncomputable def track {H Q : ℝ} (C : TestParameters k α π η H Q)
    (R : ReservationPath) (hR : R.last = (forest T hT root).depth A.X)
    (hcache : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
      (heights T hT root D A.X) J t)
    (hsize : ∀ t, (R.inclusive t).card ≤ cacheBound k+1)
    (hprotect : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
      (fun p a => D (A.node a) p) J, t < R.finish b) :
    GeometricTrack V (cacheBound k+1) (upper k) J H Q where
  path := R
  start := A.start
  start_le := by rw [hR]; exact A.start_le
  delta := A.δ
  antitone := A.monotone
  nonneg := fun t => A.nonneg _ _
  start_pos := A.positive
  end_zero := by
    change D ((downPath T hT root A.X).getVert R.last) A.x = 0
    rw [hR,← downPath_length,SimpleGraph.Walk.getVert_length]
    exact A.zero A.X A.x A.hx
  error := A.err
  error_nonneg := norm_nonneg _
  size := hsize
  B := fun t => B (A.node t)
  D := fun t => D (A.node t)
  x := A.x
  at_x := fun _ => rfl
  lipschitz := fun a => A.lipschitz (A.node a)
  launch := by
    intro a e he ha hs
    rw [hcache e he] at ha
    exact A.launch a e (by rwa [← hR]) ha hs
  small := by
    intro a e he ha hs hd
    rw [hcache e he] at ha
    exact A.small C a e (by rwa [← hR]) ha hs hd
  obstruction := by
    intro a e t he ha hs hst hte hg
    rw [hcache e he] at ha
    exact A.obstruction C a e t (by rwa [← hR]) ha hs hst hte hg
  protect_rule := hprotect

lemma lower_of_track {H Q : ℝ} (C : TestParameters k α π η H Q)
    (hJ : J = 10*(upper k+4)) (hH : 10^5*J < H)
    (c : ℝ) (hc : ∀ CC : CacheControl (cacheBound k+1) Q H, c ≤ CC.error)
    (R : ReservationPath) (hR : R.last = (forest T hT root).depth A.X)
    (hcache : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
      (heights T hT root D A.X) J t)
    (hsize : ∀ t, (R.inclusive t).card ≤ cacheBound k+1)
    (hprotect : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
      (fun p a => D (A.node a) p) J, t < R.finish b) :
    c*A.δ A.start ≤ A.err := by
  let QP := A.track C R hR hcache hsize hprotect
  have hh := hc (QP.control (upper_pos k).le hJ hH C.qlarge)
  change c ≤ A.err/A.δ A.start at hh
  exact (le_div_iff₀ A.positive).mp hh
end PathGeometry
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
noncomputable section

theorem test_parameters_exist (k : ℕ) (α π : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/8)
    (hπ : 0 < π) (hπ1 : π ≤ 1) :
    ∃ J H η Q : ℝ, J = 10*(upper k+4) ∧ 10^5*J < H ∧
      Nonempty (TestParameters k α π η H Q) := by
  let J := 10*(upper k+4)
  let H := 10^5*J+1
  have hU := upper_pos k
  have hL := particleLip_pos k
  have hJ : 0 < J := by dsimp [J]; positivity
  have hH : 1 < H := by dsimp [H]; nlinarith
  let η := 1/(16*H)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η < 1/4 := by
    dsimp [η]; apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr; nlinarith
  have hr : 4*η*H < 1 := by
    have hH0 : H ≠ 0 := by linarith
    dsimp [η]; field_simp; norm_num
  let c := α/8*η
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by
    have hαη := mul_le_mul_of_nonneg_right hα1 hη.le
    dsimp [c]; nlinarith
  let b := c/(8*((k:ℝ)+1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  let w := π/8*b
  have hw : 0 < w := by dsimp [w]; positivity
  let Q := (1+upper k+particleLip k)/w+(upper k+1)
  have hQ : upper k+1 ≤ Q := by
    dsimp [Q]; have hh : 0 ≤ (1+upper k+particleLip k)/w := by positivity
    linarith
  have hbound : 1+upper k+particleLip k ≤ (π/8*b)*Q := by
    have hh : w*((1+upper k+particleLip k)/w) = 1+upper k+particleLip k :=
      mul_div_cancel₀ _ hw.ne'
    change _ ≤ w*Q
    dsimp only [Q]
    nlinarith [mul_nonneg hw.le (show 0 ≤ upper k+1 by positivity)]
  refine ⟨J,H,η,Q,rfl,by dsimp [H]; linarith,⟨?_⟩⟩
  exact {
    c := c, b := b, c_eq := rfl, c_pos := hc, c_half := hc2,
    b_eq := rfl, b_pos := hb, b_one := hb1, eta_pos := hη, eta_small := hη4,
    pi_pos := hπ, pi_one := hπ1, radius := hr, qbound := hbound, qlarge := hQ }
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

lemma Model.join_lower (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (hdist : ∀ u v, dist u v = shortestPathDistance G ℓ u v)
    (hne : ∀ i, (B i).Nonempty)
    (hD : ∀ i, D i = bagDistance G ℓ (B i) (hne i))
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (hbag : ∀ i, (B i).card ≤ k) (hbound : ∀ i v, D i v ≤ P.Δ)
    {H Q : ℝ} (C : TestParameters k α π η H Q)
    (hJ : J = 10*(upper k+4)) (hH : 10^5*J < H)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ CC : CacheControl (cacheBound k+1) Q H, c ≤ CC.error)
    (X Y : Fin (n+1)) (x y : V) (hx : x ∈ B X) (hy : y ∈ B Y) (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    c*D ((downPath T hT root X).getVert s) x ≤ ‖P.map x-P.map y‖ := by
  by_cases hp : 0 < D ((downPath T hT root X).getVert s) x
  · let A := graphPath P G hG ℓ hℓ hdist hne hD hedge hrun hbag hbound X Y x y hx hy s hsx hsy hs hmax hp
    obtain ⟨R,hR,hcache,hsize,hprotect⟩ := graph_cache_realizes G ℓ hG hℓ T B hne hT hedge hrun k hbag J
      (downPath T hT root X) (downPath_isPath T hT root X)
    have hR' : R.last = (forest T hT root).depth A.X := hR.trans (downPath_length T hT root X)
    have hdF : dist = shortestPathDistance G ℓ := funext (fun u => funext (hdist u))
    have hDF : D = fun i => bagDistance G ℓ (B i) (hne i) := funext hD
    have hcache' : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
        (heights T hT root D A.X) J t := by
      intro t ht
      change R.inclusive t = inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J t
      rw [hdF,hDF]
      exact hcache t (by rwa [← hR])
    have hprotect' : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
        (fun p a => D (A.node a) p) J, t < R.finish b := by
      intro t ht b hb
      apply hprotect t (by rwa [← hR]) b
      rw [hcache' t ht.le] at hb
      change b ∈ protectedEntries (B ((downPath T hT root X).getVert t))
        (inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J t) dist
        (fun p a => D ((downPath T hT root X).getVert a) p) J at hb
      rw [hdF,hDF] at hb
      exact hb
    exact A.lower_of_track C hJ hH c hc R hR' hcache' hsize hprotect'
  · exact (mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_gt hp)).trans (norm_nonneg _)

/-- The constructed anchor ensemble controls BOTH distances to one actual common
bag. This is enough for all-pairs lower comparison when combined with co-bag
separation, and involves no assumed contraction/Markov-flow theorem. -/
theorem anchor_common_bag_embedding (k : ℕ) (hk : 2 ≤ k) :
    ∃ U c : ℝ, 0 < U ∧ 0 < c ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (_ : G.Connected) (ℓ : G.edgeSet → ℝ) (_ : ∀ e, 0 < ℓ e)
      (n : ℕ) (T : SimpleGraph (Fin (n+1))) (_ : T.IsTree) (_ : Fin (n+1))
      (B : Fin (n+1) → Finset V) (hne : ∀ i, (B i).Nonempty)
      (_ : ∀ v, ∃ i, v ∈ B i)
      (_ : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
      (_ : ∀ v, (T.induce {i | v ∈ B i}).Connected)
      (_ : ∀ i, (B i).card ≤ k),
      ∃ m : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
        (∀ x y, ‖Φ x-Φ y‖ ≤ U*shortestPathDistance G ℓ x y) ∧
        ∀ x y, ∃ i, c*bagDistance G ℓ (B i) (hne i) x ≤ ‖Φ x-Φ y‖ ∧
          c*bagDistance G ℓ (B i) (hne i) y ≤ ‖Φ x-Φ y‖ := by
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_ordinary_noise k hk
  obtain ⟨J,H,η,Q,hJ,hH,⟨C⟩⟩ := test_parameters_exist k α π hα hα8 hπ hπ1
  have hQ : 0 < Q := by linarith [C.qlarge,upper_pos k]
  obtain ⟨c,hc,hccontrol⟩ := CacheControl.uniform_lower (cacheBound k+1) Q H hQ
  refine ⟨upper k,c,upper_pos k,hc,?_⟩
  intro V _ _ _ G hG ℓ hℓ n T hT root B hne hcover hedge hrun hbag
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  have hdec : HasTreeDecomposition G k := ⟨n+1,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hnoise (i : Fin (n+1)) : HasOrdinaryNoise (D i) α π η := by
    have hn := hsampler V G hG hdec ℓ hℓ (B i : Set V) (hne i) η C.eta_pos C.eta_small
    have heq : D i = fun x => Metric.infDist x (B i : Set V) := by
      funext x
      exact bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) x
    rw [heq]
    exact hn
  let seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η :=
    fun i => Classical.choice (OrdinarySeed.exists_of_has (hnoise i))
  obtain ⟨P,hbound⟩ := model_exists G hG ℓ hℓ T hT root B hne hcover hedge hrun k hbag J α π η seed
  refine ⟨P.dim,P.map,P.upper_bound,?_⟩
  intro x y
  obtain ⟨X,hx⟩ := hcover x
  obtain ⟨Y,hy⟩ := hcover y
  obtain ⟨s,hsx,hsy,hs,hmax⟩ := exists_join_index T hT root X Y
  refine ⟨(downPath T hT root X).getVert s,?_,?_⟩
  · exact P.join_lower G hG ℓ hℓ (fun _ _ => rfl) hne (fun _ => rfl) hedge hrun hbag hbound
      C hJ hH c hc.le hccontrol X Y x y hx hy s hsx hsy hs hmax
  · have hm : ∀ a b, a ≤ (forest T hT root).depth Y → b ≤ (forest T hT root).depth X →
        (downPath T hT root Y).getVert a = (downPath T hT root X).getVert b → a = b ∧ a ≤ s := by
      intro a b ha hb he
      obtain ⟨hab,hbs⟩ := hmax b a hb ha he.symm
      exact ⟨hab.symm,hab ▸ hbs⟩
    have hh := P.join_lower G hG ℓ hℓ (fun _ _ => rfl) hne (fun _ => rfl) hedge hrun hbag hbound
      C hJ hH c hc.le hccontrol Y X y x hy hx s hsy hsx hs.symm hm
    rw [norm_sub_rev,← hs] at hh
    exact hh
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
