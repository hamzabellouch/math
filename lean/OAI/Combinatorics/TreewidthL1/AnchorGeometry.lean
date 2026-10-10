import OAI.Combinatorics.TreewidthL1.CacheControl

namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

structure TestParameters (k : ℕ) (α π η H Q : ℝ) where
  c : ℝ
  b : ℝ
  c_eq : c = α/8*η
  c_pos : 0 < c
  c_half : c ≤ 1/2
  b_eq : b = c/(8*((k:ℝ)+1))
  b_pos : 0 < b
  b_one : b ≤ 1
  eta_pos : 0 < η
  eta_small : η < 1/4
  pi_pos : 0 < π
  pi_one : π ≤ 1
  radius : 4*η*H < 1
  qbound : 1+upper k+particleLip k ≤ (π/8*b)*Q
  qlarge : upper k+1 ≤ Q

variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

/-- All properties here are literal shortest-path/bag geometry. -/
structure PathGeometry where
  X : Fin (n+1)
  Y : Fin (n+1)
  x : V
  y : V
  start : ℕ
  start_le : start ≤ (forest T hT root).depth X
  hx : x ∈ B X
  hy : y ∈ B Y
  positive : 0 < D ((downPath T hT root X).getVert start) x
  nonneg : ∀ i v, 0 ≤ D i v
  lipschitz : ∀ i u v, |D i u-D i v| ≤ dist u v
  zero : ∀ i v, v ∈ B i → D i v = 0
  bounded : ∀ i v, D i v ≤ P.Δ
  bag_bound : ∀ i, (B i).card ≤ k
  monotone : Antitone (fun t => D ((downPath T hT root X).getVert t) x)
  near : ∀ t, ∃ p ∈ B ((downPath T hT root X).getVert t),
    dist x p = D ((downPath T hT root X).getVert t) x
  geodesic : ∀ a t, a ≤ t → t ≤ (forest T hT root).depth X →
    ∃ v ∈ B ((downPath T hT root X).getVert t),
      D ((downPath T hT root X).getVert a) v + dist x v = D ((downPath T hT root X).getVert a) x
  suffix : ∀ e, start ≤ e → e ≤ (forest T hT root).depth X → ∃ l,
    (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-start) ∧
    ∀ b, start ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-start)) =
        (downPath T hT root X).getVert b

namespace PathGeometry
variable {P} (A : PathGeometry P)
abbrev node (t : ℕ) := (downPath T hT root A.X).getVert t
abbrev δ (t : ℕ) := D (A.node t) A.x
abbrev err := ‖P.map A.x-P.map A.y‖
abbrev cached (a e : ℕ) := a ∈ inclusiveCache k (bags T hT root B A.X) dist (heights T hT root D A.X) J e
lemma lower_near (t : ℕ) (v : V) (hv : v ∈ B (A.node t)) : A.δ t ≤ dist A.x v := by
  have hh := A.lipschitz (A.node t) A.x v
  rw [A.zero _ _ hv,sub_zero,abs_of_nonneg (A.nonneg _ _)] at hh
  exact hh
lemma proxy_upper (z : V) : ‖P.map A.y-P.map z‖ ≤ A.err+upper k*dist A.x z := by
  have hh := dist_triangle (P.map A.y) (P.map A.x) (P.map z)
  simp only [dist_eq_norm] at hh
  rw [norm_sub_rev (P.map A.y) (P.map A.x)] at hh
  have hu := P.upper_bound A.x z
  change ‖P.map A.y-P.map z‖ ≤ ‖P.map A.x-P.map A.y‖+upper k*dist A.x z
  linarith

lemma numerical_test {H Q : ℝ} (C : TestParameters k α π η H Q)
    (v d : ℝ) (hd : 0 ≤ d)
    (ht : (π/8)*(C.b*v-particleLip k*d) ≤ A.err+upper k*d) :
    v ≤ Q*(A.err+d) := by
  have hp : 0 < π/8*C.b := mul_pos (by linarith [C.pi_pos]) C.b_pos
  have hπ : 0 ≤ π/8 := by linarith [C.pi_pos]
  have hπ1 : π/8 ≤ 1 := by linarith [C.pi_one]
  have hL := particleLip_pos k
  have hU := upper_pos k
  have hE : 0 ≤ A.err := norm_nonneg _
  have hLπ : (π/8)*particleLip k ≤ particleLip k := mul_le_of_le_one_left hL.le hπ1
  have hm := mul_le_mul_of_nonneg_right C.qbound (add_nonneg hE hd)
  have he := mul_nonneg (add_nonneg hU.le hL.le) hE
  have hld := mul_le_mul_of_nonneg_right hLπ hd
  nlinarith

lemma trivial_test {H Q : ℝ} (C : TestParameters k α π η H Q) (e : ℕ) (he : e ≤ A.start) :
    A.δ A.start ≤ Q*(A.err+A.δ e) := by
  have hq : 1 ≤ Q := by linarith [C.qlarge,upper_pos k]
  have hm := mul_le_mul_of_nonneg_right hq (add_nonneg (norm_nonneg (P.map A.x-P.map A.y)) (A.nonneg (A.node e) A.x))
  have hd := A.monotone he
  nlinarith [norm_nonneg (P.map A.x-P.map A.y)]

lemma launch (a e : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (hsa : A.start ≤ a) : A.δ a ≤ A.err+(upper k+1)*A.δ e := by
  have hae : a ≤ e := inclusive_age k _ _ _ _ e a ha
  by_cases heq : a = e
  · subst a
    nlinarith [A.nonneg (A.node e) A.x, norm_nonneg (P.map A.x-P.map A.y),upper_pos k]
  obtain ⟨l,hlen,hpath⟩ := A.suffix e (hsa.trans hae) he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have ht := P.launch_test A.zero A.X A.Y A.y z A.hy A.start e l a he hsa (lt_of_le_of_ne hae heq) ha hz hlen hpath
  have hl := (abs_le.mp (A.lipschitz (A.node a) A.x z)).2
  have hu := A.proxy_upper z
  rw [hzdist] at hl hu
  change A.δ a-_ ≤ _ at hl
  linarith

lemma budget {H Q : ℝ} (C : TestParameters k α π η H Q)
    (v β γ : ℝ) (hv : 0 ≤ v) (hβ : 0 < β) (hγ : 0 < γ)
    (hvb : C.c*v ≤ β) (hvg : C.c*v ≤ γ) (t : ℕ) :
    ((B (A.node t)).card:ℝ)*(2*(C.b*v)/β+2*(C.b*v)/γ) ≤ 1/2 := by
  have hh := gap_budget k β γ (C.c*v) hβ hγ (mul_nonneg C.c_pos.le hv) hvb hvg
  have heq : C.c*v/(8*((k:ℝ)+1)) = C.b*v := by rw [C.b_eq]; ring
  rw [heq] at hh
  apply le_trans _ hh
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast A.bag_bound (A.node t)) (by positivity [C.b_pos])

lemma bounded_tau {H Q : ℝ} (C : TestParameters k α π η H Q) (t : ℕ) : C.b*A.δ t ≤ 2*P.Δ := by
  have hh := mul_le_mul_of_nonneg_right C.b_one (A.nonneg (A.node t) A.x)
  have hb := A.bounded (A.node t) A.x
  nlinarith [P.Δ_pos]

lemma small {H Q : ℝ} (C : TestParameters k α π η H Q)
    (a e : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (has : a < A.start) (hDa : A.δ a ≤ H*A.δ A.start) :
    A.δ A.start ≤ Q*(A.err+A.δ e) := by
  by_cases hes : e ≤ A.start
  · exact A.trivial_test C e hes
  have hse : A.start < e := lt_of_not_ge hes
  obtain ⟨l,hlen,hpath⟩ := A.suffix e hse.le he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have hAa : A.δ A.start ≤ A.δ a := A.monotone has.le
  have hapos : 0 < A.δ a := A.positive.trans_le hAa
  have hrad : 4*η*A.δ a < A.δ A.start := by
    have hm := mul_le_mul_of_nonneg_left hDa (show 0 ≤ 4*η by positivity [C.eta_pos])
    have hh := mul_lt_mul_of_pos_right C.radius A.positive
    nlinarith
  have hamp : ∀ loc, GoodBump (D (A.node a)) α η ((seed (A.node a)).bump loc) A.x →
      ∀ v ∈ B (A.node A.start), A.δ A.start ≤ |D (A.node a) A.x-D (A.node a) v| ∨
        ∃ j, C.c*A.δ a ≤ |(seed (A.node a)).bump loc j A.x-(seed (A.node a)).bump loc j v| := by
    intro loc hg v hv
    obtain ⟨j,hj,hn,hzero⟩ := hg
    right
    refine ⟨j,?_⟩
    rw [hzero v (hrad.trans_le (A.lower_near A.start v hv)),sub_zero,abs_of_nonneg (hn A.x)]
    simpa only [C.c_eq,mul_assoc] using hj
  have ht := P.height_test A.X A.Y A.x A.y z A.hy A.start e l a A.start he le_rfl hse has ha hz hlen hpath
    (C.b*A.δ A.start) (A.δ A.start) (C.c*A.δ a) (by positivity [C.b_pos,A.positive])
    (A.bounded_tau C A.start) A.positive (mul_pos C.c_pos hapos) C.pi_pos.le hapos hamp
    (A.budget C (A.δ A.start) (A.δ A.start) (C.c*A.δ a) A.positive.le A.positive (mul_pos C.c_pos hapos)
      (by nlinarith [C.c_half,A.positive]) (mul_le_mul_of_nonneg_left hAa C.c_pos.le) A.start)
  have hu := A.proxy_upper z
  rw [hzdist] at ht hu
  exact A.numerical_test C (A.δ A.start) (A.δ e) (A.nonneg _ _) (ht.trans hu)

lemma obstruction {H Q : ℝ} (C : TestParameters k α π η H Q)
    (a e t : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (has : a < A.start) (hst : A.start ≤ t) (hte : t < e)
    (hgap : Q*(A.err+A.δ e) < A.δ t) :
    ∃ p ∈ B (A.node t), ∃ q ∈ B (A.node t), dist A.x p = A.δ t ∧
      A.δ t/4 ≤ dist p q ∧ dist p q ≤ 10*A.δ a := by
  have hQ : 0 < Q := by linarith [C.qlarge,upper_pos k]
  have hδ : 0 < A.δ t := lt_of_le_of_lt (mul_nonneg hQ.le (add_nonneg (norm_nonneg (P.map A.x-P.map A.y)) (A.nonneg _ _))) hgap
  have hDa : A.δ t ≤ A.δ a := A.monotone (has.le.trans hst)
  have hapos : 0 < A.δ a := hδ.trans_le hDa
  obtain ⟨p,hp,hpdist⟩ := A.near t
  by_contra hno
  have hno' : ∀ q ∈ B (A.node t), ¬(A.δ t/4 ≤ dist p q ∧ dist p q ≤ 10*A.δ a) := by
    intro q hq hh
    exact hno ⟨p,hp,q,hq,hpdist,hh⟩
  obtain ⟨v₀,hv₀,hgeo⟩ := A.geodesic a t (has.le.trans hst) (hte.le.trans he)
  have hamp : ∀ loc, GoodBump (D (A.node a)) α η ((seed (A.node a)).bump loc) A.x →
      ∀ v ∈ B (A.node t), A.δ t/2 ≤ |D (A.node a) A.x-D (A.node a) v| ∨
        ∃ j, C.c*A.δ a ≤ |(seed (A.node a)).bump loc j A.x-(seed (A.node a)).bump loc j v| := by
    intro loc hg v hv
    obtain ⟨j,hj,hn,hzero⟩ := hg
    have hj' : C.c*A.δ a ≤ (seed (A.node a)).bump loc j A.x := by simpa only [C.c_eq,mul_assoc] using hj
    have hr : 4*η*A.δ a < 9*A.δ a := by nlinarith [C.eta_small]
    have hh := near_far_scaled (B (A.node t)) A.x p v₀ (D (A.node a))
      ((seed (A.node a)).bump loc j) (A.δ t) (A.δ a) (4*η*A.δ a) (C.c*A.δ a)
      hδ hDa hpdist hv₀ (A.lower_near t) (A.lipschitz (A.node a)) rfl hgeo (A.nonneg _ _)
      hno' hr (mul_pos C.c_pos hapos) hj' hzero v hv
    exact hh.imp id (fun h => ⟨j,h⟩)
  obtain ⟨l,hlen,hpath⟩ := A.suffix e (hst.trans hte.le) he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have ht := P.height_test A.X A.Y A.x A.y z A.hy A.start e l a t he hst hte (has.trans_le hst) ha hz hlen hpath
    (C.b*A.δ t) (A.δ t/2) (C.c*A.δ a) (by positivity [C.b_pos])
    (A.bounded_tau C t) (by positivity) (mul_pos C.c_pos hapos) C.pi_pos.le hapos hamp
    (A.budget C (A.δ t) (A.δ t/2) (C.c*A.δ a) hδ.le (by positivity) (mul_pos C.c_pos hapos)
      (by nlinarith [C.c_half]) (mul_le_mul_of_nonneg_left hDa C.c_pos.le) t)
  have hu := A.proxy_upper z
  rw [hzdist] at ht hu
  exact (not_le_of_gt hgap) (A.numerical_test C (A.δ t) (A.δ e) (A.nonneg _ _) (ht.trans hu))

end PathGeometry
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
