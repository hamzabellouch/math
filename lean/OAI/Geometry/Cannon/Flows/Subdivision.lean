import Mathlib
import OAI.Geometry.Cannon.Flows.Node

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
open Set Filter Finset

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

structure Subdivision (X : Type*) where
  degree : X → ℕ
  child : (x : X) → Fin (degree x) → X
  prob : (x : X) → Fin (degree x) → ℝ
  prob_pos : ∀ x i, 0 < prob x i
  prob_sum : ∀ x, ∑ i, prob x i = 1

structure Population (X : Type*) where
  size : ℕ
  state : Fin size → X

namespace Subdivision

variable {X : Type*} (R : Subdivision X)

def Offspring (P : Population X) := Σ v : Fin P.size, Fin (R.degree (P.state v))

instance (P : Population X) : Fintype (R.Offspring P) := inferInstanceAs (Fintype (Σ v : Fin P.size, Fin (R.degree (P.state v))))

def next (P : Population X) : Population X where
  size := Fintype.card (R.Offspring P)
  state i := R.child (P.state ((Fintype.equivFin (R.Offspring P)).symm i).1)
    ((Fintype.equivFin (R.Offspring P)).symm i).2

def parentOf (P : Population X) : Fin (R.next P).size → Fin P.size :=
  fun i => ((Fintype.equivFin (R.Offspring P)).symm i).1

def probOf (P : Population X) : Fin (R.next P).size → ℝ := fun i =>
  R.prob (P.state ((Fintype.equivFin (R.Offspring P)).symm i).1)
    ((Fintype.equivFin (R.Offspring P)).symm i).2

lemma fiber_sum (P : Population X) (w : Fin P.size → ℝ) (v : Fin P.size) :
    ∑ i, (if R.parentOf P i = v then R.probOf P i*w (R.parentOf P i) else 0) = w v := by
  classical
  let e := Fintype.equivFin (R.Offspring P)
  have heq : ∑ i, (if R.parentOf P i = v then R.probOf P i*w (R.parentOf P i) else 0) =
      ∑ p : R.Offspring P, if p.1=v then R.prob (P.state p.1) p.2*w p.1 else 0 := by
    apply Fintype.sum_equiv e.symm
    intro i
    rfl
  rw [heq]
  change (∑ p : (Σ u : Fin P.size, Fin (R.degree (P.state u))),
    if p.1=v then R.prob (P.state p.1) p.2*w p.1 else 0) = w v
  rw [Fintype.sum_sigma]
  simp_rw [sum_ite_irrel,← sum_mul,R.prob_sum,one_mul,sum_const_zero]
  simp

def generation (x : X) : ℕ → Population X
  | 0 => ⟨1,fun _ => x⟩
  | n+1 => R.next (generation x n)

def weights (x : X) : (n : ℕ) → Fin (R.generation x n).size → ℝ
  | 0, _ => 1
  | n+1, i => R.probOf (R.generation x n) i *
      weights x n (R.parentOf (R.generation x n) i)

lemma weights_pos (x : X) : ∀ n i, 0 < R.weights x n i := by
  intro n
  induction n with
  | zero => intro i; exact zero_lt_one
  | succ n ih =>
    intro i
    exact mul_pos (R.prob_pos _ _) (ih _)

def flow (x : X) (good : X → Prop) : FiniteFlow where
  size n := (R.generation x n).size
  parent n := R.parentOf (R.generation x n)
  weight := R.weights x
  nonneg n i := (R.weights_pos x n i).le
  root_mass := by
    change (∑ _ : Fin 1, (1:ℝ)) = 1
    simp
  conserves n v := (R.fiber_sum (R.generation x n) (R.weights x n) v).symm
  good n v := good ((R.generation x n).state v)

theorem flow_step (x : X) (good : X → Prop) (n : ℕ)
    (i : Fin ((R.flow x good).size (n+1))) :
    (R.flow x good).weight (n+1) i = R.probOf (R.generation x n) i *
      (R.flow x good).weight n ((R.flow x good).parent n i) := rfl

end Subdivision

namespace FiniteFlow

variable (T : FiniteFlow)

def ancestor (n : ℕ) : (m : ℕ) → Fin (T.size (n+m)) → Fin (T.size n)
  | 0, v => v
  | m+1, v => ancestor n m (T.parent (n+m) v)

theorem conditional_weight {α : ℝ} (hα : 0 ≤ α)
    (hstep : ∀ n v, T.weight (n+1) v ≤ α*T.weight n (T.parent n v)) :
    ∀ n m v, T.weight (n+m) v ≤ α^m*T.weight n (T.ancestor n m v) := by
  intro n m
  induction m with
  | zero => intro v; simp [ancestor]
  | succ m ih =>
    intro v
    calc
      _ ≤ α*T.weight (n+m) (T.parent (n+m) v) := hstep _ _
      _ ≤ α*(α^m*T.weight n (T.ancestor n m (T.parent (n+m) v))) :=
        mul_le_mul_of_nonneg_left (ih _) hα
      _ = _ := by simp only [ancestor,pow_succ]; ring

theorem ancestor_conserves (n m : ℕ) (v : Fin (T.size n)) :
    ∑ w, (if T.ancestor n m w = v then T.weight (n+m) w else 0) = T.weight n v := by
  classical
  induction m with
  | zero =>
    change (∑ w : Fin (T.size n), if w=v then T.weight n w else 0) = T.weight n v
    simp
  | succ m ih =>
    calc
      _ = ∑ w, T.weight (n+m+1) w *
          (if T.ancestor n m (T.parent (n+m) w) = v then 1 else 0) := by
        apply sum_congr rfl
        intro w _
        simp only [ancestor,mul_ite,mul_one,mul_zero]
        rfl
      _ = ∑ u, T.weight (n+m) u * (if T.ancestor n m u = v then 1 else 0) :=
        (T.conserve_expectation (n+m) (fun u => if T.ancestor n m u = v then 1 else 0)).symm
      _ = _ := by simpa only [mul_ite,mul_one,mul_zero] using ih

end FiniteFlow

end CannonFlow

namespace CannonFlow.FiniteFlow

open Finset

variable (T : CannonFlow.FiniteFlow)

theorem descendant_displacement {X : Type*} [MetricSpace X]
    (center : (n : ℕ) → Fin (T.size n) → X) (r : ℕ → ℝ)
    (B C θ : ℝ) (hr : ∀ n, 0 ≤ r n) (hBC : B ≤ C*(1-θ))
    (hscale : ∀ n, r (n+1) = θ*r n)
    (hstep : ∀ n v, dist (center (n+1) v) (center n (T.parent n v)) ≤ B*r n) :
    ∀ n m v, dist (center (n+m) v) (center n (T.ancestor n m v)) ≤
      C*(r n-r (n+m)) := by
  intro n m
  induction m with
  | zero => intro v; simp [ancestor]
  | succ m ih =>
    intro v
    have hed : B*r (n+m) ≤ C*(r (n+m)-r (n+m+1)) := by
      have hh := mul_le_mul_of_nonneg_right hBC (hr (n+m))
      rw [hscale]
      nlinarith only [hh]
    calc
      _ ≤ dist (center (n+m+1) v) (center (n+m) (T.parent (n+m) v)) +
          dist (center (n+m) (T.parent (n+m) v))
            (center n (T.ancestor n m (T.parent (n+m) v))) := dist_triangle _ _ _
      _ ≤ B*r (n+m) + C*(r n-r (n+m)) := add_le_add (hstep _ _) (ih _)
      _ ≤ C*(r (n+m)-r (n+m+1)) + C*(r n-r (n+m)) := add_le_add hed le_rfl
      _ = _ := by ring_nf

theorem centers_separated {X : Type*} [MetricSpace X]
    (center : (n : ℕ) → Fin (T.size n) → X) (r : ℕ → ℝ)
    (B H θ : ℝ) (hr : ∀ n, 0 ≤ r n)
    (hscale : ∀ n, r (n+1) = θ*r n) (hbudget : H*θ ≤ H-2*B)
    (hroot : ∀ i j, i ≠ j → H*r 0 ≤ dist (center 0 i) (center 0 j))
    (hstep : ∀ n v, dist (center (n+1) v) (center n (T.parent n v)) ≤ B*r n)
    (hsibling : ∀ n i j, T.parent n i = T.parent n j → i ≠ j →
      H*r (n+1) ≤ dist (center (n+1) i) (center (n+1) j)) :
    ∀ n i j, i ≠ j → H*r n ≤ dist (center n i) (center n j) := by
  intro n
  induction n with
  | zero => exact hroot
  | succ n ih =>
    intro i j hij
    by_cases hp : T.parent n i = T.parent n j
    · exact hsibling n i j hp hij
    · have hpar := ih _ _ hp
      have hii := hstep n i
      have hjj := hstep n j
      have ht₁ := dist_triangle (center n (T.parent n i)) (center (n+1) i)
        (center n (T.parent n j))
      have ht₂ := dist_triangle (center (n+1) i) (center (n+1) j)
        (center n (T.parent n j))
      rw [dist_comm (center n (T.parent n i)) (center (n+1) i)] at ht₁
      have hb := mul_le_mul_of_nonneg_right hbudget (hr n)
      rw [hscale]
      nlinarith only [hpar,hii,hjj,ht₁,ht₂,hb]

end CannonFlow.FiniteFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

theorem source_rule_of_subdivisions {X : Type*} [MetricSpace X]
    (f : X → ℝ) (x₀ : X) (ε ell c₀ B H L Qg Qb : ℝ) (kmin D : ℕ)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (Y : SourceNode f x₀ ε ell c₀ B kmin → Finset X)
    (good : SourceNode f x₀ ε ell c₀ B kmin → Prop)
    (hY : ∀ v, ∀ y ∈ Y v, dist y v.center ≤ B*radius ell v.depth)
    (htrans : ∀ v,
      ∃ S : Finset (Y v),
        (∀ y ∈ S, 0 < fraction v.a v.b
          (lower f y (c₀*radius ell (v.depth+D))) (upper f y (c₀*radius ell (v.depth+D)))) ∧
        (∀ y ∈ S, ∀ z ∈ S, y ≠ z →
          H*radius ell (v.depth+D) < dist (y:X) z) ∧
        ∃ p : S → ℝ, (∀ y, 0 < p y) ∧ (∑ y, p y = 1) ∧
        (∀ y, p y ≤ L*fraction v.a v.b
          (lower f (y.val:X) (c₀*radius ell (v.depth+D)))
          (upper f (y.val:X) (c₀*radius ell (v.depth+D)))) ∧
        ∀ y, p y ≤ (if good v then Qg else Qb)*
          (fraction v.a v.b (lower f (y.val:X) (c₀*radius ell (v.depth+D)))
            (upper f (y.val:X) (c₀*radius ell (v.depth+D))))^2) :
    ∃ R : Subdivision (SourceNode f x₀ ε ell c₀ B kmin),
      (∀ v i, (R.child v i).depth=v.depth+D) ∧
      (∀ v i, dist (R.child v i).center v.center ≤ B*radius ell v.depth) ∧
      (∀ v i j, i ≠ j → H*radius ell (v.depth+D) <
        dist (R.child v i).center (R.child v j).center) ∧
      (∀ v i, R.prob v i*v.length ≤ L*(R.child v i).length) ∧
      (∀ v i, R.prob v i*v.length^2 ≤
        (if good v then Qg else Qb)*(R.child v i).length^2) ∧
      ∀ v i, (R.child v i).length ≤ v.length := by
  classical
  choose S hpos hsep p hp hsum hl hq using htrans
  let e := fun v => (Fintype.equivFin (S v)).symm
  let child := fun (v : SourceNode f x₀ ε ell c₀ B kmin) (i : Fin (Fintype.card (S v))) => v.child D ((e v i).val:X) hB hθ
    (hY v (e v i).val (e v i).val.property) (hpos v (e v i).val (e v i).property)
  let R : Subdivision (SourceNode f x₀ ε ell c₀ B kmin) := {
    degree := fun v => Fintype.card (S v)
    child := child
    prob := fun v i => p v (e v i)
    prob_pos := fun v i => hp v (e v i)
    prob_sum := fun v => by
      exact (Fintype.sum_equiv (e v) (fun i => p v (e v i)) (p v) (fun _ => rfl)).trans (hsum v) }
  have hlength (v) (i : Fin (R.degree v)) :
      (R.child v i).length = v.length * fraction v.a v.b
        (lower f ((e v i).val:X) (c₀*radius ell (v.depth+D)))
        (upper f ((e v i).val:X) (c₀*radius ell (v.depth+D))) := by
    exact SourceNode.child_length v D ((e v i).val:X) hB hθ
      (hY v (e v i).val (e v i).val.property) (hpos v (e v i).val (e v i).property)
  refine ⟨R,fun _ _ => rfl,fun v i => hY v (e v i).val (e v i).val.property,?_,?_,?_,?_⟩
  · intro v i j hij
    apply hsep v (e v i).val (e v i).property (e v j).val (e v j).property
    intro he
    exact hij ((e v).injective (Subtype.ext he))
  · intro v i
    change p v (e v i)*v.length ≤ L*(R.child v i).length
    have hh := mul_le_mul_of_nonneg_right (hl v (e v i)) v.length_pos.le
    calc
      _ ≤ _ := hh
      _ = _ := by rw [hlength]; ring
  · intro v i
    change p v (e v i)*v.length^2 ≤ (if good v then Qg else Qb)*(R.child v i).length^2
    have hh := mul_le_mul_of_nonneg_right (hq v (e v i)) (sq_nonneg v.length)
    calc
      _ ≤ _ := hh
      _ = _ := by rw [hlength]; ring
  · intro v i
    change min v.b _ - max v.a _ ≤ v.b-v.a
    exact sub_le_sub (min_le_left _ _) (le_max_left _ _)

end CannonNode

end

section

open Set Metric

namespace CannonNode

open Set Metric Filter Topology

theorem exists_nonlocally_constant {X : Type*} [MetricSpace X] (f : X → ℝ)
    (K : Set X) (hK : IsPreconnected K)
    (hvar : ∃ y ∈ K, ∃ z ∈ K, f y ≠ f z) :
    ∃ x ∈ K, ∀ r : ℝ, 0 < r → ∃ y ∈ ball x r, f y ≠ f x := by
  classical
  by_contra hn
  push Not at hn
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hc : IsLocallyConstant (fun x : K => f x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨r,hr,hconst⟩ := hn x x.property
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact hconst y (show (y:X) ∈ ball (x:X) r from hy)
  obtain ⟨y,hy,z,hz,hneq⟩ := hvar
  exact hneq (hc.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨z,hz⟩)

theorem root_at_scale {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (x : X) (Ω : Set X) (c₀ R : ℝ)
    (hc₀ : 0 < c₀) (hR : 0 < R) (hf : ContinuousOn f Ω)
    (hloc : closedBall x (c₀*R) ⊆ Ω)
    (hunit : ∀ y ∈ Ω, f y ∈ Icc (0:ℝ) 1)
    (hvar : ∀ r : ℝ, 0 < r → ∃ y ∈ ball x r, f y ≠ f x) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      lower f x (c₀*R) < a ∧ b < upper f x (c₀*R) := by
  obtain ⟨y,hy,hneq⟩ := hvar (c₀*R) (mul_pos hc₀ hR)
  exact exists_node_interval f x (c₀*R) (mul_pos hc₀ hR).le (hf.mono hloc)
    (fun y hy => hunit y (hloc hy))
    ⟨y,ball_subset_closedBall hy,x,mem_closedBall_self (mul_pos hc₀ hR).le,hneq⟩

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

structure SourceConstruction {X : Type*} [MetricSpace X] (f : X → ℝ) (x₀ : X)
    (ε ell c₀ A B H ρ : ℝ) (qdim n : ℕ) where
  kmin : ℕ
  small : ∀ k ≥ kmin, radius ell k ≤ ρ
  root : SourceNode f x₀ ε ell c₀ (B+1) kmin
  root_depth : root.depth=kmin
  pattern_small : c₀*radius ell (160*(qdim+1)*n) ≤ 1
  κ : ℝ
  κpos : 0 < κ
  Y : SourceNode f x₀ ε ell c₀ (B+1) kmin → Finset X
  Yloc : ∀ v, ∀ y ∈ Y v, (A-1)*radius ell v.depth ≤ dist y v.center ∧
    dist y v.center ≤ (B+1)*radius ell v.depth
  Ysep : ∀ v, ∀ y ∈ Y v, ∀ z ∈ Y v, y ≠ z →
    radius ell (v.depth+160*(qdim+1)*n) ≤ dist y z
  Ynet : ∀ v w, (A-1)*radius ell v.depth ≤ dist w v.center →
    dist w v.center ≤ (B+1)*radius ell v.depth →
    ∃ y ∈ Y v, dist w y ≤ radius ell (v.depth+160*(qdim+1)*n)
  rule : Subdivision (SourceNode f x₀ ε ell c₀ (B+1) kmin)
  child_depth : ∀ v i, (rule.child v i).depth=v.depth+160*(qdim+1)*n
  child_move : ∀ v i, dist (rule.child v i).center v.center ≤ (B+1)*radius ell v.depth
  child_sep : ∀ v i j, i ≠ j → H*radius ell (v.depth+160*(qdim+1)*n) <
    dist (rule.child v i).center (rule.child v j).center
  child_linear : ∀ v i, rule.prob v i*v.length ≤ Real.exp (-ell*n)*(rule.child v i).length
  child_quadratic : ∀ v i, rule.prob v i*v.length^2 ≤
    (if LiteralGood f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b κ
      then Real.exp (8*(qdim+1)*ell*n) else Real.exp (-((80*(qdim+1):ℝ)*ell*n)))*
        (rule.child v i).length^2
  child_length_le : ∀ v i, (rule.child v i).length ≤ v.length

lemma exists_source_threshold (ell B H L c₀ ε d₁ ρ : ℝ)
    (hell : 0 < ell) (hε : 0 < ε) (hd₁ : 0 < d₁) (hρ : 0 < ρ) :
    ∃ kmin : ℕ, ∀ k ≥ kmin,
      radius ell k ≤ ρ ∧ (B+1)*radius ell k ≤ 1 ∧ max H 1*radius ell k ≤ 1 ∧
      3*radius ell k ≤ 1 ∧ 2*B*radius ell k < d₁ ∧
      (B+2)*radius ell k ≤ ε ∧ 2*(B+1)*radius ell k ≤ ε ∧
      L*c₀*radius ell k ≤ ε := by
  have ht := radius_tendsto hell
  have hc (C t : ℝ) (ht' : 0 < t) : ∀ᶠ k : ℕ in atTop, C*radius ell k < t := by
    have hh : Tendsto (fun k => C*radius ell k) atTop (𝓝 0) := by
      simpa only [mul_zero] using ht.const_mul C
    exact hh.eventually (gt_mem_nhds ht')
  apply eventually_atTop.mp
  filter_upwards [ht.eventually (gt_mem_nhds hρ),hc (B+1) 1 zero_lt_one,
    hc (max H 1) 1 zero_lt_one,hc 3 1 zero_lt_one,hc (2*B) d₁ hd₁,
    hc (B+2) ε hε,hc (2*(B+1)) ε hε,hc (L*c₀) ε hε] with k hk hB hH h3 hd hε₁ hε₂ hL
  exact ⟨hk.le,hB.le,hH.le,h3.le,hd,hε₁.le,hε₂.le,hL.le⟩

theorem exists_source_construction {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B H c₀ C LE d₀ ell L : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hLE : 0 < LE) (hdc : d₀ ≤ 1/(9*LE)) (hell : 0 < ell)
    (hL : 1 ≤ L) (hLc : L*c₀ ≤ A)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) C LE)
    (hpaths : ∀ x u v : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist v x ≤ r →
      JoinedIn (ball x (L*r)) u v)
    (Ω : Set X) (f : X → ℝ) (hf : ContinuousOn f Ω)
    (hunit : ∀ y ∈ Ω, f y ∈ Icc (0:ℝ) 1)
    (K : ℝ → Set X) (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hK : ∀ t ∈ Ioo (0:ℝ) 1, IsPreconnected (K t) ∧ d₁ ≤ diam (K t) ∧
      ∀ y ∈ K t, y ∈ Ω → f y=t)
    (hhit : ∀ t ∈ Ioo (0:ℝ) 1, ∀ u v, ∀ p : Path u v, Set.range p ⊆ Ω →
      f u < t → t < f v → (K t ∩ Set.range p).Nonempty)
    (x₀ : X) (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ)
    (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (hvar : ∀ r : ℝ, 0 < r → ∃ y ∈ ball x₀ r, f y ≠ f x₀) :
    ∃ n : ℕ, 0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      Nonempty (SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n) := by
  obtain ⟨n,hns,hsc⟩ := ((eventually_scaled_subdivision qdim CP A B H c₀ C LE d₀ ell
    hpack hCP hA hAB hH hc₀ hC hLE hdc hell M hMnon hM δ ξ hξ ω hω hωmass h hexp).and
      (eventually_flow_scales qdim ell c₀ H C hell)).exists
  obtain ⟨hn,hθ,κ,hκ,hnode⟩ := hns
  obtain ⟨kmin,hsmall⟩ := exists_source_threshold ell B H L c₀ ε d₁ ρ hell hε hd₁ hρ
  have hB : 0 ≤ B+1 := by linarith only [hA,hAB]
  have hc₀pos : 0 < c₀ := by linarith only [hc₀]
  let V := SourceNode f x₀ ε ell c₀ (B+1) kmin
  have hnodeΩ (v : V) (w : X) (hw : dist w v.center ≤ (B+2)*radius ell v.depth) : w ∈ Ω := by
    have hx := mem_closedBall.mp (v.center_mem hB)
    have ht := dist_triangle w v.center x₀
    have hs := (hsmall v.depth v.lowerDepth).2.2.2.2.2.1
    apply hloc
    rw [mem_closedBall]
    linarith only [hx,ht,hw,hs]
  have hlocal (v : V) : closedBall v.center (L*c₀*radius ell v.depth) ⊆ Ω := by
    intro w hw
    apply hnodeΩ v w
    have hmul := mul_le_mul_of_nonneg_right hLc (radius_pos ell v.depth).le
    have hm := mul_le_mul_of_nonneg_right (by linarith only [hAB] : A ≤ B+2)
      (radius_pos ell v.depth).le
    exact (mem_closedBall.mp hw).trans (hmul.trans hm)
  have hrootloc : closedBall x₀ (c₀*radius ell kmin) ⊆ Ω := by
    intro w hw
    apply hloc
    have hs := (hsmall kmin le_rfl).2.2.2.2.2.2.2
    have hmul := mul_le_mul_of_nonneg_right hL (mul_pos hc₀pos (radius_pos ell kmin)).le
    rw [mem_closedBall] at hw ⊢
    nlinarith only [hs,hmul,hw,hε]
  obtain ⟨a,b,ha,hab,hb,hla,hub⟩ := root_at_scale f x₀ Ω c₀ (radius ell kmin) hc₀pos
    (radius_pos ell kmin) hf hrootloc hunit hvar
  let root : V := ⟨x₀,kmin,le_rfl,a,b,ha,hab,hb,⟨hla.le,hub.le⟩,by
    simpa only [dist_self,zero_add] using (hsmall kmin le_rfl).2.2.2.2.2.2.1⟩
  choose Y hYloc hYsep hYnet using fun v : V => annular_net v.center A B (radius ell v.depth)
    (radius ell (v.depth+160*(qdim+1)*n)) (radius_pos _ _)
  let good := fun v : V => LiteralGood f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b κ
  have htrans (v : V) : LiteralTransitions f (Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n))
      v.a v.b κ H (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n))
        (Real.exp (-((80*(qdim+1):ℝ)*ell*n))) := by
    have hv (t : ℝ) (ht : t ∈ Ioo v.a v.b) : t ∈ Ioo (0:ℝ) 1 :=
      ⟨v.apos.trans ht.1,ht.2.trans v.bone⟩
    have hlevelhit := node_level_hits f Ω K v.center (radius ell v.depth) c₀ L v.a v.b
      (radius_pos _ _) hc₀pos hL hf (hlocal v) v.straddle
      (fun u w hu hw => by
        simpa only [mul_assoc] using hpaths v.center u w (c₀*radius ell v.depth)
          (mul_pos hc₀pos (radius_pos _ _)) (mem_closedBall.mp hu) (mem_closedBall.mp hw))
      (fun t ht => hhit t (hv t ht))
    have hk := hsmall v.depth v.lowerDepth
    exact hnode v.center v.depth (Y v) Ω f K v.a v.b v.ab hk.2.1 hk.2.2.1 hk.2.2.2.1
      (hYloc v) (hYsep v) (hYnet v) (hnodeΩ v) hf
      (fun t ht => (hK t (hv t ht)).1)
      (fun t ht => by
        obtain ⟨w,hw,hd⟩ := hlevelhit t ht
        exact ⟨w,hw,hd.trans (mul_le_mul_of_nonneg_right hLc (radius_pos _ _).le)⟩)
      (fun t ht => hk.2.2.2.2.1.trans_le (hK t (hv t ht)).2.1)
      (fun t ht => (hK t (hv t ht)).2.2)
  obtain ⟨R,hdepth,hmove,hsep,hlin,hquad,hlen⟩ := source_rule_of_subdivisions f x₀ ε ell c₀ (B+1) H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n)))
    kmin (160*(qdim+1)*n) hB (hθ.le.trans (by norm_num)) Y good
    (fun v y hy => (hYloc v y hy).2) htrans
  exact ⟨n,hn,hθ,⟨{
    kmin := kmin, small := fun k hk => (hsmall k hk).1, root := root, root_depth := rfl, pattern_small := hsc.2.2.1,
    κ := κ, κpos := hκ, Y := Y, Yloc := hYloc, Ysep := hYsep, Ynet := hYnet,
    rule := R, child_depth := hdepth, child_move := hmove, child_sep := hsep,
    child_linear := hlin, child_quadratic := hquad, child_length_le := hlen }⟩⟩

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

namespace CannonFlow.Subdivision

open Finset

variable {X : Type*} (R : Subdivision X) (x : X)

lemma generation_property (P : X → Prop) (hx : P x)
    (hc : ∀ y i, P y → P (R.child y i)) :
    ∀ n i, P ((R.generation x n).state i) := by
  intro n
  induction n with
  | zero => intro i; exact hx
  | succ n ih =>
    intro i
    let u := ((Fintype.equivFin (R.Offspring (R.generation x n))).symm i)
    exact hc _ u.2 (ih u.1)

lemma generation_depth (dep : X → ℕ) (D : ℕ)
    (hdep : ∀ y i, dep (R.child y i)=dep y+D) :
    ∀ n i, dep ((R.generation x n).state i)=dep x+D*n := by
  intro n
  induction n with
  | zero => intro i; simp [generation]
  | succ n ih =>
    intro i
    let u := ((Fintype.equivFin (R.Offspring (R.generation x n))).symm i)
    change dep (R.child ((R.generation x n).state u.1) u.2)=_
    rw [hdep,ih,Nat.mul_succ,Nat.add_assoc]

lemma generation_siblings {Z : Type*} [MetricSpace Z] (pos : X → Z)
    (sep : X → ℝ) (hs : ∀ y i j, i ≠ j → sep y ≤ dist (pos (R.child y i)) (pos (R.child y j)))
    (n : ℕ) (i j : Fin (R.generation x (n+1)).size)
    (hp : R.parentOf (R.generation x n) i=R.parentOf (R.generation x n) j) (hij : i ≠ j) :
    sep ((R.generation x n).state (R.parentOf (R.generation x n) i)) ≤
      dist (pos ((R.generation x (n+1)).state i)) (pos ((R.generation x (n+1)).state j)) := by
  let e := Fintype.equivFin (R.Offspring (R.generation x n))
  obtain ⟨⟨u,ui⟩,rfl⟩ := e.surjective i
  obtain ⟨⟨v,vj⟩,rfl⟩ := e.surjective j
  have huv : u=v := by
    change (e.symm (e ⟨u,ui⟩)).1 = (e.symm (e ⟨v,vj⟩)).1 at hp
    erw [e.symm_apply_apply, e.symm_apply_apply] at hp
    exact hp
  subst v
  have hne : ui ≠ vj := by
    intro he
    subst vj
    exact hij rfl
  change sep ((R.generation x n).state (e.symm (e ⟨u,ui⟩)).1) ≤
    dist (pos (R.child ((R.generation x n).state (e.symm (e ⟨u,ui⟩)).1)
      (e.symm (e ⟨u,ui⟩)).2))
      (pos (R.child ((R.generation x n).state (e.symm (e ⟨u,vj⟩)).1)
      (e.symm (e ⟨u,vj⟩)).2))
  erw [e.symm_apply_apply, e.symm_apply_apply]
  exact hs _ ui vj hne

end CannonFlow.Subdivision

end

end
end
end
end
end
end
end
end
end

end OAI
