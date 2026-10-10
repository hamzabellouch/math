import Mathlib
import OAI.Geometry.Cannon.Flows.GoodCandidates
import OAI.Geometry.Cannon.Modulus.AnnularNet
import OAI.Geometry.Cannon.CirclePacking.Radius

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
namespace CannonNode

open Set Metric

structure SourceNode {X : Type*} [MetricSpace X] (f : X → ℝ) (x₀ : X)
    (ε ell c₀ B : ℝ) (kmin : ℕ) where
  center : X
  depth : ℕ
  lowerDepth : kmin ≤ depth
  a : ℝ
  b : ℝ
  apos : 0 < a
  ab : a < b
  bone : b < 1
  straddle : lower f center (c₀*radius ell depth) ≤ a ∧
    b ≤ upper f center (c₀*radius ell depth)
  reserve : dist center x₀+2*B*radius ell depth ≤ ε

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ B : ℝ} {kmin : ℕ}

namespace SourceNode

def length (v : SourceNode f x₀ ε ell c₀ B kmin) : ℝ := v.b-v.a

lemma length_pos (v : SourceNode f x₀ ε ell c₀ B kmin) : 0 < v.length := sub_pos.mpr v.ab

def child (v : SourceNode f x₀ ε ell c₀ B kmin) (D : ℕ) (y : X)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (hy : dist y v.center ≤ B*radius ell v.depth)
    (ht : 0 < fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
      (upper f y (c₀*radius ell (v.depth+D)))) :
    SourceNode f x₀ ε ell c₀ B kmin where
  center := y
  depth := v.depth+D
  lowerDepth := v.lowerDepth.trans (Nat.le_add_right _ _)
  a := childLower v.a (lower f y (c₀*radius ell (v.depth+D)))
  b := childUpper v.b (upper f y (c₀*radius ell (v.depth+D)))
  apos := v.apos.trans_le (le_max_left _ _)
  ab := (fraction_pos_iff v.ab).mp ht
  bone := (min_le_left _ _).trans_lt v.bone
  straddle := ⟨le_max_right _ _,min_le_right _ _⟩
  reserve := by
    have hR := radius_pos ell v.depth
    have htR := mul_le_mul_of_nonneg_right hθ hR.le
    have hB' := mul_le_mul_of_nonneg_left htR (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
    have htri := dist_triangle y v.center x₀
    rw [radius_add]
    nlinarith only [v.reserve,hy,htri,hB']

lemma child_length (v : SourceNode f x₀ ε ell c₀ B kmin) (D : ℕ) (y : X)
    (hB : 0 ≤ B) (hθ : radius ell D ≤ 1/2)
    (hy : dist y v.center ≤ B*radius ell v.depth)
    (ht : 0 < fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
      (upper f y (c₀*radius ell (v.depth+D)))) :
    (v.child D y hB hθ hy ht).length = v.length *
      fraction v.a v.b (lower f y (c₀*radius ell (v.depth+D)))
        (upper f y (c₀*radius ell (v.depth+D))) := by
  exact positive_child_length v.ab ht

lemma center_mem (v : SourceNode f x₀ ε ell c₀ B kmin) (hB : 0 ≤ B) :
    v.center ∈ closedBall x₀ ε := by
  have hh : 0 ≤ 2*B*radius ell v.depth := mul_nonneg (mul_nonneg (by norm_num) hB) (radius_pos ell v.depth).le
  exact mem_closedBall.mpr (by linarith only [v.reserve,hh])

lemma root (k : ℕ) (hk : kmin ≤ k) (a b : ℝ) (ha : 0 < a)
    (hab : a < b) (hb : b < 1)
    (hs : lower f x₀ (c₀*radius ell k) ≤ a ∧ b ≤ upper f x₀ (c₀*radius ell k))
    (hroom : 2*B*radius ell k ≤ ε) :
    Nonempty (SourceNode f x₀ ε ell c₀ B kmin) :=
  ⟨⟨x₀,k,hk,a,b,ha,hab,hb,hs,by simpa only [dist_self,zero_add] using hroom⟩⟩

end SourceNode

end CannonNode

end

section

open Set Metric

namespace CannonMagnification

def Expansion {X : Type*} [MetricSpace X] (h : X ≃ₜ X) (x : X)
    (r C L : ℝ) : Prop :=
  ∀ y z,
    dist (h y) (h z) * max r (dist x y) * max r (dist x z) ≤ C*r*dist y z ∧
    r*dist y z ≤ L*dist (h y) (h z) * max r (dist x y) * max r (dist x z)

lemma expansion_ball_bounds {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x : X) (r C L B : ℝ) (hr : 0 < r) (hL : 0 < L) (hB : 1 ≤ B)
    (hexp : Expansion h x r C L) (y z : X)
    (hy : dist y x ≤ B*r) (hz : dist z x ≤ B*r) :
    dist (h y) (h z) ≤ C/r*dist y z ∧
      (1/(L*B^2))/r*dist y z ≤ dist (h y) (h z) := by
  have hE : 0 ≤ dist (h y) (h z) := dist_nonneg
  have hBr : r ≤ B*r := by nlinarith
  have hby : max r (dist x y) ≤ B*r := max_le hBr (by simpa only [dist_comm] using hy)
  have hbz : max r (dist x z) ≤ B*r := max_le hBr (by simpa only [dist_comm] using hz)
  have hmy : 0 ≤ max r (dist x y) := hr.le.trans (le_max_left _ _)
  have hmz : 0 ≤ max r (dist x z) := hr.le.trans (le_max_left _ _)
  have h₁ : dist (h y) (h z)*r*r ≤ C*r*dist y z := by
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (le_max_left _ _) hE)
      (le_max_left _ _) hr.le (mul_nonneg hE hmy)).trans (hexp y z).1
  have h₂ : r*dist y z ≤ L*dist (h y) (h z)*(B*r)*(B*r) := by
    exact (hexp y z).2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hby (mul_nonneg hL.le hE))
      hbz hmz (by positivity))
  constructor
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).mpr
    have hh : (dist (h y) (h z)*r)*r ≤ (C*dist y z)*r := by nlinarith [h₁]
    exact (mul_le_mul_iff_left₀ hr).mp hh
  · have hden : 0 < L*B^2*r := mul_pos (mul_pos hL (sq_pos_of_pos (zero_lt_one.trans_le hB))) hr
    have hraw : dist y z ≤ dist (h y) (h z)*(L*B^2*r) := by
      apply (mul_le_mul_iff_left₀ hr).mp
      nlinarith [h₂]
    have hdiv : dist y z/(L*B^2*r) ≤ dist (h y) (h z) := (div_le_iff₀ hden).mpr hraw
    convert hdiv using 1; ring

end CannonMagnification

end

section

open Set Metric

namespace CannonNode

open Set Metric

theorem node_level_hits {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (Ω : Set X) (K : ℝ → Set X) (x : X) (R c₀ L a b : ℝ)
    (hR : 0 < R) (hc₀ : 0 < c₀) (hL : 1 ≤ L)
    (hf : ContinuousOn f Ω) (hloc : closedBall x (L*c₀*R) ⊆ Ω)
    (hnode : lower f x (c₀*R) ≤ a ∧ b ≤ upper f x (c₀*R))
    (hpaths : ∀ u v, u ∈ closedBall x (c₀*R) → v ∈ closedBall x (c₀*R) →
      JoinedIn (ball x (L*c₀*R)) u v)
    (hhit : ∀ t ∈ Ioo a b, ∀ u v, ∀ p : Path u v, Set.range p ⊆ Ω →
      f u < t → t < f v → (K t ∩ Set.range p).Nonempty) :
    ∀ t ∈ Ioo a b, ∃ y ∈ K t, dist y x ≤ L*c₀*R := by
  have hsub : closedBall x (c₀*R) ⊆ closedBall x (L*c₀*R) :=
    closedBall_subset_closedBall (by nlinarith only [hL,mul_pos hc₀ hR])
  obtain ⟨⟨u,hu,huv⟩,⟨v,hv,hvv⟩⟩ := ball_extrema (mul_pos hc₀ hR).le (hf.mono (hsub.trans hloc))
  obtain ⟨p,hp⟩ := hpaths u v hu hv
  have hpΩ : range p ⊆ Ω := by
    rintro _ ⟨t,rfl⟩
    exact hloc (ball_subset_closedBall (hp t))
  intro t ht
  have hu' : f u < t := by rw [huv]; exact hnode.1.trans_lt ht.1
  have hv' : t < f v := by rw [hvv]; exact ht.2.trans_le hnode.2
  obtain ⟨z,hz,⟨s,rfl⟩⟩ := hhit t ht u v p hpΩ hu' hv'
  exact ⟨p s,hz,(mem_ball.mp (hp s)).le⟩

lemma exists_node_interval {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X → ℝ) (x : X) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall x r))
    (hunit : ∀ y ∈ closedBall x r, f y ∈ Icc (0:ℝ) 1)
    (hvar : ∃ y ∈ closedBall x r, ∃ z ∈ closedBall x r, f y ≠ f z) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ lower f x r < a ∧ b < upper f x r := by
  obtain ⟨⟨v,hv,hvv⟩,⟨w,hw,hww⟩⟩ := ball_extrema hr hf
  have hlu : lower f x r < upper f x r := by
    obtain ⟨y,hy,z,hz,hneq⟩ := hvar
    have hylu := ball_range hf hy
    have hzlu := ball_range hf hz
    by_contra hn
    have hh := le_of_not_gt hn
    have hyz : f y=f z := by linarith only [hylu.1,hylu.2,hzlu.1,hzlu.2,hh]
    exact hneq hyz
  have hl : 0 ≤ lower f x r := by rw [← hvv]; exact (hunit v hv).1
  have hu : upper f x r ≤ 1 := by rw [← hww]; exact (hunit w hw).2
  refine ⟨(2*lower f x r+upper f x r)/3,(lower f x r+2*upper f x r)/3,?_,?_,?_,?_,?_⟩ <;>
    linarith only [hlu,hl,hu]

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

def LiteralGood {X : Type*} [MetricSpace X] (f : X → ℝ) (Y : Finset X)
    (c₀ r a b κ : ℝ) : Prop :=
  GoodCandidates (fun y : Y => lower f y (2*r)) (fun y : Y => upper f y (2*r))
    (fun y : Y => lower f y (c₀*r)) (fun y : Y => upper f y (c₀*r)) a b κ

def LiteralTransitions {X : Type*} [MetricSpace X] (f : X → ℝ) (Y : Finset X)
    (c₀ r a b κ H L Qg Qb : ℝ) : Prop :=
  ∃ S : Finset Y,
    (∀ y ∈ S, 0 < fraction a b (lower f y (c₀*r)) (upper f y (c₀*r))) ∧
    (∀ y ∈ S, ∀ z ∈ S, y ≠ z → H*r < dist (y:X) z) ∧
    ∃ p : S → ℝ, (∀ y, 0 < p y) ∧ (∑ y, p y = 1) ∧
    (∀ y, p y ≤ L*fraction a b (lower f (y.val:X) (c₀*r)) (upper f (y.val:X) (c₀*r))) ∧
    ∀ y, p y ≤ (if LiteralGood f Y c₀ r a b κ then Qg else Qb)*
      (fraction a b (lower f (y.val:X) (c₀*r)) (upper f (y.val:X) (c₀*r)))^2

lemma candidate_slack {X : Type*} [MetricSpace X] (Q : ℕ) (CP B ell : ℝ)
    (hCP : 0 ≤ CP) (hB : 0 ≤ B) (D : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Y : Finset X) (R r : ℝ), 0 < r →
      (Y.card:ℝ) ≤ CP*((B+1)*R/r)^Q → R/r=Real.exp (ell*D) →
      (Y.card:ℝ)*κ ≤ 1/8 := by
  let C := CP*(B+1)^Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let E := Real.exp (ell*D)^Q
  have hE : 0 < E := pow_pos (Real.exp_pos _) _
  let κ := 1/(8*max C 1*E)
  have hmax : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hden : 0 < 8*max C 1*E := by positivity
  refine ⟨κ,one_div_pos.mpr hden,?_⟩
  intro Y R r _hr hcard hratio
  have hcard' : (Y.card:ℝ) ≤ C*E := by
    convert hcard using 1
    rw [mul_div_assoc, hratio,mul_pow]
    dsimp [C,E]
    ring
  have hh : (Y.card:ℝ) ≤ max C 1*E := hcard'.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le)
  change (Y.card:ℝ)*(1/(8*max C 1*E)) ≤ 1/8
  rw [mul_one_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hh]

theorem eventually_scaled_subdivision {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B H c₀ C LE d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hLE : 0 < LE) (hdc : d₀ ≤ 1/(9*LE)) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (δ : ℕ → Type*) [∀ j, Fintype (δ j)] (ξ : ∀ j, δ j → X)
    (hξ : ∀ j i i', i ≠ i' → radius ell j ≤ dist (ξ j i) (ξ j i'))
    (ω : ∀ j, δ j → ℝ) (hω : ∀ j, MacroscopicAdmissible (ξ j) (radius ell j) d₀ (ω j))
    (hωmass : ∀ j, (∑ i, (ω j i)^2) ≤ M j)
    (h : X → ℕ → X ≃ₜ X)
    (hexp : ∀ x k, Expansion (h x k) x (radius ell k) C LE) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ (x : X) (k : ℕ) (Y : Finset X)
        (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X) (a b : ℝ),
      let R := radius ell k
      let r := radius ell (k+160*(qdim+1)*n)
      a < b → (B+1)*R ≤ 1 → max H 1*R ≤ 1 → 3*R ≤ 1 →
      (∀ y ∈ Y, (A-1)*R ≤ dist y x ∧ dist y x ≤ (B+1)*R) →
      (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → r ≤ dist y z) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R → ∃ y ∈ Y, dist v y ≤ r) →
      (∀ v, dist v x ≤ (B+2)*R → v ∈ Ω) → ContinuousOn f Ω →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      LiteralTransitions f Y c₀ r a b κ H (Real.exp (-ell*n))
        (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n))) := by
  have hB : 0 ≤ B := by linarith only [hA,hAB]
  have hc : 0 < 1/(9*LE) := by positivity
  have hs := uniform_literal_subdivision qdim CP A B H c₀ C (1/(9*LE)) d₀ ell
    hpack hCP hA hAB hH hc₀ hC hc hdc hell M hMnon hM
  have hsc := eventually_flow_scales qdim ell c₀ H (max (C+2) (max (1/(9*LE)) 1)) hell
  filter_upwards [hs,hsc] with n hn hscale
  obtain ⟨κ,hκ,hκcount⟩ := candidate_slack (X:=X) qdim CP B ell hCP hB (160*(qdim+1)*n)
  refine ⟨hscale.1,hscale.2.1,κ,hκ,?_⟩
  intro x k Y Ω f K a b
  dsimp only
  let R := radius ell k
  let r := radius ell (k+160*(qdim+1)*n)
  let s := radius ell (k+2*n)
  have hR : 0 < R := radius_pos _ _
  have hr : 0 < r := radius_pos _ _
  have hsp : 0 < s := radius_pos _ _
  intro hab hRone hCone hthree hY hYsep hYnet hΩ hf hK hinner hdiam hlevel
  have hd : 2 ≤ 160*(qdim+1) := by omega
  have hdr : 2*n ≤ 160*(qdim+1)*n := Nat.mul_le_mul_right n hd
  have hrs : r ≤ s := radius_antitone hell.le (Nat.add_le_add_left hdr k)
  have hsR : s ≤ R := radius_antitone hell.le (Nat.le_add_right k (2*n))
  have hrR : r ≤ R := hrs.trans hsR
  have hSR : s ≤ R/4 := by
    dsimp [s,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.2.2.1 hR.le]
  have hcR : c₀*r ≤ R := by
    dsimp [r,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.1 hR.le]
  have hHR : 2*((H+3)*r) ≤ R := by
    dsimp [r,R]
    rw [radius_add]
    nlinarith only [mul_le_mul_of_nonneg_right hscale.2.2.2.1 hR.le]
  have hratioS : R/s=Real.exp (2*ell*n) := by
    dsimp [R,s]
    rw [radius_ratio]
    congr 1
    push_cast
    ring
  have hratioR : R/r=Real.exp ((160*(qdim+1):ℝ)*ell*n) := by
    dsimp [R,r]
    rw [radius_ratio]
    congr 1
    push_cast
    ring
  have hrr : r/s=radius ell ((160*(qdim+1)-2)*n) := by
    dsimp [r,s]
    rw [radius_sub_ratio ell k _ _ hdr, Nat.sub_mul]
  have hκY : (Fintype.card Y:ℝ)*κ ≤ 1/8 := by
    rw [Fintype.card_coe]
    apply hκcount Y R r hr
    · exact hpack x ((B+1)*R) r hr (hrR.trans (by nlinarith only [hB,hR])) hRone Y
        (fun y hy => by simpa only [dist_comm] using (hY y hy).2) hYsep
    · dsimp [R,r]
      exact radius_ratio _ _ _
  obtain ⟨T,hT,hTsep,hTnet⟩ := annular_net x A B R s hsp
  have htrans : max (C+2) (max (1/(9*LE)) 1)*(r/s) ≤ 1 := by
    rw [hrr]
    exact hscale.2.2.2.2.2
  have hmap (z : T) (v v' : X) (hv : dist v (z:X) ≤ 3*s) (hv' : dist v' (z:X) ≤ 3*s) :
      dist (h z (k+2*n) v) (h z (k+2*n) v') ≤ C/s*dist v v' ∧
      (1/(9*LE))/s*dist v v' ≤ dist (h z (k+2*n) v) (h z (k+2*n) v') := by
    have hh := expansion_ball_bounds (h z (k+2*n)) z s C LE 3 hsp hLE (by norm_num)
      (hexp z (k+2*n)) v v' hv hv'
    simpa only [show (3 : ℝ)^2 = 9 by norm_num, mul_comm LE 9] using hh
  have htarget : ∀ i j, i ≠ j → r/s ≤ dist (ξ ((160*(qdim+1)-2)*n) i) (ξ ((160*(qdim+1)-2)*n) j) := by
    rw [hrr]
    exact hξ _
  have hweight : MacroscopicAdmissible (ξ ((160*(qdim+1)-2)*n)) (r/s) d₀
      (ω ((160*(qdim+1)-2)*n)) := by rw [hrr]; exact hω _
  exact hn (fun y : Y => (y:X)) (fun z : T => (z:X)) (ξ ((160*(qdim+1)-2)*n))
    (fun z : T => h z (k+2*n)) x Ω f K a b κ R r s hab hκ hκY hR hr hsp hrs hSR hcR hHR
    hRone ((mul_le_mul_of_nonneg_left hrR (le_max_right H 1 |>.trans' zero_le_one)).trans hCone)
    ((mul_le_mul_of_nonneg_left hsR (by norm_num : (0:ℝ) ≤ 3)).trans hthree) htrans hratioS hratioR
    (fun y => (hY y y.property).2)
    (fun y z hyz => hYsep y y.property z z.property (fun he => hyz (Subtype.ext he)))
    (fun y z hyz => hTsep y y.property z z.property (fun he => hyz (Subtype.ext he)))
    htarget (fun z => by simpa only [dist_comm] using (hT z z.property).2)
    (fun v hl hu => by obtain ⟨y,hy,hd⟩ := hYnet v hl hu; exact ⟨⟨y,hy⟩,by simpa only [dist_comm] using hd⟩)
    (fun v hl hu => by obtain ⟨z,hz,hd⟩ := hTnet v hl hu; exact ⟨⟨z,hz⟩,hd⟩)
    hΩ hf hK hinner hdiam hlevel hmap (ω ((160*(qdim+1)-2)*n)) hweight (hωmass _)

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

structure FiniteFlow where
  size : ℕ → ℕ
  parent : (n : ℕ) → Fin (size (n+1)) → Fin (size n)
  weight : (n : ℕ) → Fin (size n) → ℝ
  nonneg : ∀ n v, 0 ≤ weight n v
  root_mass : ∑ v, weight 0 v = 1
  conserves : ∀ n v, weight n v = ∑ w, if parent n w = v then weight (n+1) w else 0
  good : (n : ℕ) → Fin (size n) → Prop

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

lemma conserve_expectation (n : ℕ) (f : Fin (T.size n) → ℝ) :
    ∑ v, T.weight n v * f v = ∑ w, T.weight (n+1) w * f (T.parent n w) := by
  classical
  simp_rw [T.conserves n, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro w hw
  simp only [ite_mul, zero_mul]
  simp

lemma total_mass (n : ℕ) : ∑ v, T.weight n v = 1 := by
  induction n with
  | zero => exact T.root_mass
  | succ n ih =>
    have h := T.conserve_expectation n (fun _ => 1)
    simpa only [mul_one] using h.symm.trans (by simpa only [mul_one] using ih)

def badCount : (n : ℕ) → Fin (T.size n) → ℕ
  | 0, _ => 0
  | n+1, v => badCount n (T.parent n v) + if T.good n (T.parent n v) then 0 else 1

def expectedBad (n : ℕ) : ℝ := ∑ v, T.weight n v * (T.badCount n v : ℝ)

def badMass (n : ℕ) : ℝ := ∑ v, T.weight n v * if T.good n v then 0 else 1

def goodMass (n : ℕ) : ℝ := ∑ v, T.weight n v * if T.good n v then 1 else 0

lemma badMass_nonneg (n : ℕ) : 0 ≤ T.badMass n := by
  classical
  apply sum_nonneg
  intro v hv
  exact mul_nonneg (T.nonneg n v) (by split_ifs <;> norm_num)

lemma good_add_bad (n : ℕ) : T.goodMass n + T.badMass n = 1 := by
  classical
  unfold goodMass badMass
  rw [← sum_add_distrib]
  convert T.total_mass n using 1
  apply sum_congr rfl
  intro v hv
  split_ifs <;> ring

lemma expectedBad_succ (n : ℕ) : T.expectedBad (n+1) = T.expectedBad n + T.badMass n := by
  classical
  unfold expectedBad badMass
  simp only [badCount, Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, mul_add, sum_add_distrib]
  exact congrArg₂ (· + ·)
    (T.conserve_expectation n (fun v => (T.badCount n v : ℝ))).symm
    (T.conserve_expectation n (fun v => if T.good n v then 0 else 1)).symm

lemma expectedBad_eq_sum (n : ℕ) : T.expectedBad n = ∑ k ∈ range n, T.badMass k := by
  induction n with
  | zero => simp [expectedBad, badCount]
  | succ n ih => rw [T.expectedBad_succ, ih, sum_range_succ]

lemma expectedBad_bound {c E : ℝ} (_hc : 0 < c)
    (henergy : ∀ n, ∑ v, T.weight n v *
      Real.exp (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n)) ≤ E)
    (n : ℕ) : c * ((11 / 20 : ℝ) * T.expectedBad n - (1 / 20 : ℝ) * n) + 1 ≤ E := by
  have htan : ∑ v, T.weight n v *
      (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n) + 1) ≤ E := by
    apply le_trans _ (henergy n)
    apply sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (T.nonneg n v)
  have heq : (∑ v, T.weight n v *
      (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n) + 1)) =
      c * ((11 / 20 : ℝ) * T.expectedBad n - (1 / 20 : ℝ) * n) + 1 := by
    calc
      _ = ∑ v, ((c * (11 / 20 : ℝ)) * (T.weight n v * T.badCount n v) +
            (1 - c * (1 / 20 : ℝ) * n) * T.weight n v) := by
        apply sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, T.total_mass]; unfold expectedBad; ring
  rwa [heq] at htan

theorem arbitrarily_late_good_levels {c E : ℝ} (hc : 0 < c)
    (henergy : ∀ n, ∑ v, T.weight n v *
      Real.exp (c * ((11 / 20 : ℝ) * T.badCount n v - (1 / 20 : ℝ) * n)) ≤ E) :
    ∀ N : ℕ, ∃ n ≥ N, (1 / 2 : ℝ) ≤ T.goodMass n := by
  classical
  intro N
  by_contra hn
  have hbad : ∀ n, N ≤ n → (1 / 2 : ℝ) ≤ T.badMass n := by
    intro n hnN
    have hg : T.goodMass n < 1 / 2 := lt_of_not_ge (fun h => hn ⟨n,hnN,h⟩)
    linarith [T.good_add_bad n]
  have hlarge : ∃ n : ℕ, N ≤ n ∧ E + c * (11 / 40 : ℝ) * N < c * (9 / 40 : ℝ) * n + 1 := by
    obtain ⟨m,hm⟩ := exists_nat_gt ((E + c * (11 / 40 : ℝ) * N) / (c * (9 / 40 : ℝ)))
    refine ⟨max m N,le_max_right _ _,?_⟩
    have hd : 0 < c * (9 / 40 : ℝ) := by positivity
    have hh : E + c * (11 / 40 : ℝ) * N < c * (9 / 40 : ℝ) * m := by simpa [mul_comm] using (div_lt_iff₀ hd).mp hm
    have hmn : (m : ℝ) ≤ max m N := by exact_mod_cast le_max_left m N
    nlinarith
  obtain ⟨n,hnN,hnE⟩ := hlarge
  have hsum : ((n - N : ℕ) : ℝ) * (1 / 2 : ℝ) ≤ T.expectedBad n := by
    rw [T.expectedBad_eq_sum]
    have he := sum_le_sum (s := Ico N n) (fun k hk => hbad k (mem_Ico.mp hk).1)
    have hs : ∑ k ∈ Ico N n, T.badMass k ≤ ∑ k ∈ range n, T.badMass k :=
      sum_le_sum_of_subset_of_nonneg (by intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2)
        (fun k _ _ => T.badMass_nonneg k)
    simpa using he.trans hs
  rw [Nat.cast_sub hnN] at hsum
  have hb := T.expectedBad_bound hc henergy n
  nlinarith

end FiniteFlow

lemma probabilities_of_capacity {ι : Type*} [Fintype ι] (cap : ι → ℝ)
    (hcap : ∀ i, 0 ≤ cap i) (hmass : 1 ≤ ∑ i, cap i) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ ∀ i, p i ≤ cap i := by
  let S := ∑ i, cap i
  have hS : 0 < S := lt_of_lt_of_le (by norm_num) hmass
  refine ⟨fun i => cap i / S, fun i => div_nonneg (hcap i) hS.le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hS.ne'
  · intro i
    exact (div_le_iff₀ hS).mpr (by nlinarith [hcap i])

lemma probabilities_of_mixed_capacity {ι : Type*} [Fintype ι]
    (t : ι → ℝ) {L Q : ℝ} (ht : ∀ i, 0 ≤ t i) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hc : 1 ≤ ∑ i, min (L * t i) (Q * (t i)^2)) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L * t i) ∧ ∀ i, p i ≤ Q * (t i)^2 := by
  obtain ⟨p,hp,hsum,hbound⟩ := probabilities_of_capacity
    (fun i => min (L*t i) (Q*(t i)^2))
    (fun i => le_min (mul_nonneg hL (ht i)) (mul_nonneg hQ (sq_nonneg _))) hc
  exact ⟨p,hp,hsum,fun i => (hbound i).trans (min_le_left _ _),
    fun i => (hbound i).trans (min_le_right _ _)⟩

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

lemma weight_le_one (n : ℕ) (v : Fin (T.size n)) : T.weight n v ≤ 1 := by
  rw [← T.total_mass n]
  exact Finset.single_le_sum (fun w _ => T.nonneg n w) (Finset.mem_univ v)

lemma linear_transition_product
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ α : ℝ}
    (hΔ₀ : 0 ≤ Δ₀) (hα : 0 ≤ α) (hroot : ∀ v, Δ 0 v = Δ₀)
    (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hlin : ∀ n v, p n v * Δ n (T.parent n v) ≤ α * Δ (n+1) v) :
    ∀ n v, Δ₀ * T.weight n v ≤ α^n * Δ n v := by
  intro n
  induction n with
  | zero =>
    intro v
    simpa [hroot] using mul_le_mul_of_nonneg_left (T.weight_le_one 0 v) hΔ₀
  | succ n ih =>
    intro v
    calc
      Δ₀ * T.weight (n+1) v = p n v * (Δ₀ * T.weight n (T.parent n v)) := by
        rw [hstep]; ring
      _ ≤ p n v * (α^n * Δ n (T.parent n v)) :=
        mul_le_mul_of_nonneg_left (ih _) (hp n v)
      _ = α^n * (p n v * Δ n (T.parent n v)) := by ring
      _ ≤ α^n * (α * Δ (n+1) v) :=
        mul_le_mul_of_nonneg_left (hlin n v) (pow_nonneg hα n)
      _ = _ := by rw [pow_succ]; ring

lemma badCount_exp_succ (c : ℝ) (n : ℕ) (v : Fin (T.size (n+1))) :
    Real.exp (c * ((11/20:ℝ) * T.badCount (n+1) v - (1/20:ℝ) * (n+1))) =
      Real.exp (c * ((11/20:ℝ) * T.badCount n (T.parent n v) - (1/20:ℝ)*n)) *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) := by
  rw [← Real.exp_add]
  congr 1
  simp only [badCount, Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  split_ifs <;> ring

lemma quadratic_transition_product
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ c : ℝ}
    (hroot : ∀ v, Δ 0 v = Δ₀) (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hq : ∀ n v, p n v *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) *
      (Δ n (T.parent n v))^2 ≤ (Δ (n+1) v)^2) :
    ∀ n v, Δ₀^2 * T.weight n v *
      Real.exp (c * ((11/20:ℝ) * T.badCount n v - (1/20:ℝ) * n)) ≤ (Δ n v)^2 := by
  intro n
  induction n with
  | zero =>
    intro v
    simpa [badCount,hroot] using
      mul_le_mul_of_nonneg_left (T.weight_le_one 0 v) (sq_nonneg Δ₀)
  | succ n ih =>
    intro v
    rw [hstep, Nat.cast_add, Nat.cast_one, T.badCount_exp_succ]
    calc
      _ = (p n v * Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2))) *
        (Δ₀^2 * T.weight n (T.parent n v) *
          Real.exp (c * ((11/20:ℝ) * T.badCount n (T.parent n v) - (1/20:ℝ) * n))) := by ring
      _ ≤ (p n v * Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2))) *
          (Δ n (T.parent n v))^2 :=
        mul_le_mul_of_nonneg_left (ih _) (mul_nonneg (hp n v) (Real.exp_pos _).le)
      _ ≤ _ := hq n v

theorem good_levels_of_transitions
    (p : (n : ℕ) → Fin (T.size (n+1)) → ℝ)
    (Δ : (n : ℕ) → Fin (T.size n) → ℝ) {Δ₀ c E : ℝ}
    (hΔ₀ : 0 < Δ₀) (hc : 0 < c)
    (hroot : ∀ v, Δ 0 v = Δ₀) (hp : ∀ n v, 0 ≤ p n v)
    (hstep : ∀ n v, T.weight (n+1) v = p n v * T.weight n (T.parent n v))
    (hq : ∀ n v, p n v *
      Real.exp (c * (if T.good n (T.parent n v) then -(1/20:ℝ) else 1/2)) *
      (Δ n (T.parent n v))^2 ≤ (Δ (n+1) v)^2)
    (henergy : ∀ n, ∑ v, (Δ n v)^2 ≤ E) :
    ∀ N : ℕ, ∃ n ≥ N, (1/2:ℝ) ≤ T.goodMass n := by
  apply T.arbitrarily_late_good_levels hc (E := E / Δ₀^2)
  intro n
  apply (le_div_iff₀ (sq_pos_of_pos hΔ₀)).mpr
  have h := (Finset.sum_le_sum fun v _ =>
    T.quadratic_transition_product p Δ hroot hp hstep hq n v).trans (henergy n)
  convert h using 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end FiniteFlow

end CannonFlow

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
end
end

end OAI
