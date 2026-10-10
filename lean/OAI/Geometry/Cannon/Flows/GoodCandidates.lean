import Mathlib
import OAI.Geometry.Cannon.Modulus.BinNearCard
import OAI.Geometry.Cannon.Flows.Lower
import OAI.Geometry.Cannon.Modulus.PositiveCapacityTransitions

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
namespace CannonFlow

open CannonCapacity Filter Topology Finset

theorem eventually_bad_transition_thresholds (qdim : ℕ) (ell H : ℝ)
    (hell : 0 < ell) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℝ,
      Real.exp ((160*(qdim+1):ℝ)*ell*n)/(2*(H+3)) ≤ N →
      8 ≤ Real.exp (-ell*n)*N ∧
      64 ≤ Real.exp (-((80*(qdim+1):ℝ)*ell*n))*N := by
  have hq : (0:ℝ) ≤ qdim := Nat.cast_nonneg _
  have h₁ := eventually_exp_domination ell ((160*(qdim+1):ℝ)*ell) (16*(H+3))
    (by nlinarith only [hell,hq])
  have h₂ := eventually_exp_domination ((80*(qdim+1):ℝ)*ell)
    ((160*(qdim+1):ℝ)*ell) (128*(H+3)) (by nlinarith only [hell,hq])
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro N hN
  have hden : 0 < 2*(H+3) := by linarith only [hH]
  have hb := (div_le_iff₀ hden).mp hN
  have hprod (a : ℝ) : Real.exp (-(a*n))*Real.exp (a*n)=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  constructor
  · have hN' : 8*Real.exp (ell*n) ≤ N := by nlinarith only [hb,hn₁,hden]
    have hh := mul_le_mul_of_nonneg_left hN' (Real.exp_pos (-(ell*n))).le
    rw [show Real.exp (-(ell*n))*(8*Real.exp (ell*n)) =
      8*(Real.exp (-(ell*n))*Real.exp (ell*n)) by ring,hprod, mul_one] at hh
    simpa only [neg_mul] using hh
  · have hN' : 64*Real.exp ((80*(qdim+1):ℝ)*ell*n) ≤ N := by
      nlinarith only [hb,hn₂,hden]
    have hh := mul_le_mul_of_nonneg_left hN'
      (Real.exp_pos (-(((80*(qdim+1):ℝ)*ell)*n))).le
    rw [show Real.exp (-(((80*(qdim+1):ℝ)*ell)*n)) *
        (64*Real.exp (((80*(qdim+1):ℝ)*ell)*n)) =
      64*(Real.exp (-(((80*(qdim+1):ℝ)*ell)*n))*Real.exp (((80*(qdim+1):ℝ)*ell)*n)) by ring,
      hprod,mul_one] at hh
    exact hh

end CannonFlow

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

def GoodCandidates {ι : Type*} (li ui lo uo : ι → ℝ) (a b κ : ℝ) : Prop :=
  ∃ i j,
    κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
    κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
    uo i+(b-a)/4 ≤ lo j

lemma fraction_clip {a b l u : ℝ} (hab : a < b) (hlu : l ≤ u) :
    clip a b u-clip a b l = (b-a)*fraction a b l u := by
  rw [clip_difference hab.le hlu]
  unfold fraction childUpper childLower
  exact (mul_div_cancel₀ _ (sub_pos.mpr hab).ne').symm

theorem candidate_subdivision {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (li ui lo uo : ι → ℝ)
    (a b κ A B R r H L Qg Qb : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι:ℝ)*κ ≤ 1/8)
    (hR : 0 < R) (hr : 0 < r) (hH : 0 < H) (hAB : A+2 ≤ B)
    (hscale : 2*((H+3)*r) ≤ R)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hcover : ∀ rad, A*R ≤ rad → rad ≤ B*R → ∀ s ∈ Ioo a b,
      ∃ i, |dist (q i) x-rad| ≤ r ∧ s ∈ Icc (li i) (ui i))
    (hL : 0 < L) (hQg : 0 < Qg) (hQb : 0 < Qb)
    (hcardL : 8 ≤ L*(R/(2*(H+3)*r)))
    (hcardQ : 64 ≤ Qb*(R/(2*(H+3)*r)))
    (hcap : ∃ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*fraction a b (lo i) (uo i))
        (Qg*(fraction a b (lo i) (uo i))^2)) :
    ∃ S : Finset ι, (∀ i ∈ S, 0 < fraction a b (lo i) (uo i)) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, p i ≤ L*fraction a b (lo i) (uo i)) ∧
      ∀ i, p i ≤ (if GoodCandidates li ui lo uo a b κ then Qg else Qb)*
        (fraction a b (lo i) (uo i))^2 := by
  classical
  let t := fun i => fraction a b (lo i) (uo i)
  by_cases hg : GoodCandidates li ui lo uo a b κ
  · obtain ⟨S,hsep,hS⟩ := hcap
    obtain ⟨T,hTS,hT,p,hp,hsum,hl,hq⟩ := positive_capacity_transitions S t hL hQg
      (fun _ _ => fraction_nonneg hab) hS
    exact ⟨T,hT,fun i hi j hj hij => hsep i (hTS hi) j (hTS hj) hij,
      p,hp,hsum,hl,fun i => by simpa only [ite_eq_left hg] using hq i⟩
  · obtain ⟨S,hcard,ht,hsep⟩ := bad_node_many_children q x li ui lo uo t a b κ A B R r H
      hab hκ hcount hR hr hH hAB hscale hinner hlo huo
      (fun i => fraction_clip hab ((hlo i).trans ((hinner i).trans (huo i)))) hcover hg
    obtain ⟨p,hp,hsum,hl,hq⟩ := uniform_bad_transitions S t hL hQb ht
      (hcardL.trans (mul_le_mul_of_nonneg_left hcard hL.le))
      (hcardQ.trans (mul_le_mul_of_nonneg_left hcard hQb.le))
    exact ⟨S,fun i hi => lt_of_lt_of_le (by norm_num) (ht i hi),hsep,
      p,hp,hsum,hl,fun i => by simpa only [ite_eq_right hg] using hq i⟩

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

theorem uniform_literal_subdivision {X : Type*} [MetricSpace X] [ProperSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B₀ H c₀ C c d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B₀) (hH : 0 < H) (hc₀ : 2 ≤ c₀)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι ζ δ : Type*} [Fintype ι] [Fintype ζ] [Fintype δ]
      (q : ι → X) (aux : ζ → X) (ξ : δ → X) (h : ζ → X ≃ₜ X)
      (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X) (a b κ R r s : ℝ),
      a < b → 0 < κ → (Fintype.card ι:ℝ)*κ ≤ 1/8 →
      0 < R → 0 < r → 0 < s → r ≤ s → s ≤ R/4 →
      c₀*r ≤ R → 2*((H+3)*r) ≤ R →
      (B₀+1)*R ≤ 1 → max H 1*r ≤ 1 → 3*s ≤ 1 →
      max (C+2) (max c 1)*(r/s) ≤ 1 →
      R/s = Real.exp (2*ell*n) → R/r = Real.exp ((160*(qdim+1):ℝ)*ell*n) →
      (∀ i, dist (q i) x ≤ (B₀+1)*R) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → s ≤ dist (aux i) (aux j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ z, dist x (aux z) ≤ (B₀+1)*R) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ i, dist (q i) v ≤ r) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ z, dist v (aux z) ≤ s) →
      (∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω) → ContinuousOn f Ω →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B₀*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      (∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
        dist (h z v) (h z v') ≤ C/s*dist v v' ∧ c/s*dist v v' ≤ dist (h z v) (h z v')) →
      ∀ ω : δ → ℝ, MacroscopicAdmissible ξ (r/s) d₀ ω →
      (∑ i, (ω i)^2) ≤ M ((160*(qdim+1)-2)*n) →
      let lo := fun i => lower f (q i) (c₀*r)
      let uo := fun i => upper f (q i) (c₀*r)
      let li := fun i => lower f (q i) (2*r)
      let ui := fun i => upper f (q i) (2*r)
      ∃ S : Finset ι, (∀ i ∈ S, 0 < fraction a b (lo i) (uo i)) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
        ∃ p : S → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
        (∀ i, p i ≤ Real.exp (-ell*n)*fraction a b (lo i) (uo i)) ∧
        ∀ i, p i ≤ (if GoodCandidates li ui lo uo a b κ
          then Real.exp (8*(qdim+1)*ell*n) else Real.exp (-((80*(qdim+1):ℝ)*ell*n)))*
          (fraction a b (lo i) (uo i))^2 := by
  have hcap := uniform_separated_capacity qdim CP A B₀ H C c d₀ ell
    hpack hCP hA hAB hH hC hc hdc hell M hMnon hM
  have hbad := eventually_bad_transition_thresholds qdim ell H hell hH
  filter_upwards [hcap,hbad] with n hn hnb
  intro ι ζ δ _ _ _ q aux ξ h x Ω f K a b κ R r s hab hκ hcount hR hr hs hrs hsR
    hsmall hsparse hrad hdegscale hauxscale htransscale hratio hratioR
    hqloc hq haux hξ hauxloc hnet hauxnet hΩ hf hK hinner hdiam hlevel hmap ω hω hωmass
  dsimp only
  let lo := fun i => lower f (q i) (c₀*r)
  let uo := fun i => upper f (q i) (c₀*r)
  let li := fun i => lower f (q i) (2*r)
  let ui := fun i => upper f (q i) (2*r)
  let t := fun i => fraction a b (lo i) (uo i)
  have hr₂ : 0 ≤ 2*r := by positivity
  have hro : 0 ≤ c₀*r := mul_nonneg (by linarith only [hc₀]) hr.le
  have hsub (i : ι) : closedBall (q i) (2*r) ⊆ closedBall (q i) (c₀*r) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hc₀ hr.le)
  have hloc (i : ι) : closedBall (q i) (c₀*r) ⊆ Ω := by
    intro v hv
    have hvd := mem_closedBall.mp hv
    have hd := dist_triangle v (q i) x
    exact hΩ v (by nlinarith only [hd,hvd,hqloc i,hsmall])
  have hfo (i : ι) := hf.mono (hloc i)
  have hfi (i : ι) := (hfo i).mono (hsub i)
  have hlohi (i : ι) : lo i ≤ uo i := lower_le_upper hro (hfo i)
  have hliui (i : ι) : li i ≤ ui i := lower_le_upper hr₂ (hfi i)
  have hcontain (i : ι) : lo i ≤ li i ∧ ui i ≤ uo i :=
    ball_range_mono hr₂ (mul_le_mul_of_nonneg_right hc₀ hr.le) (hfo i)
  have hlen (i : ι) : clip a b (uo i)-clip a b (lo i) = (b-a)*t i :=
    fraction_clip hab (hlohi i)
  have hout (i : ι) (v : X) (_hvΩ : v ∈ Ω) (hv : dist v (q i) ≤ 2*r) :
      f v ∈ Icc (lo i) (uo i) := ball_range (hfo i) (hsub i (mem_closedBall.mpr hv))
  have hin (i : ι) (v : X) (_hvΩ : v ∈ Ω) (hv : dist v (q i) ≤ 2*r) :
      f v ∈ Icc (li i) (ui i) := ball_range (hfi i) (mem_closedBall.mpr hv)
  have hcapnode := hn q aux ξ h x Ω f K lo uo t a b R r s hab hR hr hs hrs hsR
    hrad hdegscale hauxscale htransscale hratio hq haux hξ hauxloc hnet hauxnet hΩ
    hK hinner hdiam hlevel hlohi (fun _ => fraction_nonneg hab) hlen hout hmap ω hω hωmass
  have hcover (rad : ℝ) (hl : A*R ≤ rad) (hu : rad ≤ B₀*R) :=
    node_radial_cover q x Ω f K li ui a b A B₀ R r rad hR hr.le
      (by linarith only [hA]) ⟨hl,hu⟩ hnet
      (fun v hv => hΩ v (by nlinarith only [hv,hR])) hK hinner hdiam hlevel hin
  have hb := hnb (R/(2*(H+3)*r)) (by
    rw [← hratioR]
    exact le_of_eq (by field_simp))
  exact candidate_subdivision q x li ui lo uo a b κ A B₀ R r H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) (Real.exp (-((80*(qdim+1):ℝ)*ell*n)))
    hab hκ hcount hR hr hH (by linarith only [hAB]) hsparse hliui
    (fun i => (hcontain i).1) (fun i => (hcontain i).2) hcover
    (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _) hb.1 hb.2 hcapnode

end CannonNode

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
