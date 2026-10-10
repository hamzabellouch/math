import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ActionOrbitTransport
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Growth.HomogeneousAverage
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteActionAverage
import OAI.Probability.CriticalPercolation.Harmonic.CayleyPoincare

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma getVert_mem_ball {b : X} (p : W.graph.Walk W.root b) (N i : ℕ) (hp : p.length≤N) :
    p.getVert i∈W.ball N := by
  apply W.mem_around.mpr
  exact ⟨p.take i,(p.take_length i).le.trans (min_le_right _ _) |>.trans hp⟩

lemma walk_square_bound {a b : X} (p : W.graph.Walk a b) (f : X → ℝ) :
    (f b-f a)^2≤(p.length:ℝ)*∑ i∈Finset.range p.length, (f (p.getVert (i+1))-f (p.getVert i))^2 := by
  have hh := sq_sum_le_card_mul_sum_sq (s:=Finset.range p.length)
    (f:=fun i => f (p.getVert (i+1))-f (p.getVert i))
  rw [Finset.sum_range_sub (fun i => f (p.getVert i)),Finset.card_range,p.getVert_zero,p.getVert_length] at hh
  exact hh

lemma averaged_path_bound
    (hu : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    {H : Type*} [Group H] [Fintype H] (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (p : W.graph.Walk W.root b) (hp : p.length≤N) (R : ℕ) (u : X → ℝ) :
    (∑ x∈W.ball R, ∑ h : H, (u (W.frame x (r h • b))-u x)^2)≤
      (N:ℝ)^2*(Fintype.card H : ℝ)*W.energy (W.ball (R+N)) u := by
  let e : X → ℝ := fun y => ∑ z∈W.neighbors y, (u z-u y)^2
  have he (y : X) : 0≤e y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg (i : ℕ) (hi : i∈Finset.range p.length) :
      (∑ x∈W.ball R, ∑ h : H,
        (u (W.frame x (r h • p.getVert (i+1)))-u (W.frame x (r h • p.getVert i)))^2)≤
        (Fintype.card H : ℝ)*W.energy (W.ball (R+N)) u := by
    have hav := W.average_sum_bound hu N r hm hs (p.getVert i) (W.getVert_mem_ball p N i hp) R e he
    apply le_trans _ hav
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro h hh
    have hadj := (W.frame x).map_adj_iff.mpr ((r h).val.map_adj_iff.mpr (p.adj_getVert_succ (Finset.mem_range.mp hi)))
    exact Finset.single_le_sum (f:=fun z => (u z-u (W.frame x (r h • p.getVert i)))^2)
      (fun _ _ => sq_nonneg _) (W.mem_neighbors.mpr hadj)
  have hb (x : X) (h : H) := W.walk_square_bound p (fun z => u (W.frame x (r h • z)))
  have hb' (x : X) (h : H) :
      (u (W.frame x (r h • b))-u x)^2≤(p.length:ℝ)*
        ∑ i∈Finset.range p.length,
          (u (W.frame x (r h • p.getVert (i+1)))-u (W.frame x (r h • p.getVert i)))^2 := by
    have hk : r h • W.root=W.root := (r h).property
    simpa only [hk,W.frame_root] using hb x h
  have hsum := Finset.sum_le_sum (fun x (_ : x∈W.ball R) =>
    Finset.sum_le_sum (fun h (_ : h∈Finset.univ) => hb' x h))
  simp only [←Finset.mul_sum] at hsum
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.range p.length)] at hsum
  rw [Finset.sum_comm (s:=W.ball R) (t:=Finset.range p.length)] at hsum
  have hgrad := Finset.sum_le_sum hg
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hgrad
  have hn : (p.length:ℝ)≤N := by exact_mod_cast hp
  have hnn : (0:ℝ)≤p.length := Nat.cast_nonneg _
  have hNn : (0:ℝ)≤N := Nat.cast_nonneg _
  have hc : (0:ℝ)≤Fintype.card H := Nat.cast_nonneg _
  have hE := W.energy_nonneg (W.ball (R+N)) u
  have hh := mul_le_mul_of_nonneg_left hgrad hnn
  have hsquare := (sq_le_sq₀ hnn hNn).mpr hn
  have hh' := mul_le_mul_of_nonneg_right hsquare (mul_nonneg hc hE)
  nlinarith

lemma pair_sum_le_aut (u : X → ℝ) (r : ℕ) (x : X) (hx : x∈W.ball r)
    (a : W.Aut) (ha : a W.root=x) :
    (∑ y∈W.ball r, (u y-u x)^2)≤∑ b∈W.ball (2*r), (u (a b)-u x)^2 := by
  have hsub : W.ball r⊆W.around x (2*r) := by
    intro y hy
    simpa only [show r+r=2*r by omega] using W.mem_around_add (W.mem_around_symm hx) hy
  calc
    _ ≤ ∑ y∈W.around x (2*r), (u y-u x)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by
      rw [←ha,←W.aut_around_image,Finset.sum_image]
      intro b _ c _ he; exact a.injective he

theorem ball_poincare
    (hun : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    (u : X → ℝ) (r : ℕ) (hu : (∑ x∈W.ball r, u x)=0) :
    (W.ball r).card*(∑ x∈W.ball r, (u x)^2)≤
      2*(r:ℝ)^2*((W.ball (2*r)).card:ℝ)*W.energy (W.ball (3*r)) u := by
  obtain ⟨H,hH,hHF,t,htm,hts⟩ := exists_finite_restriction (G:=W.Stab)
    (W.ball (2*r):Set X) (W.ball (2*r)).finite_toSet (W.stab_ball_preserved (2*r))
  let := hH
  let := hHF
  have hav (b : X) (hb : b∈W.ball (2*r)) :
      (∑ x∈W.ball r, ∑ h : H, (u (W.frame x (t h • b))-u x)^2)≤
        (2*(r:ℝ))^2*(Fintype.card H:ℝ)*W.energy (W.ball (3*r)) u := by
    obtain ⟨p,hp⟩ := W.mem_around.mp hb
    simpa only [show r+2*r=3*r by omega,Nat.cast_mul,Nat.cast_ofNat] using
      W.averaged_path_bound hun (2*r) t htm hts b p hp r u
  have hlower (x : X) (hx : x∈W.ball r) (h : H) :
      (∑ y∈W.ball r, (u y-u x)^2)≤∑ b∈W.ball (2*r), (u (W.frame x (t h • b))-u x)^2 := by
    apply W.pair_sum_le_aut u r x hx (W.frame x*(t h).val)
    change W.frame x ((t h).val W.root)=x
    rw [show (t h).val W.root=W.root from (t h).property,W.frame_root]
  have hl := Finset.sum_le_sum (fun x (hx : x∈W.ball r) =>
    Finset.sum_le_sum (fun h (_ : h∈Finset.univ) => hlower x hx h))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum] at hl
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=W.ball (2*r))] at hl
  rw [Finset.sum_comm (s:=W.ball r) (t:=W.ball (2*r))] at hl
  have hs := Finset.sum_le_sum hav
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hid := HarmonicAnalysis.finite_variance_identity (W.ball r) u
  have hswap : (∑ x∈W.ball r, ∑ y∈W.ball r, (u y-u x)^2)=
      2*((W.ball r).card:ℝ)*(∑ x∈W.ball r, (u x)^2) := by
    rw [Finset.sum_comm,hid,hu]; ring
  rw [hswap] at hl
  have hpos : (0:ℝ)<Fintype.card H := by exact_mod_cast Fintype.card_pos
  nlinarith [hl.trans hs]

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
