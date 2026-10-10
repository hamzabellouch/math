import Mathlib
import OAI.Probability.CriticalPercolation.Modular.RelativeModular
import OAI.Probability.CriticalPercolation.Modular.ActionOrbitTransport
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Growth.HomogeneousAverage
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

def HasDegree (d : ℕ) : Prop := ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (W.ball n).card≤C*n^d

lemma not_quadratic_exponential_lower
    (d : ℕ) (hg : W.HasDegree d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (W.ball (L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := SparseGrowth.eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (W.ball (L*n^2)).card := hlo n
      _ ≤ (W.ball r).card := Finset.card_le_card (W.ball_mono hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma suborbit_card_relIndex (x y : X) : suborbitCard W.Aut X x y=
    (MulAction.stabilizer W.Aut y).relIndex (MulAction.stabilizer W.Aut x) := by
  have he : (MulAction.stabilizer W.Aut y).subgroupOf (MulAction.stabilizer W.Aut x)=
      MulAction.stabilizer (MulAction.stabilizer W.Aut x) y := by ext g; rfl
  rw [Subgroup.relIndex,he,MulAction.index_stabilizer]
  rfl

def ratio (x y : X) : ℝ := (suborbitCard W.Aut X x y : ℝ)/(suborbitCard W.Aut X y x : ℝ)
lemma ratio_relativeMass (x y : X) : W.ratio x y=
    Subgroup.relativeMass (MulAction.stabilizer W.Aut x) (MulAction.stabilizer W.Aut y) := by
  simp only [ratio,W.suborbit_card_relIndex,Subgroup.relativeMass]
lemma ratio_pos (x y : X) : 0<W.ratio x y :=
  div_pos (Nat.cast_pos.mpr (W.suborbit_card_pos x y)) (Nat.cast_pos.mpr (W.suborbit_card_pos y x))
lemma ratio_cocycle (x y z : X) : W.ratio x y*W.ratio y z=W.ratio x z := by
  simp only [W.ratio_relativeMass]
  apply Subgroup.relativeMass_cocycle
  all_goals
    rw [←W.suborbit_card_relIndex]
    exact ne_of_gt (W.suborbit_card_pos _ _)
lemma ratio_self (x : X) : W.ratio x x=1 := by
  rw [W.ratio_relativeMass,Subgroup.relativeMass_self]
lemma ratio_aut (g : W.Aut) (x y : X) : W.ratio (g x) (g y)=W.ratio x y := by
  change W.ratio (g • x) (g • y)=_
  simp only [ratio,smul_suborbitCard]
lemma ratio_pow (g : W.Aut) (x : X) (n : ℕ) : W.ratio x ((g^n) x)=(W.ratio x (g x))^n := by
  induction n with
  | zero => change W.ratio x x=(W.ratio x (g x))^0; rw [W.ratio_self,pow_zero]
  | succ n ih =>
    have he : (g^(n+1)) x=(g^n) (g x) := by rw [pow_succ]; rfl
    rw [he,←W.ratio_cocycle x ((g^n) x),W.ratio_aut,ih,pow_succ]

lemma aut_pow_ball (g : W.Aut) (x : X) (L : ℕ) (hl : g x∈W.around x L) (n : ℕ) :
    (g^n) x∈W.around x (n*L) := by
  induction n with
  | zero => change x∈W.around x (0*L); simpa only [Nat.zero_mul] using W.self_mem_around x 0
  | succ n ih =>
    have hstep : (g^n) (g x)∈W.around ((g^n) x) L := by
      rw [←W.aut_around_image]
      exact Finset.mem_image.mpr ⟨g x,hl,rfl⟩
    have hh := W.mem_around_add ih hstep
    have he : (g^(n+1)) x=(g^n) (g x) := by rw [pow_succ]; rfl
    simpa only [Nat.add_mul,Nat.one_mul,←he] using hh

lemma ratio_power_card_bound (g : W.Aut) (x : X) (L : ℕ) (hl : g x∈W.around x L) (n : ℕ) :
    (W.ratio x (g x))^n≤((W.ball (n*L)).card:ℝ) := by
  rw [←W.ratio_pow]
  have hr : W.ratio x ((g^n) x)≤(suborbitCard W.Aut X x ((g^n) x):ℝ) := by
    apply div_le_self (Nat.cast_nonneg _)
    exact_mod_cast W.suborbit_card_pos ((g^n) x) x
  apply hr.trans
  have hsub : stabilizerOrbit W.Aut X x ((g^n) x)⊆(W.around x (n*L):Set X) := by
    intro y hy
    obtain ⟨k,hk,rfl⟩ := (mem_stabilizerOrbit W.Aut X).mp hy
    change k x=x at hk
    change k ((g^n) x)∈W.around x (n*L)
    simpa only [hk] using W.mem_around.mpr
      (GraphTopology.iso_reachBall W.graph k (W.mem_around.mp (W.aut_pow_ball g x L hl n)))
  have hc := Set.ncard_le_ncard hsub (W.around x (n*L)).finite_toSet
  rw [Set.ncard_coe_finset,W.card_around x (n*L)] at hc
  exact_mod_cast hc

lemma ratio_le_one (d : ℕ) (hg : W.HasDegree d) (x y : X) : W.ratio x y≤1 := by
  by_contra! hr
  obtain ⟨g,hgxy⟩ := W.transitive x y
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2:ℝ) hr
  let a := g^k
  have ha : 2≤W.ratio x (a x) := by
    dsimp [a]
    rw [W.ratio_pow,hgxy]
    exact hk.le
  obtain ⟨p,_,_⟩ := W.connected.exists_path_of_dist x (a x)
  let L := max p.length 1
  have him : a x∈W.around x L := W.mem_around.mpr ⟨p,le_max_left _ _⟩
  apply W.not_quadratic_exponential_lower d hg L (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
  intro n
  have hb := W.ratio_power_card_bound a x L him n
  have he : (2:ℝ)^n≤((W.ball (n*L)).card:ℝ) :=
    (pow_le_pow_left₀ (by norm_num) ha n).trans hb
  have hh : 2^n≤(W.ball (n*L)).card := by exact_mod_cast he
  apply hh.trans (Finset.card_le_card (W.ball_mono ?_))
  have hn : n≤n^2 := by nlinarith
  nlinarith

theorem balanced_suborbits (d : ℕ) (hg : W.HasDegree d) (x y : X) :
    suborbitCard W.Aut X x y=suborbitCard W.Aut X y x := by
  have h1 := W.ratio_le_one d hg x y
  have h2 := W.ratio_le_one d hg y x
  have hp : (0:ℝ)<suborbitCard W.Aut X y x := by exact_mod_cast W.suborbit_card_pos y x
  have hq : (0:ℝ)<suborbitCard W.Aut X x y := by exact_mod_cast W.suborbit_card_pos x y
  dsimp [ratio] at h1 h2
  have he : (suborbitCard W.Aut X x y:ℝ)=(suborbitCard W.Aut X y x:ℝ) := by
    apply le_antisymm
    · exact (div_le_one hp).mp h1
    · exact (div_le_one hq).mp h2
  exact_mod_cast he

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
