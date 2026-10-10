import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Harmonic.FiniteHilbert
import OAI.Probability.CriticalPercolation.Harmonic.GraphWalkOperator

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma degree_pos [Infinite X] : 0<W.degree := by
  obtain ⟨x,hx⟩ := exists_ne W.root
  obtain ⟨p⟩ := W.connected W.root x
  cases p with
  | nil => exact (hx rfl).elim
  | @cons a y z h p => exact Finset.card_pos.mpr ⟨y,W.mem_neighbors.mpr h⟩

lemma averaging_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.averaging f)=FH.mass f := by
  have hc : (W.degree:ℝ)≠0 := by exact_mod_cast hD.ne'
  have hdelta (x : X) : FH.mass (W.averaging (FH.delta x))=1 := by
    rw [W.averaging_delta,map_smul,map_sum]
    simp only [FH.mass_delta,Finset.sum_const,nsmul_eq_mul,mul_one,smul_eq_mul,W.neighbors_card]
    exact inv_mul_cancel₀ hc
  rw [←f.delta_decomposition]
  simp only [map_sum,map_smul,hdelta,FH.mass_delta]
lemma lazyWalk_nonnegative (f : FH X) (hf : ∀ x, 0≤f x) : ∀ x, 0≤W.lazyWalk f x := by
  intro x
  rw [W.lazyWalk_coordinate]
  exact mul_nonneg (by norm_num) (add_nonneg (hf x)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => hf y))))
lemma lazyWalk_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.lazyWalk f)=FH.mass f := by
  rw [W.lazyWalk_apply,map_smul,map_add,W.averaging_mass hD]
  simp only [smul_eq_mul]; ring

def walkFeature (n : ℕ) (x : X) : FH X := (W.lazyWalk^n) (FH.delta x)
abbrev walkState (n : ℕ) := W.walkFeature n W.root
@[simp] lemma walkFeature_zero (x : X) : W.walkFeature 0 x=FH.delta x := rfl
lemma walkFeature_succ (n : ℕ) (x : X) : W.walkFeature (n+1) x=W.lazyWalk (W.walkFeature n x) := by
  simp only [walkFeature,pow_succ',Module.End.mul_apply]
lemma walkState_succ (n : ℕ) : W.walkState (n+1)=W.lazyWalk (W.walkState n) := W.walkFeature_succ n W.root
lemma walkState_nonnegative (n : ℕ) : ∀ x, 0≤W.walkState n x := by
  induction n with
  | zero => intro x; simp only [walkState,walkFeature_zero,FH.delta_apply]; split <;> norm_num
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_nonnegative _ ih
lemma walkState_mass (hD : 0<W.degree) (n : ℕ) : FH.mass (W.walkState n)=1 := by
  induction n with
  | zero => exact FH.mass_delta _
  | succ n ih => rw [W.walkState_succ,W.lazyWalk_mass hD,ih]
lemma walkState_root_pos (n : ℕ) : 0<W.walkState n W.root := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hs : 0≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors W.root, W.walkState n y := by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => W.walkState_nonnegative n y))
    positivity
lemma walkState_support (n : ℕ) {x : X} (hx : x∉W.ball n) : W.walkState n x=0 := by
  induction n generalizing x with
  | zero =>
    have hne : x≠W.root := by intro h; apply hx; rw [h]; exact W.self_mem_around _ _
    simp [hne]
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate,ih (fun h => hx (W.ball_mono (by omega) h))]
    have hs : (∑ y∈W.neighbors x, W.walkState n y)=0 := by
      apply Finset.sum_eq_zero
      intro y hy
      apply ih
      intro hn
      apply hx
      apply W.mem_around_add hn
      exact W.mem_around.mpr ⟨SimpleGraph.Walk.cons (W.mem_neighbors.mp hy).symm .nil,by simp⟩
    rw [hs]; ring
lemma walkPower_symmetric (n : ℕ) (f g : FH X) :
    inner ℝ ((W.lazyWalk^n) f) g=inner ℝ f ((W.lazyWalk^n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    calc
      _ = inner ℝ ((W.lazyWalk^n) (W.lazyWalk f)) g := by rw [pow_succ,Module.End.mul_apply]
      _ = inner ℝ (W.lazyWalk f) ((W.lazyWalk^n) g) := ih _ _
      _ = inner ℝ f (W.lazyWalk ((W.lazyWalk^n) g)) := W.lazyWalk_symmetric _ _
      _ = _ := by rw [pow_succ',Module.End.mul_apply]
lemma walkState_double_at_root (n : ℕ) : W.walkState (2*n) W.root=‖W.walkState n‖^2 := by
  have hh := W.walkPower_symmetric n (FH.delta W.root) (W.walkState n)
  rw [FH.delta_inner] at hh
  have he : (W.lazyWalk^n) (W.walkState n)=W.walkState (2*n) := by
    simp only [walkState,walkFeature,←Module.End.mul_apply,←pow_add,two_mul]
  rw [he] at hh
  change inner ℝ (W.walkState n) (W.walkState n)=_ at hh
  rw [real_inner_self_eq_norm_sq] at hh
  exact hh.symm
lemma walkState_norm_sq (n : ℕ) : ‖W.walkState n‖^2=∑ x∈W.ball n, (W.walkState n x)^2 :=
  (W.walkState n).norm_sq_eq_sum _ (by
    intro x hx; by_contra hn; exact ((W.walkState n).mem_support x).mp hx (W.walkState_support n hn))
lemma walkState_norm_lower (hD : 0<W.degree) (n : ℕ) : 1≤((W.ball n).card:ℝ)*‖W.walkState n‖^2 := by
  have hmass : (∑ x∈W.ball n, W.walkState n x)=1 := by
    rw [←W.walkState_mass hD n]
    exact (tsum_eq_sum (f:=fun x => W.walkState n x) (s:=W.ball n)
      (fun x hx => W.walkState_support n hx)).symm
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (W.ball n) (fun _ => (1:ℝ)) (fun x => W.walkState n x)
  simpa only [one_mul,hmass,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,←W.walkState_norm_sq] using hc

lemma transport_averaging (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.averaging f)=W.averaging (FH.transport g.toEquiv f) := by
  ext x
  simp only [FH.transport_apply,W.averaging_coordinate]
  congr 1
  change (∑ y∈W.neighbors (g.symm x), f y)=∑ y∈W.neighbors x, f (g.symm y)
  rw [←W.neighbors_image g.symm x,Finset.sum_image]
  exact fun a ha b hb h => g.symm.injective h
lemma transport_lazyWalk (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.lazyWalk f)=W.lazyWalk (FH.transport g.toEquiv f) := by
  simp only [W.lazyWalk_apply,map_smul,map_add,W.transport_averaging]
lemma transport_walkFeature (g : W.Aut) (n : ℕ) (x : X) :
    FH.transport g.toEquiv (W.walkFeature n x)=W.walkFeature n (g x) := by
  induction n with
  | zero => exact FH.transport_delta _ _
  | succ n ih => rw [W.walkFeature_succ,W.transport_lazyWalk,ih,W.walkFeature_succ]
lemma walkFeature_norm (n : ℕ) (x : X) : ‖W.walkFeature n x‖=‖W.walkState n‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,LinearIsometryEquiv.norm_map]
lemma walkFeature_average (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, W.walkFeature n y)=(W.degree:ℝ) • W.averaging (W.walkFeature n x) := by
  have hc : W.averaging.comp W.lazyWalk=W.lazyWalk.comp W.averaging := by
    ext f y
    simp only [LinearMap.comp_apply,W.lazyWalk_apply,map_smul,map_add]
  have hcomm : ∀ n, W.averaging.comp (W.lazyWalk^n)=(W.lazyWalk^n).comp W.averaging := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change W.averaging*(W.lazyWalk^(n+1))=(W.lazyWalk^(n+1))*W.averaging
      rw [pow_succ',←mul_assoc,show W.averaging*W.lazyWalk=W.lazyWalk*W.averaging from hc,
        mul_assoc,show W.averaging*W.lazyWalk^n=W.lazyWalk^n*W.averaging from ih,←mul_assoc,←pow_succ']
  have hd (x : X) : (W.degree:ℝ) • W.averaging (FH.delta x)=∑ y∈W.neighbors x, FH.delta y := by
    by_cases hD : W.degree=0
    · have he : W.neighbors x=∅ := Finset.card_eq_zero.mp (by exact (W.neighbors_card x).trans hD)
      simp [hD,he]
    · rw [W.averaging_delta,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hD),one_smul]
  calc
    _ = (W.lazyWalk^n) (∑ y∈W.neighbors x, FH.delta y) := (map_sum _ _ _).symm
    _ = (W.lazyWalk^n) ((W.degree:ℝ) • W.averaging (FH.delta x)) := by rw [hd]
    _ = _ := by rw [map_smul,←LinearMap.comp_apply,←hcomm,LinearMap.comp_apply]; rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
