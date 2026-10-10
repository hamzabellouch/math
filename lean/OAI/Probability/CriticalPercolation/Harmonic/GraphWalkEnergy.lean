import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGrowth
import OAI.Probability.CriticalPercolation.Growth.SparseEnergyRatio
import OAI.Probability.CriticalPercolation.Harmonic.GraphWalkOperator
import OAI.Probability.CriticalPercolation.Harmonic.GraphWalkProbability

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma exists_ball_boundary [Infinite X] (r : ℕ) : ∃ x∈W.ball (r+1), x∉W.ball r := by
  by_contra! hbad
  have hb (n : ℕ) : W.ball n⊆W.ball r := by
    intro x hx
    obtain ⟨p,hp⟩ := W.mem_around.mp hx
    have hw : ∀ {a b : X}, (p : W.graph.Walk a b) → a∈W.ball r → b∈W.ball r := by
      intro a b p
      induction p with
      | nil => exact id
      | @cons a y b h p ih =>
        intro ha
        apply ih
        apply hbad
        exact W.mem_around_add ha (W.mem_around.mpr ⟨.cons h .nil,by simp⟩)
    exact hw p (W.self_mem_around _ _)
  have hf : (Set.univ:Set X).Finite := (W.ball r).finite_toSet.subset (by
    intro x _; obtain ⟨n,hn⟩ := W.exists_mem_ball x; exact hb n hn)
  exact Set.infinite_univ hf

lemma walkFeature_symmetric (n : ℕ) (x y : X) : W.walkFeature n x y=W.walkFeature n y x := by
  have h := W.walkPower_symmetric n (FH.delta x) (FH.delta y)
  rw [real_inner_comm,FH.delta_inner,FH.delta_inner] at h
  exact h

lemma walkEnergy_gradient (n : ℕ) :
    (∑ y∈W.neighbors W.root, ‖W.walkFeature n y-W.walkState n‖^2)=
      4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  simp only [norm_sub_sq_real,W.walkFeature_norm,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum,←sum_inner,W.walkFeature_average,
    real_inner_smul_left (F:=FH X)]
  unfold walkEnergy
  rw [inner_sub_right,W.lazyWalk_apply,real_inner_smul_right (F:=FH X),inner_add_right,
    real_inner_self_eq_norm_sq,W.averaging_symmetric]
  dsimp only [walkState,degree]
  ring

lemma feature_neighbor_bound (hD : 0<W.degree) (n : ℕ) {y : X} (hy : y∈W.neighbors W.root) :
    ‖W.walkFeature n y-W.walkState n‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  have hh := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) hy).trans_eq (W.walkEnergy_gradient n)
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg hD _)
  nlinarith [Real.sq_sqrt he,Real.sqrt_nonneg (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)),
    norm_nonneg (W.walkFeature n y-W.walkState n)]
lemma feature_edge_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (h : W.graph.Adj x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  have he : W.walkFeature n y-W.walkFeature n (g W.root)=
      FH.transport g.toEquiv (W.walkFeature n (g.symm y)-W.walkState n) := by
    rw [map_sub,W.transport_walkFeature,W.transport_walkFeature,g.apply_symm_apply]
  rw [he,LinearIsometryEquiv.norm_map]
  apply W.feature_neighbor_bound hD
  exact W.mem_neighbors.mpr (by simpa using g.symm.map_adj_iff.mpr h)
lemma feature_walk_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (p : W.graph.Walk x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤(p.length:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have he : W.walkFeature n z-W.walkFeature n x=
        (W.walkFeature n z-W.walkFeature n y)+(W.walkFeature n y-W.walkFeature n x) := by abel
    rw [he]
    have ht := norm_add_le (W.walkFeature n z-W.walkFeature n y) (W.walkFeature n y-W.walkFeature n x)
    have hb := W.feature_edge_bound hD n h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith
lemma feature_ball_bound (hD : 0<W.degree) (n r : ℕ) {x : X} (hx : x∈W.ball r) :
    ‖W.walkFeature n x-W.walkState n‖≤(r:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨p,hp⟩ := W.mem_around.mp hx
  exact (W.feature_walk_bound hD n p).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (Real.sqrt_nonneg _))

lemma supported_energy_bound [Infinite X] (n : ℕ) :
    W.walkState n W.root^2≤(n+1:ℝ)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  obtain ⟨x,hx,hx'⟩ := W.exists_ball_boundary n
  have hp := (W.walkFeature n x-W.walkState n).norm_coordinate_le W.root
  have hb := W.feature_ball_bound W.degree_pos n (n+1) hx
  have hv : |(W.walkFeature n x-W.walkState n) W.root|=|W.walkState n W.root| := by
    rw [FH.sub_apply,W.walkFeature_symmetric,W.walkState_support n hx',zero_sub,abs_neg]
  rw [hv] at hp
  have ht := pow_le_pow_left₀ (abs_nonneg _) (hp.trans hb) 2
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg W.degree_pos _)
  rw [mul_pow,Real.sq_sqrt he,sq_abs] at ht
  push_cast at ht
  nlinarith
lemma walkState_energy_pos [Infinite X] (n : ℕ) : 0<W.walkEnergy (W.walkState n) := by
  have hp := W.walkState_root_pos n
  have hb := W.supported_energy_bound n
  have hn := W.walkEnergy_nonneg W.degree_pos (W.walkState n)
  by_contra! h
  have he := le_antisymm h hn
  rw [he,mul_zero] at hb
  nlinarith
lemma walkState_energy_lower [Infinite X] (n : ℕ) :
    1≤((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState (2*n)) := by
  have hn := W.walkState_norm_lower W.degree_pos n
  have hb := W.supported_energy_bound (2*n)
  rw [W.walkState_double_at_root] at hb
  have hsq : 1≤((W.ball n).card:ℝ)^2*(‖W.walkState n‖^2)^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((W.ball n).card:ℝ))
  push_cast at hh
  nlinarith
lemma walkState_energy_antitone (hD : 0<W.degree) : Antitone (fun n => W.walkEnergy (W.walkState n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := W.walkEnergy_dissipation hD (W.walkState n)
  rw [←W.walkState_succ] at h
  nlinarith [sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖]

lemma walk_energy_inverse_sparse [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) :
    ∃ C : ℝ, 0≤C ∧ ∀ R, ∃ m≥R,
      (W.walkEnergy (W.walkState m))⁻¹≤C*(m:ℝ)^(2*d+2) := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨36*(W.degree:ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvol⟩ := hC (max R 1)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hnR : R≤n := (le_max_left R 1).trans hn
  refine ⟨2*n,by omega,?_⟩
  have hV : ((W.ball n).card:ℝ)≤(C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvol
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : ((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)≤
      (36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)^2*(3*(n:ℝ))^2*4*(W.degree:ℝ) := by
        gcongr
        linarith
      _ = (36*(W.degree:ℝ)*(C:ℝ)^2)*(n:ℝ)^(2*d+2) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have hb := W.walkState_energy_lower n
  have hh := mul_le_mul_of_nonneg_right hpoly (W.walkState_energy_pos (2*n)).le
  have hf : 1≤((36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2))*
      W.walkEnergy (W.walkState (2*n)) := hb.trans hh
  exact (inv_le_iff_one_le_mul₀ (W.walkState_energy_pos (2*n))).mpr hf

theorem exists_walk_small_relative_residual [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) (ε : ℝ) (hε : 0<ε) :
    ∃ n, 0<W.walkEnergy (W.walkState n) ∧
      ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2≤ε*W.walkEnergy (W.walkState n) := by
  obtain ⟨C,hC,hpoly⟩ := W.walk_energy_inverse_sparse d hg
  obtain ⟨n,hn⟩ := exists_small_relative_dissipation
    (fun n => W.walkEnergy (W.walkState n))
    (fun n => ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2)
    W.walkState_energy_pos (W.walkState_energy_antitone W.degree_pos)
    (fun n => by simpa only [W.walkState_succ] using W.walkEnergy_dissipation W.degree_pos (W.walkState n))
    (2*d+2) C hC hpoly ε hε
  exact ⟨n,W.walkState_energy_pos n,hn⟩

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
