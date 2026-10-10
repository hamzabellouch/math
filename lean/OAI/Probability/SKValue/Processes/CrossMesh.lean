import Mathlib
import OAI.Probability.SKValue.GroundState.CrossExpectation

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma abs_telescope_source {N : ℕ} {A b Γ Δ : ℕ → ℝ} {c d e : ℝ}
    (h : ∀ j<N,|A (j+1)-A j+b j|≤c+d*(Γ (j+1)-Γ j)+e*(Δ (j+1)-Δ j)) :
    |A N-A 0+∑ j∈Finset.range N,b j|≤
      (N : ℝ)*c+d*(Γ N-Γ 0)+e*(Δ N-Δ 0) := by
  have hs := (Finset.abs_sum_le_sum_abs (fun j ↦ A (j+1)-A j+b j) (Finset.range N)).trans
    (Finset.sum_le_sum (fun j hj ↦ h j (Finset.mem_range.mp hj)))
  simpa only [Finset.sum_add_distrib,Finset.sum_range_sub,←Finset.mul_sum,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hs

noncomputable def crossMeshSource (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V U : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j∈Finset.range N,(stepSize T N/2)*(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2
      ∂gaussianProduct (Fin (N+1)))

lemma cross_value_mesh_expectation {T K L K' L' G : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (hT : 0<T) (hT1 : T≤1) (hG : γ T≤G) (hG' : β T≤G) {N : ℕ} (hN : 0<N) :
    |(∫ z,U T (euler T N β (crossFeedback V U) z N)-
      V T (euler T N β (crossFeedback V U) z N) ∂gaussianProduct (Fin (N+1)))-
      (U 0 0-V 0 0)+crossMeshSource T N γ β V U|≤
    T*Real.sqrt (stepSize T N)*(cubicEnvelopeMean G K ((1/2+G)*L)+
      cubicEnvelopeMean G K' ((1/2+G)*L'))+
      stepSize T N*K*(γ T-γ 0)+stepSize T N*K'*(β T-β 0) := by
  let δ := stepSize T N
  let Y := euler T N β (crossFeedback V U)
  let A := fun j ↦ ∫ z,U (meshTime T N j) (Y z j)-V (meshTime T N j) (Y z j)
    ∂gaussianProduct (Fin (N+1))
  let b := fun j ↦ (δ/2)*(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(deriv (V (meshTime T N j)) (Y z j))^2 ∂gaussianProduct (Fin (N+1)))
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := div_nonneg hT.le hNr.le
  have hδ1 : δ≤1 := by
    apply (div_le_iff₀ hNr).mpr
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    simpa only [one_mul] using hT1.trans hN1
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
  have hs (j : ℕ) : meshTime T N j+δ=meshTime T N (j+1) := by
    dsimp [meshTime]; push_cast; ring
  have hlast : meshTime T N N=T := by dsimp [meshTime,stepSize]; field_simp
  have hzero : meshTime T N 0=0 := by simp [meshTime]
  have hfm (j : ℕ) (hj : j<N) : Measurable (crossFeedback V U (meshTime T N j)) :=
    (((hU.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable.add
      ((hV.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable).div_const 2
  have hfb (j : ℕ) (hj : j<N) (x : ℝ) : |crossFeedback V U (meshTime T N j) x|≤1 :=
    crossFeedback_bound (hV.bounded _ (htime j hj.le) x) (hU.bounded _ (htime j hj.le) x)
  have hstep (j : ℕ) (hj : j<N) : |A (j+1)-A j+b j|≤
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (meshTime T N (j+1))-γ (meshTime T N j))+
      δ*K'*(β (meshTime T N (j+1))-β (meshTime T N j)) := by
    have hYp : DependsBefore j (fun z ↦ Y z j) :=
      eulerCoefficient_dependsBefore T hj.le β (crossFeedback V U) (fun _ y ↦ y)
    have he := cross_value_expectation_step hV hU (htime j hj.le).1 hδ hδ1
      (by rw [hs]; exact (htime (j+1) (by omega)).2) hG hG' (by omega : j<N+1)
      (measurable_euler T N β (crossFeedback V U) hfm j hj.le) hYp
      (euler_memLp T N β (crossFeedback V U) hfm hfb j hj.le)
    dsimp only at he
    rw [hs] at he
    simpa only [A,b,Y,euler,δ,mul_assoc] using he
  have hh := abs_telescope_source (A := A) (b := b)
    (Γ := fun j ↦ γ (meshTime T N j)) (Δ := fun j ↦ β (meshTime T N j)) hstep
  have hA0 : A 0=U 0 0-V 0 0 := by simp [A,Y,meshTime,euler]
  rw [hA0,show A N=(∫ z,U T (Y z N)-V T (Y z N) ∂gaussianProduct (Fin (N+1))) by
    dsimp only [A]; rw [hlast],hlast,hzero] at hh
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  convert hh using 1
  · rfl
  · dsimp only [δ] at hNd ⊢
    simp only [←mul_assoc,hNd]

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma euler_same_noise_bound {T G L d e : ℝ} {N : ℕ} {γ β : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hT : 0≤T) (hN : 0<N)
    (hG : 0≤G) (hL : 0≤L) (hd : 0≤d) (he : 0≤e)
    (hg : ∀ j<N,|γ (meshTime T N j)|≤G)
    (hc : ∀ j<N,|β (meshTime T N j)-γ (meshTime T N j)|≤d)
    (hv : ∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs : ∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤e)
    (hu : ∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z : Fin (N+1) → ℝ) {j : ℕ} (hj : j≤N) :
    |euler T N β v z j-euler T N γ u z j|≤T*(d+G*e)*Real.exp (T*G*L) := by
  let δ := stepSize T N
  have hδ : 0≤δ := div_nonneg hT (Nat.cast_nonneg _)
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have hrec (k : ℕ) (hk : k<N) :
      |euler T N β v z (k+1)-euler T N γ u z (k+1)|≤
        (1+δ*G*L)*|euler T N β v z k-euler T N γ u z k|+δ*(d+G*e) := by
    let y := euler T N β v z k
    let x := euler T N γ u z k
    let t := meshTime T N k
    have hb : |β t*v t y-γ t*u t x|≤d+G*e+G*L*|y-x| := by
      calc
        |β t*v t y-γ t*u t x| = |(β t-γ t)*v t y+γ t*(v t y-u t y)+γ t*(u t y-u t x)| := by congr 1; ring
        _ ≤ |(β t-γ t)*v t y|+|γ t*(v t y-u t y)|+|γ t*(u t y-u t x)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ d*1+G*e+G*(L*|y-x|) := by
          simp only [abs_mul]
          gcongr
          · exact hc k hk
          · exact hv k hk y
          · exact hg k hk
          · exact hs k hk y
          · exact hg k hk
          · exact hu k hk y x
        _ = _ := by ring
    change |y+Real.sqrt δ*coordinate N k z+δ*β t*v t y-
      (x+Real.sqrt δ*coordinate N k z+δ*γ t*u t x)|≤_
    calc
      _ = |(y-x)+δ*(β t*v t y-γ t*u t x)| := by congr 1; ring
      _ ≤ |y-x|+δ*|β t*v t y-γ t*u t x| := by simpa only [abs_mul,abs_of_nonneg hδ] using abs_add_le (y-x) (δ*(β t*v t y-γ t*u t x))
      _ ≤ |y-x|+δ*(d+G*e+G*L*|y-x|) := add_le_add_right (mul_le_mul_of_nonneg_left hb hδ) _
      _ = _ := by ring
  have h := finite_discrete_gronwall (e := fun k ↦ |euler T N β v z k-euler T N γ u z k|) (mul_nonneg (mul_nonneg hδ hG) hL)
    (show |euler T N β v z 0-euler T N γ u z 0|=0 by simp [euler])
    (fun k hk ↦ mul_nonneg hδ (add_nonneg hd (mul_nonneg hG he))) hrec j hj
  have hsum : (∑ k∈Finset.range j,δ*(d+G*e))≤T*(d+G*e) := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←hNd]
    have hjs : (j : ℝ)≤N := by exact_mod_cast hj
    nlinarith [mul_nonneg hG he,mul_nonneg hd hδ,mul_nonneg hδ (mul_nonneg hG he)]
  apply h.trans
  apply mul_le_mul hsum
  · apply Real.exp_le_exp.mpr
    calc
      (j : ℝ)*(δ*G*L)≤(N : ℝ)*(δ*G*L) := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (mul_nonneg (mul_nonneg hδ hG) hL)
      _=T*G*L := by rw [←hNd]; ring
  · positivity
  · positivity

end SKValue

end

end OAI
