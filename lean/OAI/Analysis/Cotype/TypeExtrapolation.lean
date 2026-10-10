import OAI.Analysis.Cotype.GeometricTypeLevels
import OAI.Analysis.Cotype.KConvexUniformL1

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem finite_geometric_sum_le (s : Finset ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑ k ∈ s, q^k) ≤ (1-q)⁻¹ := by
  classical
  have hgeom (K : ℕ) : (1-q)*(∑ k ∈ Finset.range K, q^k) = 1-q^K := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
  let K := s.sup id+1
  have hs : s ⊆ Finset.range K := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => pow_nonneg hq k)
  apply hb.trans
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith [hgeom K,pow_nonneg hq K]

theorem normalized_type_bound_of_quadratic_powers {n : ℕ} (hn : 0 < n)
    {A p r : ℝ} (hA : 0 ≤ A) (hp : 0 < p) (hr : 1 < r) (hrp : r^p = n)
    (hq : Real.sqrt (A*n)*r⁻¹ < 1)
    (h : ∀ k : ℕ, QuadraticTypeBound X (n^k) (A^k))
    (N : ℕ) (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(1-Real.sqrt (A*n)*r⁻¹)⁻¹ := by
  classical
  have hr0 : 0 < r := by linarith
  obtain ⟨l,hl⟩ := exists_geometric_levels hr x (norm_le_one_of_lp_ball hp x hx)
  let S : Finset ℕ := Finset.univ.image l
  let f : ℕ → Fin N → X := fun k i => if l i = k then x i else 0
  have hblock (k : ℕ) : cubeL2 X (rademacherSum X (f k)) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by
    let s : Finset (Fin N) := Finset.univ.filter (fun i => x i ≠ 0 ∧ l i = k)
    have hcard : s.card ≤ n^(k+1) := by
      apply geometric_level_card_le hn hp hr0 hrp x hx s
      intro i hi
      obtain ⟨hi0,hik⟩ := (Finset.mem_filter.mp hi).2
      simpa only [hik] using ((hl i).2 hi0).le
    apply geometric_block_bound hA hr0 (h (k+1)) s hcard (f k)
    · intro i hi
      dsimp [f]
      split_ifs with hik
      · by_contra hi0
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi0,hik⟩)
      · rfl
    · intro i hi
      have hik := (Finset.mem_filter.mp hi).2.2
      simpa only [f,hik,ite_true] using (hl i).1
  have he : rademacherSum X x = fun ε => ∑ k ∈ S, rademacherSum X (f k) ε := by
    funext ε
    simp only [rademacherSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.smul_sum]
    congr 1
    have hi : l i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    simp [f,hi]
  have hq0 : 0 ≤ Real.sqrt (A*n)*r⁻¹ := mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hr0.le)
  rw [he]
  calc
    _ ≤ ∑ k ∈ S, cubeL2 X (rademacherSum X (f k)) := cubeL2_sum_le S _
    _ ≤ ∑ k ∈ S, Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := Finset.sum_le_sum (fun k _ => hblock k)
    _ = Real.sqrt (A*n)*∑ k ∈ S, (Real.sqrt (A*n)*r⁻¹)^k := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_geometric_sum_le S hq0 hq) (Real.sqrt_nonneg _)

theorem nontrivialType_of_bConvex_nontrivial [Nontrivial X] (h : BConvex X) : NontrivialType X := by
  obtain ⟨n,hn,A,hA,hAn,h⟩ := fixed_quadratic_improvement_of_bConvex h
  have hA1 := QuadraticTypeBound.one_le hn h
  have hn1 : 1 < n := by exact_mod_cast (lt_of_le_of_lt hA1 hAn)
  obtain ⟨p,r,hp,hp2,hr,hrp,_,hq⟩ := exists_type_extrapolation_parameters hn1 hA hAn
  have hD : 0 ≤ Real.sqrt (A*n)*(1-Real.sqrt (A*n)*r⁻¹)⁻¹ := by positivity
  refine ⟨p,hasType_of_normalized_bound hp hp2 hD ?_⟩
  exact normalized_type_bound_of_quadratic_powers hn hA (by linarith) hr hrp hq
    (quadraticTypeBound_pow hA h)

theorem nontrivialType_of_bConvex (h : BConvex X) : NontrivialType X := by
  cases subsingleton_or_nontrivial X with
  | inl hzero =>
      let _ := hzero
      refine ⟨2,by norm_num,by norm_num,0,by norm_num,fun n x => ?_⟩
      have hx : ∀ i, x i = 0 := fun i => Subsingleton.elim _ _
      simp [hx,rademacherSum,cubeL2,average]
  | inr hnonzero =>
      let _ := hnonzero
      exact nontrivialType_of_bConvex_nontrivial h

theorem nontrivialType_of_kConvex (h : KConvex X) : NontrivialType X :=
  nontrivialType_of_bConvex (bConvex_of_not_uniformL1 (not_uniformL1_of_kConvex h))

theorem forwardTarget_proved [CompleteSpace X] [Nontrivial X] : ForwardTarget X := by
  intro h
  exact finiteCotype_pair_of_nontrivialType (nontrivialType_of_kConvex h)
    (nontrivialType_of_kConvex (kConvex_dual_iff.mpr h))

end Cotype

end

end OAI
