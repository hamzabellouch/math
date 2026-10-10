import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.SmallExpectations
import OAI.Analysis.TracialCohomology.CenterExtensions

namespace OAI

/-! Center quantization for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)

include e hτ htr hfaith h1 in
lemma energy_contract_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (hr : 0 < r) (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : PopaMatrices.System m (1:M),
      energy τ F t ≤ (1-1/(1024*(r:ℝ)))*energy τ F s := by
  classical
  have hrR : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  by_cases hz : energy τ F s=0
  · exact ⟨n,hn,s,by rw [hz]; simp⟩
  have hE : 0 < energy τ F s := lt_of_le_of_ne (energy_nonneg τ F s) (Ne.symm hz)
  have hsum : (∑ _i : Fin r, energy τ F s/(r:ℝ)) = energy τ F s := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _i : Fin r => energy τ F s/(r:ℝ))
    (g := fun i : Fin r => ‖τ.toPreGNS (s.expect (F i))‖^2)
    ⟨⟨0,hr⟩,Finset.mem_univ _⟩ (by rw [hsum]; rfl)
  have hi : 0 < ‖τ.toPreGNS (s.expect (F i))‖ := by
    have hh := (div_pos hE hrR).trans_le hmax
    nlinarith [norm_nonneg (τ.toPreGNS (s.expect (F i)))]
  obtain ⟨m,hm,t,hle,hlt⟩ := extend_energy_decrease_center e τ hτ htr hfaith h1
    hdiff s hn (F i) (hF i) hi
  have hdiffs (j : Fin r) : 0 ≤ ‖τ.toPreGNS (s.expect (F j))‖^2-
      ‖τ.toPreGNS (t.expect (F j))‖^2 := by
    have hj := hle (F j)
    nlinarith [norm_nonneg (τ.toPreGNS (t.expect (F j)))]
  have hdrop := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin r =>
    ‖τ.toPreGNS (s.expect (F j))‖^2-‖τ.toPreGNS (t.expect (F j))‖^2)
    (fun j _ => hdiffs j) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hdrop
  change _ ≤ energy τ F s-energy τ F t at hdrop
  have hmax' : energy τ F s ≤ (r:ℝ)*‖τ.toPreGNS (s.expect (F i))‖^2 := by
    exact (div_le_iff₀ hrR).mp hmax |>.trans_eq (mul_comm _ _)
  refine ⟨m,hm,t,?_⟩
  apply (le_of_mul_le_mul_left ?_ (show 0 < 1024*(r:ℝ) by positivity))
  have hh : (1024*(r:ℝ))*((1-1/(1024*(r:ℝ)))*energy τ F s)=
      (1024*(r:ℝ)-1)*energy τ F s := by field_simp
  rw [hh]
  have hlow : ‖τ.toPreGNS (s.expect (F i))‖^2/1024 < energy τ F s-energy τ F t := by linarith
  have hmul := mul_lt_mul_of_pos_left hlow hrR
  nlinarith

include e hτ htr hfaith h1 in

theorem exists_small_expectation_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M), energy τ F s < ε := by
  by_cases hr : r=0
  · subst r
    exact ⟨1,by omega,trivialSystem,by simpa [energy] using hε⟩
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  let q : ℝ := 1-1/(1024*(r:ℝ))
  have hrR : 1 ≤ (r:ℝ) := by exact_mod_cast hrp
  have hq0 : 0 ≤ q := by
    have hh : 1/(1024*(r:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; exact sub_lt_self _ (by positivity)
  have hi : ∀ k : ℕ, ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M),
      energy τ F s ≤ q^k*energy τ F (trivialSystem (M:=M)) := by
    intro k
    induction k with
    | zero => exact ⟨1,by omega,trivialSystem,by simp⟩
    | succ k ih =>
      obtain ⟨n,hn,s,hs⟩ := ih
      obtain ⟨m,hm,t,ht⟩ := energy_contract_center e τ hτ htr hfaith h1 hdiff hrp F hF s hn
      refine ⟨m,hm,t,ht.trans ?_⟩
      have hh := mul_le_mul_of_nonneg_left hs hq0
      change q*energy τ F s ≤ _
      simpa only [pow_succ,mul_assoc,mul_comm q,mul_left_comm q] using hh
  have ht : Tendsto (fun k : ℕ => q^k*energy τ F (trivialSystem (M:=M))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (energy τ F (trivialSystem (M:=M)))
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨n,hn,s,hs⟩ := hi k
  exact ⟨n,hn,s,hs.trans_lt hk⟩
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem exists_large_refinement_center (hdiff : NoAbelianCorners M)
    {n : ℕ} (s : PopaMatrices.System n (1:M)) (hn : 0 < n) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ ∃ t : PopaMatrices.System m (1:M),
      ∀ x : M, ‖τ.toPreGNS (t.expect x)‖ ≤ ‖τ.toPreGNS (s.expect x)‖ := by
  obtain ⟨P,_hPn,hP⟩ := HochschildSakai.exists_abstract_star_preadjoint e
  let hL := (HochschildSakai.abstract_multiplication_normal e).1
  let hR := (HochschildSakai.abstract_multiplication_normal e).2
  let Q := closedCommutant e s P hP
  let eQ : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator
      (WeakAlgebra.linearClosure e s.commutant)) ≃ₗᵢ⋆[ℂ] Q := WeakAlgebra.predualEquiv e s.commutant hL hR P hP
  let τQ : Q →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ s.commutant hL hR P hP
  obtain ⟨r⟩ := exists_dyadic_system eQ τQ
    (WeakAlgebra.inheritedTrace_normal e τ s.commutant hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ s.commutant hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ s.commutant hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ s.commutant hL hR P hP h1)
    (closedCommutant_typeII e s P hP hn hdiff) (N+1)
  let rM := r.map Q.subtype
  have hc : ∀ i j a b, Commute (rM.entry i j) (s.entry a b) := by
    intro i j a b
    exact closedCommutant_subset e s P hP (r.entry i j).property a b
  let t := rM.tensor s hc
  have hpow : N < 2^(N+1) := lt_trans (Nat.lt_succ_self N) (Nat.lt_two_pow_self)
  have hpowpos : 0 < 2^(N+1) := pow_pos (by omega) _
  refine ⟨2^(N+1)*n,by nlinarith,t,?_⟩
  intro x
  rw [show t.expect x=rM.expect (s.expect x) from rM.tensor_expect s hc x]
  exact rM.expect_norm_le τ htr (by omega) _

include e hτ htr hfaith h1 in
lemma exists_large_small_expectation_center (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∃ s : PopaMatrices.System n (1:M), energy τ F s < ε := by
  obtain ⟨n,hn,s,hs⟩ := exists_small_expectation_center e τ hτ htr hfaith h1 hdiff F hF ε hε
  obtain ⟨m,hm,t,ht⟩ := exists_large_refinement_center e τ hτ htr hfaith h1 hdiff s hn N
  refine ⟨m,hm,t,(Finset.sum_le_sum (fun i _ => ?_)).trans_lt hs⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (ht (F i)) 2
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem local_quantization_center_valued (hdiff : NoAbelianCorners M)
    {r : ℕ} (F : Fin r → M) (hF : ∀ i, average e τ hτ htr hfaith (F i)=0)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re < δ ∧
      average e τ hτ htr hfaith q=(τ q).re • (1:M) ∧
      (∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η*(τ q).re := by
  let C : ℝ := ∑ j, ‖τ.toPreGNS (F j)‖^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*C/η) (1/δ))
  obtain ⟨n,hn,s,hs⟩ := exists_large_small_expectation_center e τ hτ htr hfaith h1
    hdiff F hF (η/2) (by positivity) N
  have hnpos : 0<n := Nat.zero_lt_of_lt hn
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hnpos
  have hb : 4*C/η < (n:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans (Nat.cast_lt.mpr hn)
  have hd : 1/δ < (n:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans (Nat.cast_lt.mpr hn)
  obtain ⟨a,ha⟩ := s.exists_flat_projection τ htr ⟨0,hnpos⟩ F
  let q := s.flatProjection ⟨0,hnpos⟩ a
  have hq : IsStarProjection q := s.flatProjection_projection _ _
  have ht : (τ q).re=(n:ℝ)⁻¹ := by
    rw [show τ q=(n:ℂ)⁻¹ from s.flatProjection_trace τ htr h1 _ _]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_inv,Complex.ofReal_re]
  have htpos : 0 < (τ q).re := by rw [ht]; positivity
  refine ⟨q,hq,fun h => by simp only [h,map_zero,Complex.zero_re,lt_self_iff_false] at htpos,?_,?_,?_⟩
  · rw [ht]
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ hnR).mpr (by
      have hh := (div_lt_iff₀ hδ).mp hd
      nlinarith)
  · rw [ht]
    change average e τ hτ htr hfaith (s.flatColumn ⟨0,hnpos⟩ a*star (s.flatColumn ⟨0,hnpos⟩ a))=_
    rw [average_trace e τ hτ htr hfaith h1,s.flatColumn_star_mul]
    have hd := average_diagonal_one e τ hτ htr hfaith h1 s ⟨0,hnpos⟩
    have hh := congrArg (fun z : M => (n:ℝ)⁻¹ • z) hd
    simpa only [smul_smul,inv_mul_cancel₀ hnR.ne',one_smul] using hh
  · have hterm : (2/(n:ℝ))*C < η/2 := by
      have hh := (div_lt_iff₀ hη).mp hb
      apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have hn0 := hnR.ne'
      field_simp
      nlinarith
    have hh : (n:ℝ)*(∑ i, ‖τ.toPreGNS (q*F i*q)‖^2) < η := by
      rw [Finset.mul_sum]
      exact ha.trans_lt (by change energy τ F s+2/(n:ℝ)*C<η; linarith)
    rw [ht,←div_eq_mul_inv]
    exact (lt_div_iff₀ hnR).mpr (by nlinarith)
end PopaCenter

end

end OAI
