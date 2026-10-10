import Mathlib
import OAI.Analysis.BoundedHochschild.CommutantQuantization
import OAI.Analysis.BoundedHochschild.FinitePhases

namespace OAI

/-! Rank-one projections, phase coefficients and small corners. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildFinitePhase
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

def scalarMatrix (a : Fin n → Fin n → ℂ) : M := ∑ i,∑ j,a i j • E.entry i j

lemma scalarMatrix_mul (a b : Fin n → Fin n → ℂ) :
    E.scalarMatrix a * E.scalarMatrix b = E.scalarMatrix (fun i l => ∑ j,a i j*b j l) := by
  classical
  simp only [scalarMatrix,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,E.entry_mul,
    smul_ite,smul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    _ = ∑ j,∑ i,∑ l,(a i j*b j l) • E.entry i l :=
      Finset.sum_congr rfl (fun j hj => Finset.sum_comm)
    _ = ∑ i,∑ j,∑ l,(a i j*b j l) • E.entry i l := Finset.sum_comm
    _ = ∑ i,∑ l,∑ j,(a i j*b j l) • E.entry i l :=
      Finset.sum_congr rfl (fun i hi => Finset.sum_comm)
    _ = _ := by simp only [Finset.sum_smul]

lemma scalarMatrix_star (a : Fin n → Fin n → ℂ) :
    star (E.scalarMatrix a)=E.scalarMatrix (fun i j => star (a j i)) := by
  simp only [scalarMatrix,star_sum,star_smul,E.star_entry]
  exact Finset.sum_comm

lemma scalarMatrix_smul (c : ℂ) (a : Fin n → Fin n → ℂ) :
    E.scalarMatrix (fun i j => c*a i j)=c • E.scalarMatrix a := by
  simp only [scalarMatrix,Finset.smul_sum,smul_smul]

lemma phase_star_self' (g : Fin n → ZMod 3) (i : Fin n) :
    phase g i*star (phase g i)=1 := by rw [mul_comm]; exact phase_star_self g i

def rankOne (g : Fin n → ZMod 3) : M :=
  E.scalarMatrix (fun i j => (n:ℂ)⁻¹*(phase g i*star (phase g j)))

lemma rankOne_star (g : Fin n → ZMod 3) : star (E.rankOne g)=E.rankOne g := by
  rw [rankOne,scalarMatrix_star]
  congr 1
  funext i j
  simp only [star_mul,star_inv₀,star_natCast,star_star]
  ring

lemma rankOne_mul (hn : n ≠ 0) (g : Fin n → ZMod 3) : E.rankOne g*E.rankOne g=E.rankOne g := by
  rw [rankOne,scalarMatrix_mul]
  congr 1
  funext i l
  have ht (j : Fin n) :
      ((n:ℂ)⁻¹*(phase g i*star (phase g j)))*((n:ℂ)⁻¹*(phase g j*star (phase g l)))=
        ((n:ℂ)⁻¹)^2*(phase g i*star (phase g l)) := by
    calc
      _ = ((n:ℂ)⁻¹)^2*(phase g i*star (phase g l))*(star (phase g j)*phase g j) := by ring
      _ = _ := by rw [phase_star_self,mul_one]
  simp only [ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

lemma rankOne_projection (hn : n ≠ 0) (g : Fin n → ZMod 3) : IsStarProjection (E.rankOne g) :=
  ⟨E.rankOne_mul hn g,E.rankOne_star g⟩

section
variable [PartialOrder M]

lemma trace_scalarMatrix_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : Fin n → Fin n → ℂ) (c : M) (hc : c ∈ E.commutant) :
    τ (E.scalarMatrix a*c)=(n:ℂ)⁻¹*(∑ i,a i i)*τ c := by
  simp only [scalarMatrix,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,
    E.trace_entry_commutant τ htr hn c hc,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul]
  ring

lemma trace_rankOne_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) (c : M) (hc : c ∈ E.commutant) :
    τ (E.rankOne g*c)=(n:ℂ)⁻¹*τ c := by
  rw [rankOne,E.trace_scalarMatrix_commutant τ htr hn _ c hc]
  simp only [phase_star_self',mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [mul_inv_cancel₀ hnC,mul_one]

lemma trace_rankOne (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (h1 : τ 1=1) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) : τ (E.rankOne g)=(n:ℂ)⁻¹ := by
  simpa only [mul_one,h1] using E.trace_rankOne_commutant τ htr hn g 1 E.commutant.one_mem

end

lemma coefficient_ext {x y : M} (h : ∀ i j,E.coefficient i j x=E.coefficient i j y) : x=y := by
  rw [← E.reconstruct x,← E.reconstruct y]
  simp only [h]

lemma coefficient_entry (i j a b : Fin n) :
    E.coefficient i j (E.entry a b)=if i=a ∧ b=j then (1:M) else 0 := by
  classical
  simp only [coefficient,E.entry_mul,ite_mul,zero_mul]
  by_cases hia : i=a
  · subst a
    by_cases hbj : b=j
    · subst b
      simp only [ite_true,and_self,E.sum_diagonal]
    · simp [hbj]
  · simp [hia]

lemma coefficient_smul (i j : Fin n) (c : ℂ) (x : M) :
    E.coefficient i j (c • x)=c • E.coefficient i j x := by
  simp only [coefficient,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

lemma coefficient_sum {J : Type*} (s : Finset J) (i j : Fin n) (f : J → M) :
    E.coefficient i j (∑ k ∈ s,f k)=∑ k ∈ s,E.coefficient i j (f k) := by
  simp only [coefficient,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

lemma coefficient_scalarMatrix (a : Fin n → Fin n → ℂ) (i j : Fin n) :
    E.coefficient i j (E.scalarMatrix a)=a i j • (1:M) := by
  classical
  simp only [scalarMatrix,E.coefficient_sum,E.coefficient_smul,E.coefficient_entry,smul_ite,smul_zero]
  simp only [ite_and]
  simp

lemma coefficient_mul_mem (i j : Fin n) (x c : M) (hc : c ∈ E.commutant) :
    E.coefficient i j (x*c)=E.coefficient i j x*c := by
  simp only [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = E.entry k i*x*(c*E.entry j k) := by noncomm_ring
    _ = _ := by rw [(hc j k).eq]; noncomm_ring

def phaseCoefficient (g : Fin n → ZMod 3) (x : M) : M :=
  (n:ℂ)⁻¹ • ∑ i,∑ j,(star (phase g i)*phase g j) • E.coefficient i j x

lemma phaseCoefficient_mem (g : Fin n → ZMod 3) (x : M) : E.phaseCoefficient g x ∈ E.commutant := by
  apply E.commutant.smul_mem
  apply E.commutant.sum_mem
  intro i hi
  apply E.commutant.sum_mem
  intro j hj
  exact E.commutant.smul_mem (E.coefficient_mem i j x) _

lemma rankOne_compression (g : Fin n → ZMod 3) (x : M) :
    E.rankOne g*x*E.rankOne g=E.rankOne g*E.phaseCoefficient g x := by
  apply E.coefficient_ext
  intro i l
  rw [E.coefficient_mul_mem i l _ _ (E.phaseCoefficient_mem g x)]
  rw [coefficient_product_matrix]
  simp only [coefficient_product_matrix,rankOne,coefficient_scalarMatrix,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  simp only [phaseCoefficient,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

variable [PartialOrder M] [StarOrderedRing M]

lemma rankOne_compression_norm (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) (x : M) :
    ‖τ.toPreGNS (E.rankOne g*x*E.rankOne g)‖^2=
      (n:ℝ)⁻¹*‖τ.toPreGNS (E.phaseCoefficient g x)‖^2 := by
  rw [E.rankOne_compression g x, norm_sq,norm_sq]
  have hb := E.phaseCoefficient_mem g x
  have hcomm : Commute (E.phaseCoefficient g x) (E.rankOne g) := by
    dsimp only [rankOne,scalarMatrix]
    apply Commute.sum_right
    intro i hi
    apply Commute.sum_right
    intro j hj
    exact (hb i j).smul_right _
  have hprod : star (E.rankOne g*E.phaseCoefficient g x)*(E.rankOne g*E.phaseCoefficient g x)=
      E.rankOne g*(star (E.phaseCoefficient g x)*E.phaseCoefficient g x) := by
    rw [star_mul,E.rankOne_star]
    have hstar : Commute (star (E.phaseCoefficient g x)) (E.rankOne g) := by
      simpa only [E.rankOne_star] using (commute_star_star.mpr hcomm)
    calc
      _ = star (E.phaseCoefficient g x)*(E.rankOne g*E.rankOne g)*E.phaseCoefficient g x := by noncomm_ring
      _ = _ := by rw [E.rankOne_mul hn g,hstar.eq]; noncomm_ring
  rw [hprod,E.trace_rankOne_commutant τ htr hn g _
    (E.commutant.mul_mem (E.commutant.star_mem' hb) hb)]
  have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end MatrixSystem
end HochschildMatrixSystems

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildFinitePhase
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n)

lemma phaseCoefficient_energy_bound (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    (∑ g : Fin n → ZMod 3, ‖τ.toPreGNS (E.phaseCoefficient g x)‖^2) ≤
      (Fintype.card (Fin n → ZMod 3):ℝ)*
        (‖τ.toPreGNS (E.expectation x)‖^2+‖τ.toPreGNS x‖^2/(n:ℝ)) := by
  classical
  have hdiag : ‖∑ i,τ.toPreGNS (E.coefficient i i x)‖^2=
      (n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2 := by
    rw [← map_sum,E.sum_coefficient_diagonal hn,map_smul,norm_smul,mul_pow]
    simp
  have hoff : (∑ i,∑ j,if i=j then 0 else ‖τ.toPreGNS (E.coefficient i j x)‖^2) ≤
      (n:ℝ)*‖τ.toPreGNS x‖^2 := by
    rw [← E.coefficient_norm_sq_sum τ htr hn x]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · positivity
    · exact le_rfl
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    _ = (n:ℝ)⁻¹^2 * ∑ g : Fin n → ZMod 3,
        ‖∑ i,∑ j,(star (phase g i)*phase g j) • τ.toPreGNS (E.coefficient i j x)‖^2 := by
      simp only [phaseCoefficient,map_smul,map_sum,norm_smul,norm_inv,Complex.norm_natCast,mul_pow,
        ← Finset.mul_sum]
    _ = (n:ℝ)⁻¹^2 * ((Fintype.card (Fin n → ZMod 3):ℝ)*
        ((n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2+
          ∑ i,∑ j,if i=j then 0 else ‖τ.toPreGNS (E.coefficient i j x)‖^2)) := by
      rw [phase_parseval,hdiag]
    _ ≤ (n:ℝ)⁻¹^2 * ((Fintype.card (Fin n → ZMod 3):ℝ)*
        ((n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2+(n:ℝ)*‖τ.toPreGNS x‖^2)) := by
      gcongr
    _ = _ := by field_simp

lemma exists_phase_energy_bound {I : Type*} [Fintype I] (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : I → M) :
    ∃ g : Fin n → ZMod 3,
      (∑ i, ‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2) ≤
        ∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ)) := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    E.phaseCoefficient_energy_bound τ htr hn (x i))
  rw [Finset.sum_comm,← Finset.mul_sum] at hh
  by_contra hg
  push Not at hg
  have hstrict : (Fintype.card (Fin n → ZMod 3):ℝ)*
      (∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ))) <
        ∑ g : Fin n → ZMod 3, ∑ i,‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2 := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun _ _ => hg _)
  exact (not_lt_of_ge hh) hstrict

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
lemma exists_large_small_expectations
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (x : I → M) (hx : ∀ i, τ (x i)=0) {ε : ℝ} (hε : 0<ε) (N : ℕ) :
    ∃ (n : ℕ) (E : MatrixSystem M n), N<n ∧ ∀ i, ‖τ.toPreGNS (E.expectation (x i))‖<ε := by
  obtain ⟨n,E,hn,hE⟩ := exists_small_matrix_expectations e τ hτ h1 htr hfaith hfactor hdiff x hx hε
  obtain ⟨P,hPn,hP⟩ := exists_abstract_star_preadjoint e
  let hL := mul_hasPreadjoint e
  let hR := mul_right_hasPreadjoint e
  let eC := E.commutantPredualEquiv e hL hR P hP
  let ρ := E.commutantTrace τ
  obtain ⟨F⟩ := exists_matrixSystem eC ρ (E.commutantTrace_normal e hL hR P hP τ hτ)
    (E.commutantTrace_tracial τ htr) (E.commutantTrace_faithful τ hfaith)
    (E.commutantTrace_one τ h1) (E.factor_of_commutant _ rfl hfactor)
    (E.commutant_no_minimal ⟨0,hn⟩ hdiff) (N+1) (by omega)
  refine ⟨n*(N+1),E.extend F,?_,?_⟩
  · have hh : N+1 ≤ n*(N+1) := Nat.le_mul_of_pos_left _ hn
    omega
  · intro i
    exact (E.extension_gns_contract F τ htr (Nat.ne_of_gt hn) (by omega) (x i)).trans_lt (hE i)

include e in
 

theorem exists_small_corner_of_trace_limit
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (x : I → M) (hx : ∀ i, τ (x i)=0) {δ η₀ : ℝ} (hδ : 0<δ) (hη₀ : 0<η₀) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re < η₀ ∧
      ∀ i, ‖τ.toPreGNS (q*x i*q)‖^2 < δ*(τ q).re := by
  classical
  let K : ℝ := Fintype.card I+1
  have hK : 0<K := by dsimp [K]; positivity
  let η : ℝ := Real.sqrt (δ/(4*K))
  have hη : 0<η := Real.sqrt_pos.mpr (by positivity)
  have hηsq : η^2=δ/(4*K) := Real.sq_sqrt (by positivity)
  let B : ℝ := ∑ i,‖τ.toPreGNS (x i)‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨N,hNall⟩ := exists_nat_gt (max (4*B/δ) (1/η₀))
  have hN : 4*B/δ < (N:ℝ) := (le_max_left _ _).trans_lt hNall
  have hNη : 1/η₀ < (N:ℝ) := (le_max_right _ _).trans_lt hNall
  obtain ⟨n,E,hnN,hE⟩ := exists_large_small_expectations e τ hτ h1 htr hfaith hfactor hdiff x hx hη N
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le N) hnN
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hBlt : B/(n:ℝ)<δ/4 := by
    have hh : 4*B/δ<(n:ℝ) := hN.trans (by exact_mod_cast hnN)
    have hh' := (div_lt_iff₀ hδ).mp hh
    apply (div_lt_iff₀ hnR).mpr
    nlinarith
  have hsum : (∑ i,‖τ.toPreGNS (E.expectation (x i))‖^2) ≤ (Fintype.card I:ℝ)*η^2 := by
    calc
      _ ≤ ∑ _i : I,η^2 := Finset.sum_le_sum (fun i hi =>
        (sq_le_sq₀ (norm_nonneg _) hη.le).mpr (hE i).le)
      _ = _ := by simp
  have hcard : (Fintype.card I:ℝ)*η^2<δ/4 := by
    rw [hηsq]
    have hh : (Fintype.card I:ℝ)<K := by dsimp [K]; linarith
    have hrat : 0<δ/(4*K) := by positivity
    have hall : K*(δ/(4*K))=δ/4 := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hh hrat]
  have htotal : (∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ)))<δ := by
    rw [Finset.sum_add_distrib,← Finset.sum_div]
    change _ + B/(n:ℝ)<δ
    linarith
  obtain ⟨g,hg⟩ := E.exists_phase_energy_bound τ htr (Nat.ne_of_gt hn) x
  have hend : ∀ i,‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2<δ := by
    intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      sq_nonneg ‖τ.toPreGNS (E.phaseCoefficient g (x j))‖) (Finset.mem_univ i)
    exact hi.trans_lt (hg.trans_lt htotal)
  refine ⟨E.rankOne g,E.rankOne_projection (Nat.ne_of_gt hn) g,?_,?_,?_⟩
  · intro hz
    have ht := E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g
    rw [hz,map_zero] at ht
    exact (inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn) : (n:ℂ) ≠ 0)) ht.symm
  · rw [E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g]
    have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
    rw [he,Complex.ofReal_re]
    have hh : 1/η₀ < (n:ℝ) := hNη.trans (by exact_mod_cast hnN)
    exact (inv_lt_comm₀ hnR hη₀).mpr (by simpa only [one_div] using hh)
  · intro i
    rw [E.rankOne_compression_norm τ htr (Nat.ne_of_gt hn) g (x i),
      E.trace_rankOne τ htr h1 (Nat.ne_of_gt hn) g]
    have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
    rw [he,Complex.ofReal_re,mul_comm δ]
    exact mul_lt_mul_of_pos_left (hend i) (inv_pos.mpr hnR)

include e in
theorem exists_small_corner
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (x : I → M) (hx : ∀ i, τ (x i)=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧
      ∀ i, ‖τ.toPreGNS (q*x i*q)‖^2 < δ*(τ q).re := by
  obtain ⟨q,hq,hq0,_,hxq⟩ := exists_small_corner_of_trace_limit e τ hτ h1 htr hfaith
    hfactor hdiff x hx hδ (by norm_num : (0:ℝ)<1)
  exact ⟨q,hq,hq0,hxq⟩

end HochschildQuantization
end

end OAI
