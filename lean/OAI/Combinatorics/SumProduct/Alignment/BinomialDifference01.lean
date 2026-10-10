import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevTail03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators commutatorElement
noncomputable section
namespace CharacterFactorization
open CubeFaces CubePolynomials RationalFactorPeriods RationalLattice MalcevCharacters MalcevTailFactor
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (H : Filtration G) {n s : ℕ} (c : RealCoordinates (H.level 2) n) (hsk : SecondKind c)
variable (χ : H.level 2 →* Multiplicative ℝ) (k : Fin n → ℤ)
variable (hχ : ∀ x, (χ x).toAdd = IntegerHyperplane.form k (c.coord x))
variable (r : Fin s → ℕ)
variable (hlevel : ∀ i (x : H.level 2), x.val ∈ H.level (i.val+2) ↔
  ∀ u : Fin n, u.val < r i → c.coord x u = 0)
variable (hcomm : ∀ a b : G, ⁅a,b⁆ ∈ χ.ker.map (H.level 2).subtype)

 

theorem uniform_gamma_period_of_rational_lattice (Γ : Subgroup G)
    [DiscreteTopology (Γ.comap (H.level 2).subtype)]
    (hΓ : Γ.comap (H.level 2).subtype ≤ rationalSubgroup c)
    (K : Set (H.level 2)) (hK : IsCompact K)
    (hrep : ∀ x : H.level 2, ∃ y ∈ K, (y⁻¹*x).val ∈ Γ) :
    ∃ T : ℕ, 0 < T ∧ ∀ a : Fin s → H.level 2,
      Function.Periodic (fun z => (QuotientGroup.mk (gamma H c χ k r a z) : G ⧸ Γ)) (T:ℤ) := by
  let L := Γ.comap (H.level 2).subtype
  let : ConnectedSpace (H.level 2) := c.coord.symm.surjective.connectedSpace c.coord.symm.continuous
  let : LocallyCompactSpace (H.level 2) := c.coord.locallyCompactSpace_iff.mpr inferInstance
  obtain ⟨T,hT,hper⟩ := uniform_rational_word_period c L hΓ K hK hrep
    (rationalGenerator c k r) (generator_rational c k r)
    (fun i => i.val+2) (s+2) (fun i => by omega)
  refine ⟨T,hT,fun a z => ?_⟩
  have hp := hper (numerator χ a) z
  have hm := QuotientGroup.eq.mp hp
  exact QuotientGroup.eq.mpr hm

include hsk hχ hlevel in
 

theorem uniform_smooth_factorization (hbot : H.level s = ⊥)
    (Γ : Subgroup G) (hΓ : ∀ x : H.level 2, x.val ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord x i = z)
    (A C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∃ T : ℕ, 0 < T ∧
      ∀ (g : ℤ → G), g ∈ polynomials H 0 → g 0=1 → g 1 ∈ H.level 1 →
      ∃ a : Fin s → H.level 2,
        (∀ i, (a i).val ∈ H.level (i.val+2)) ∧
        (∀ z, g z = (orderedWord a (fun i => i.val+2) z).val * g 1 ^ z) ∧
        (∀ z, g z = epsilon H c χ k r a z * residual H c χ k r g a z * gamma H c χ k r a z) ∧
        epsilon H c χ k r a 0=1 ∧
        epsilon H c χ k r a ∈ polynomials H 0 ∧
        gamma H c χ k r a ∈ polynomials H 0 ∧
        residual H c χ k r g a ∈ polynomials (H.refine (χ.ker.map (H.level 2).subtype) hcomm) 0 ∧
        Function.Periodic (fun z => (QuotientGroup.mk (gamma H c χ k r a z) : G ⧸ Γ)) (T:ℤ) ∧
        ∀ L : ℝ, 1 ≤ L → (∀ i, L^(i.val+2)*‖(beta χ a i : UnitAddCircle)‖ ≤ C) →
          (∀ z : ℤ, |(z:ℝ)| ≤ A*L →
            ‖c.coord (orderedWord (smallCoeff c χ k r a) (fun i => i.val+2) z)‖ ≤ B) ∧
          (∀ z w : ℤ, |(z:ℝ)| ≤ A*L → |(w:ℝ)| ≤ A*L →
            ‖c.coord (orderedWord (smallCoeff c χ k r a) (fun i => i.val+2) z *
              (orderedWord (smallCoeff c χ k r a) (fun i => i.val+2) w)⁻¹)‖ ≤ (B/L)*|(z:ℝ)-(w:ℝ)|) := by
  obtain ⟨B,hB,hsmall⟩ := small_word_smooth c hsk χ k r (fun i => i.val+2) A C hC
  obtain ⟨T,hT,hper⟩ := uniform_gamma_period H c χ k r Γ hΓ
  refine ⟨B,hB,T,hT,?_⟩
  intro g hg h0 h1
  obtain ⟨a,ha,he,hep,hgp,hrp⟩ := normalized_factorization H c hsk χ k hχ r hlevel hcomm hbot g hg h0 h1
  exact ⟨a,ha,he,factorization_identity H c χ k r g a,epsilon_zero H c χ k r a,
    hep,hgp,hrp,hper a,fun L hL ha => hsmall L a hL ha⟩

end CharacterFactorization
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
noncomputable section
namespace BinomialDifference
variable (R : Type*) [CommRing R]

def step : Module.End R R[X] := taylor 1-LinearMap.id

def coefficient (j : ℕ) : R[X] →ₗ[R] R := (aeval (0:R)).toLinearMap ∘ₗ (step R)^j

lemma step_apply (p : R[X]) : step R p=taylor 1 p-p := rfl
lemma coefficient_apply (j : ℕ) (p : R[X]) : coefficient R j p=(((step R)^j) p).eval 0 := rfl
lemma coefficient_zero (p : R[X]) : coefficient R 0 p=p.eval 0 := rfl
lemma coefficient_succ (j : ℕ) (p : R[X]) : coefficient R (j+1) p=coefficient R j (step R p) := by
  simp only [coefficient_apply,pow_succ,Module.End.mul_apply]

lemma iterate_map {S : Type*} [CommRing S] (φ : R →+* S) (j : ℕ) (p : R[X]) :
    (((step R)^j) p).map φ=((step S)^j) (p.map φ) := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ,Module.End.mul_apply,ih,pow_succ,Module.End.mul_apply]
    congr 1
    simp only [step_apply,Polynomial.map_sub,map_taylor,map_one]

lemma coefficient_map {S : Type*} [CommRing S] (φ : R →+* S) (j : ℕ) (p : R[X]) :
    φ (coefficient R j p)=coefficient S j (p.map φ) := by
  simp only [coefficient_apply,← iterate_map R φ j p]
  rw [eval_map]
  simpa only [map_zero] using (eval₂_at_apply (p := ((step R)^j) p) φ 0).symm

lemma step_degree_lt {p : R[X]} (hp : p≠0) : (step R p).degree<p.degree :=
  degree_sub_lt_right (degree_taylor p 1) hp (leadingCoeff_taylor 1 p)

lemma iterate_eq_zero (j : ℕ) (p : R[X]) (hp : p.natDegree<j) : ((step R)^j) p=0 := by
  induction j generalizing p with
  | zero => omega
  | succ j ih =>
    rw [pow_succ,Module.End.mul_apply]
    by_cases hp0 : p=0
    · simp [hp0]
    by_cases hq0 : step R p=0
    · simp [hq0]
    apply ih
    have hh := step_degree_lt R hp0
    rw [degree_eq_natDegree hq0,degree_eq_natDegree hp0] at hh
    have hh' : (step R p).natDegree<p.natDegree := WithBot.coe_lt_coe.mp hh
    omega

lemma coefficient_eq_zero (j : ℕ) (p : R[X]) (hp : p.natDegree<j) : coefficient R j p=0 := by
  rw [coefficient_apply,iterate_eq_zero R j p hp,eval_zero]

def matrix (j i : ℕ) : ℤ := coefficient ℤ j (X^i)

lemma matrix_low (j i : ℕ) (hij : i<j) : matrix j i=0 := by
  apply coefficient_eq_zero
  simpa only [natDegree_X_pow] using hij

lemma coefficient_X_pow (j i : ℕ) : coefficient ℝ j (X^i)=(matrix j i:ℝ) := by
  simpa only [Polynomial.map_pow,map_X,matrix,Int.coe_castRingHom] using
    (coefficient_map ℤ (Int.castRingHom ℝ) j (X^i)).symm

lemma coefficient_expansion (s j : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ s) :
    coefficient ℝ j P=∑ i∈Finset.range (s+1),P.coeff i*(matrix j i:ℝ) := by
  conv_lhs => arg 2; rw [P.as_sum_range_C_mul_X_pow' (by omega : P.natDegree<s+1)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_eq_C_mul,map_smul,smul_eq_mul,coefficient_X_pow]

open RationalFactorPeriods
lemma step_choose (j : ℕ) : step ℝ (choosePolynomial (j+1))=choosePolynomial j := by
  apply Polynomial.funext
  intro x
  simp only [step_apply,eval_sub,taylor_eval,choosePolynomial_eval]
  rw [Ring.choose_succ_succ]
  ring

lemma step_choose_zero : step ℝ (choosePolynomial 0)=0 := by
  simp [step_apply,choosePolynomial,descPochhammer_zero]

lemma coefficient_choose (j i : ℕ) : coefficient ℝ j (choosePolynomial i)=if i=j then 1 else 0 := by
  induction j generalizing i with
  | zero =>
    rw [coefficient_zero,choosePolynomial_eval,Ring.choose_zero_ite]
  | succ j ih =>
    rw [coefficient_succ]
    cases i with
    | zero => simp [step_choose_zero]
    | succ i => simp only [step_choose,ih,Nat.add_right_cancel_iff]

 

lemma coefficient_word {G : Type*} [Group G] {l : ℕ}
    (χ : G →* Multiplicative ℝ) (a : Fin l → G) (r : ℕ) (i : Fin l) :
    coefficient ℝ (i.val+r) (wordCharacterPolynomial χ a (fun j => j.val+r))=(χ (a i)).toAdd := by
  classical
  rw [wordCharacterPolynomial,map_sum]
  simp only [← smul_eq_C_mul,map_smul,smul_eq_mul,coefficient_choose,Nat.add_right_cancel_iff]
  simp only [Fin.val_inj, mul_ite, mul_one, mul_zero]
  simpa only [Finset.mem_univ, ite_true] using Finset.sum_ite_eq' Finset.univ i (fun x => (χ (a x)).toAdd)

end BinomialDifference
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
noncomputable section
namespace BinomialDifference

def conversionBound (s : ℕ) : ℝ :=
  1+∑ j∈range (s+1), ∑ i∈range (s+1), |(matrix j i:ℝ)|

lemma conversionBound_pos (s : ℕ) : 0<conversionBound s := by
  have h : 0 ≤ ∑ j∈range (s+1), ∑ i∈range (s+1), |(matrix j i:ℝ)| :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
  unfold conversionBound
  linarith

lemma row_bound (s j : ℕ) (hj : j ≤  s) :
    (∑ i∈range (s+1), |(matrix j i:ℝ)|) ≤ conversionBound s := by
  have h := single_le_sum (fun u (_ : u∈range (s+1)) =>
    sum_nonneg (fun i (_ : i∈range (s+1)) => abs_nonneg (matrix u i:ℝ))) (mem_range.mpr (by omega : j<s+1))
  unfold conversionBound
  linarith

 

lemma coefficient_bound (s k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤  s)
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hc : ∀ i : ℕ, k ≤ i → ∃ m : ℤ, |P.coeff i-m| ≤ C/L^i)
    (j : ℕ) (hj : k ≤ j) :
    L^j*‖(coefficient ℝ j P : UnitAddCircle)‖ ≤ conversionBound s*C := by
  classical
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  by_cases hjs : j ≤  s
  · let m : ℕ → ℤ := fun i => if hi : k ≤ i then (hc i hi).choose else 0
    have hm (i : ℕ) (hi : k ≤ i) : |P.coeff i-m i| ≤ C/L^i := by
      simpa only [m,dite_eq_left hi] using (hc i hi).choose_spec
    let z : ℤ := ∑ i∈range (s+1), m i*matrix j i
    have he : coefficient ℝ j P-z=∑ i∈range (s+1), (P.coeff i-m i)*(matrix j i:ℝ) := by
      rw [coefficient_expansion s j P hP]
      simp only [z,Int.cast_sum,Int.cast_mul,← sum_sub_distrib,sub_mul]
    have ht (i : ℕ) (hi : i∈range (s+1)) :
        |(P.coeff i-m i)*(matrix j i:ℝ)| ≤ (C/L^j)*|(matrix j i:ℝ)| := by
      by_cases hij : j ≤ i
      · rw [abs_mul]
        apply mul_le_mul_of_nonneg_right ((hm i (hj.trans hij)).trans ?_) (abs_nonneg _)
        exact div_le_div_of_nonneg_left hC (pow_pos hLp _) (pow_le_pow_right₀ hL hij)
      · simp only [matrix_low j i (by omega),Int.cast_zero,mul_zero,abs_zero,le_refl]
    have hh : ‖(coefficient ℝ j P : UnitAddCircle)‖ ≤ (conversionBound s*C)/L^j := by
      calc
        _ = |coefficient ℝ j P-round (coefficient ℝ j P)| := UnitAddCircle.norm_eq
        _ ≤ |coefficient ℝ j P-z| := round_le _ _
        _ = |∑ i∈range (s+1), (P.coeff i-m i)*(matrix j i:ℝ)| := by rw [he]
        _ ≤ ∑ i∈range (s+1), |(P.coeff i-m i)*(matrix j i:ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ i∈range (s+1), (C/L^j)*|(matrix j i:ℝ)| := sum_le_sum ht
        _ = (C/L^j)*(∑ i∈range (s+1), |(matrix j i:ℝ)|) := (mul_sum _ _ _).symm
        _ ≤ (C/L^j)*conversionBound s := mul_le_mul_of_nonneg_left (row_bound s j hjs) (by positivity)
        _ = _ := by ring
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hLp j)).mp hh
  · rw [coefficient_eq_zero ℝ j P (by omega)]
    simp only [AddCircle.coe_zero,norm_zero,mul_zero]
    exact mul_nonneg (conversionBound_pos s).le hC

open RationalFactorPeriods
 

lemma word_coefficient_bound {G : Type*} [Group G] {l : ℕ}
    (χ : G →* Multiplicative ℝ) (a : Fin l → G) (r s : ℕ)
    (P : ℝ[X]) (hP : P.natDegree ≤  s)
    (he : ∀ z : ℤ, P.eval (z:ℝ)=(χ (orderedWord a (fun i => i.val+r) z)).toAdd)
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hc : ∀ j : ℕ, r ≤ j → ∃ m : ℤ, |P.coeff j-m| ≤ C/L^j) :
    ∀ i : Fin l, L^(i.val+r)*‖((χ (a i)).toAdd : UnitAddCircle)‖ ≤ conversionBound s*C := by
  have hp : P=wordCharacterPolynomial χ a (fun i => i.val+r) := by
    apply Polynomial.eq_of_eval_nat_eq
    intro z
    simpa only [Int.cast_natCast] using (he (z:ℤ)).trans (wordCharacterPolynomial_eval χ a _ (z:ℤ)).symm
  intro i
  have hh := coefficient_bound s r P hP L C hL hC hc (i.val+r) (by omega)
  rwa [hp,coefficient_word] at hh

end BinomialDifference

end
end
end
end
end

end OAI
