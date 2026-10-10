import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BracketDrift01
import OAI.Combinatorics.SumProduct.Alignment.PolynomialCharacter01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open Finset Set BracketHyperplanes
open scoped BigOperators
end
end
 

 
section
noncomputable section
open Finset BracketHyperplanes
open scoped BigOperators
namespace BracketDrift

def matrixContraction {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) (γ : Fin d → ℝ) (j : Fin d) : ℝ :=
  ∑ i, γ i*(M i j:ℝ)

lemma matrixContraction_bound {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    (B : ℝ) (hB : 0≤B) (hM : ∀ i j, |(M i j:ℝ)|≤B)
    (γ : Fin d → ℝ) (hγ : ‖γ‖≤1) : ‖matrixContraction M γ‖≤(d:ℝ)*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change |∑ i,γ i*(M i j:ℝ)|≤(d:ℝ)*B
  calc
    _ ≤ ∑ i,|γ i*(M i j:ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d,B := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      have hi : |γ i|≤1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mp hγ i
      exact (mul_le_mul hi (hM i j) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp

 

theorem matrix_bracket_alternative (d : ℕ) (B : ℕ) (A δ : ℝ) (hA : 0<A) (hδ : 0<δ) :
    ∃ R : ℕ, 0<R ∧ ∃ C : ℝ, 0<C ∧
      ∀ N : ℕ, 0<N → ∀ M : Matrix (Fin d) (Fin d) ℤ,
      (∀ i j, |M i j|≤B) → ∀ γ β : Fin d → ℝ, ‖γ‖≤1 →
      ∀ ρ b : ℝ, ∀ x : ℕ → Fin d → ℝ, (∀ n, ‖x n‖≤1) →
      (∀ n, BracketHyperplanes.torusMap (x n)=BracketHyperplanes.torusMap (fun i => γ i*n+β i)) →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ n∈S, ‖((b+ρ*n+∑ i,matrixContraction M γ i*x n i:ℝ):UnitAddCircle)‖≤A/N) →
      M=0 ∨ ∃ k : Fin d → ℤ, k≠0 ∧ (∀ i, |k i|≤R) ∧
        ∃ m : ℤ, |(∑ i,(k i:ℝ)*γ i)-m|≤C/N := by
  classical
  let A' := A+(d:ℝ)*B+1
  have hAA' : A≤A' := by dsimp [A']; nlinarith [Nat.cast_nonneg (d*B) (α:=ℝ)]
  have hBnd : (d:ℝ)*B≤A' := by dsimp [A']; linarith
  have hA' : 0<A' := hA.trans_le hAA'
  obtain ⟨R,hR,C,hC,hdesc⟩ := arbitrary_drift_alternative d A' δ hA' hδ
  refine ⟨R*(B+1),by positivity,C,hC,?_⟩
  intro N hN M hM γ β hγ ρ b x hx horbit S hSN hS hsmall
  by_cases hzero : M=0
  · exact Or.inl hzero
  right
  have hMreal (i j : Fin d) : |(M i j:ℝ)|≤B := by exact_mod_cast hM i j
  have ha := (matrixContraction_bound M B (Nat.cast_nonneg _) hMreal γ hγ).trans hBnd
  have hsmall' (n : ℕ) (hn : n∈S) :
      ‖((b+ρ*n+∑ i,matrixContraction M γ i*x n i:ℝ):UnitAddCircle)‖≤A'/N :=
    (hsmall n hn).trans (div_le_div_of_nonneg_right hAA' (Nat.cast_nonneg _))
  rcases hdesc N hN (matrixContraction M γ) γ β ha ρ b x hx horbit S hSN hS hsmall' with hrat | hfreq
  · obtain ⟨r,hr,hrR,hcoeff⟩ := hrat
    have hex : ∃ j : Fin d, (fun i => M i j)≠0 := by
      by_contra! hh
      apply hzero
      ext i j
      exact congrFun (hh j) i
    obtain ⟨j,hj⟩ := hex
    let k (i : Fin d) := r*M i j
    have hk : k≠0 := by
      intro hz
      apply hj
      funext i
      exact (mul_eq_zero.mp (congrFun hz i)).resolve_left hr
    obtain ⟨m,hm⟩ := hcoeff j
    refine ⟨k,hk,?_,m,?_⟩
    · intro i
      calc
        |k i| = |r| * |M i j| := abs_mul _ _
        _ ≤ (R:ℤ)*B := mul_le_mul hrR (hM i j) (abs_nonneg _) (Int.natCast_nonneg _)
        _ ≤ R*(B+1) := by nlinarith [Int.natCast_nonneg R]
    · convert hm using 2
      simp only [k,matrixContraction,Int.cast_mul,mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
  · obtain ⟨k,hk,hkR,m,hm⟩ := hfreq
    refine ⟨k,hk,?_,m,hm⟩
    intro i
    apply (hkR i).trans
    have h0 : 0≤(R:ℤ)*B := by positivity
    push_cast
    linarith

end BracketDrift
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset BracketHyperplanes
open scoped BigOperators
namespace NonabelianCharacterDescent
open BracketDrift PolynomialCharacterDescent

 

theorem scalar_descent (d s B : ℕ) (hs : 2≤ s) (δ A : ℝ) (hδ : 0<δ) (hA : 0≤A) :
    ∃ R : ℕ, 0<R ∧ ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀≤N → ∀ M : Matrix (Fin d) (Fin d) ℤ,
      (∀ i j, |M i j|≤B) → ∀ γ β : Fin d → ℝ, ‖γ‖≤1 →
      ∀ x : ℕ → Fin d → ℝ, (∀ n, ‖x n‖≤1) →
      (∀ n, BracketHyperplanes.torusMap (x n)=BracketHyperplanes.torusMap (fun i => γ i*n+β i)) →
      ∀ P Q : ℝ[X], P.natDegree≤ s → Q.natDegree≤ s →
      ∀ S : Finset ℕ, S⊆range N → δ*N≤(S.card:ℝ) →
      (∀ h∈S, ∀ j : ℕ, 0<j → j≤ s → ∃ z : ℤ,
        |(P+taylor (h:ℝ) Q-Q).coeff j+
          (if j=1 then ∑ i,matrixContraction M γ i*x h i else 0)-z|≤A/(N:ℝ)^j) →
      (∃ k : Fin d → ℤ, k≠0 ∧ (∀ i, |k i|≤R) ∧
        ∃ m : ℤ, |(∑ i,(k i:ℝ)*γ i)-m|≤C/N) ∨
      (M=0 ∧ ∃ q : ℤ, q≠0 ∧ |q|≤R ∧
        (∀ j : ℕ, 0<j → ∃ m : ℤ, |(q:ℝ)*P.coeff j-m|≤C/(N:ℝ)^j) ∧
        (∀ j : ℕ, 1<j → ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m|≤C/(N:ℝ)^j)) := by
  classical
  obtain ⟨R₁,hR₁,C₁,hC₁,L₁,hL₁,hpoly⟩ := polynomial_descent s hs δ A hδ hA
  obtain ⟨R₂,hR₂,C₂,hC₂,hmat⟩ := matrix_bracket_alternative d (R₁*B) C₁ δ hC₁ hδ
  obtain ⟨R₃,hR₃,C₃,hC₃,L₃,hL₃,hzero⟩ := zero_commutator_descent s (by omega) δ A hδ hA
  let R := max R₂ R₃
  let C := max C₂ C₃
  let L := max L₁ L₃
  have hR₂' : (R₂:ℤ)≤R := by exact_mod_cast (le_max_left R₂ R₃)
  have hR₃' : (R₃:ℤ)≤R := by exact_mod_cast (le_max_right R₂ R₃)
  have hC₂' : C₂≤C := le_max_left _ _
  have hC₃' : C₃≤C := le_max_right _ _
  refine ⟨R,hR₂.trans_le (le_max_left _ _),C,hC₂.trans_le hC₂',L,hL₁.trans_le (le_max_left _ _),?_⟩
  intro N hLN M hM γ β hγ x hx horbit P Q hP hQ S hSN hS hsmall
  have hL₁N : L₁≤N := (le_max_left _ _).trans hLN
  have hL₃N : L₃≤N := (le_max_right _ _).trans hLN
  have hN : 0<N := hL₁.trans_le hL₁N
  let σ (h : ℕ) := ∑ i,matrixContraction M γ i*x h i
  obtain ⟨q,hq,hqR,hhigh,hlinear⟩ := hpoly N hL₁N P Q hQ σ S hSN hS
    (by intro h hh; simpa using hsmall h hh 2 (by decide) hs)
    (by intro h hh; simpa [σ] using hsmall h hh 1 (by decide) (by omega))
  let M' : Matrix (Fin d) (Fin d) ℤ := fun i j => q*M i j
  have hM' (i j : Fin d) : |M' i j|≤R₁*B := by
    change |q*M i j|≤((R₁*B:ℕ):ℤ)
    rw [abs_mul,Nat.cast_mul]
    exact mul_le_mul hqR (hM i j) (abs_nonneg _) (Int.natCast_nonneg _)
  have he (h : ℕ) : (q:ℝ)*P.coeff 1+(2*(q:ℝ)*Q.coeff 2)*(h:ℝ)+
      ∑ i,matrixContraction M' γ i*x h i =
        (q:ℝ)*P.coeff 1+2*(q:ℝ)*Q.coeff 2*h+(q:ℝ)*σ h := by
    have hcoeff (j : Fin d) : matrixContraction M' γ j=(q:ℝ)*matrixContraction M γ j := by
      simp only [matrixContraction,M',Int.cast_mul,mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    simp only [hcoeff,σ,mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  have hsmall' (h : ℕ) (hh : h∈S) :
      ‖(((q:ℝ)*P.coeff 1+(2*(q:ℝ)*Q.coeff 2)*(h:ℝ)+
        ∑ i,matrixContraction M' γ i*x h i:ℝ):UnitAddCircle)‖≤C₁/N := by
    rw [he]
    obtain ⟨z,hz⟩ := hlinear h hh
    rw [UnitAddCircle.norm_eq]
    exact (round_le _ z).trans hz
  rcases hmat N hN M' hM' γ β hγ (2*(q:ℝ)*Q.coeff 2) ((q:ℝ)*P.coeff 1)
    x hx horbit S hSN hS hsmall' with hz | hf
  · right
    have hMz : M=0 := by
      ext i j
      apply (mul_eq_zero.mp (congrFun (congrFun hz i) j)).resolve_left hq
    refine ⟨hMz,?_⟩
    obtain ⟨r,hr,hrR,hP',hQ'⟩ := hzero N hL₃N P Q hP hQ S hSN hS (by
      intro h hh j hj hjs
      simpa [hMz,matrixContraction] using hsmall h hh j hj hjs)
    refine ⟨r,hr,hrR.trans hR₃',?_,?_⟩
    · intro j hj
      obtain ⟨m,hm⟩ := hP' j hj
      exact ⟨m,hm.trans (div_le_div_of_nonneg_right hC₃' (by positivity))⟩
    · intro j hj
      obtain ⟨m,hm⟩ := hQ' j hj
      exact ⟨m,hm.trans (div_le_div_of_nonneg_right hC₃' (by positivity))⟩
  · left
    obtain ⟨k,hk,hkR,m,hm⟩ := hf
    exact ⟨k,hk,fun i => (hkR i).trans hR₂',m,
      hm.trans (div_le_div_of_nonneg_right hC₂' (Nat.cast_nonneg _))⟩

end NonabelianCharacterDescent
end
end
 

 
section
noncomputable section
open scoped commutatorElement BigOperators
namespace LeibmanSquare
open CubeFaces CubePolynomials SquareHorizontalCharacter _root_.Polynomial _root_.OAI.Polynomial
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (ξ : level H h0 1 →* Multiplicative ℝ)

def pairTailCharacter : PairTail.square (H.level 2) →* Multiplicative ℝ :=
  ξ.comp (firstPairEquiv H h0 h1).symm.toMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma pairTailCharacter_base :
    PairTail.baseCharacter (H.level 2) (pairTailCharacter H h0 h1 ξ)=
      ξ.comp (diagonal H h0 h1) := by
  apply MonoidHom.ext
  intro g
  change ξ _ = ξ _
  apply congrArg ξ
  apply Subtype.ext
  change (g,g*1)=(g,g)
  simp
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma pairTailCharacter_lower :
    PairTail.lowerCharacter (H.level 2) (pairTailCharacter H h0 h1 ξ)=
      ξ.comp (lower H h0) := by
  apply MonoidHom.ext
  intro g
  change ξ _ = ξ _
  apply congrArg ξ
  apply Subtype.ext
  change (1,1*(g:G))=(1,(g:G))
  simp
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma pairTailCharacter_bracket (a b : G) :
    PairTail.lowerCharacter (H.level 2) (pairTailCharacter H h0 h1 ξ)
      (PairTail.bracket (H.level 2) (SquareHorizontalCharacter.commutator_mem H h1) a b)=pairing H h0 h1 ξ a b := by
  rw [pairTailCharacter_lower]
  rfl

 

lemma actual_square_character_identity {f : ℤ → G} (hf : Polynomial H 0 f)
    (hf0 : f 0=1) (h n : ℤ) (v : G) :
    (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n)).toAdd=
      ((ξ.comp (diagonal H h0 h1)) (f n)).toAdd+
      (((ξ.comp (lower H h0)) (linearRemainder H h0 hf hf0 (n+h))).toAdd-
       ((ξ.comp (lower H h0)) (linearRemainder H h0 hf hf0 n)).toAdd)+
      (n:ℝ)*(pairing H h0 h1 ξ (f 1) v).toAdd := by
  have he := PairTail.square_orbit_identity (H.level 2) (pairTailCharacter H h0 h1 ξ)
    (SquareHorizontalCharacter.commutator_mem H h1) (f 1) v (linearRemainder H h0 hf hf0) h n
  rw [← linearNormalizedPair_eq_pairTail H h0 h1 hf hf0 (f 1)
    (linearRemainder H h0 hf hf0) (linearRemainder_mul H h0 hf hf0)
    (SquareHorizontalCharacter.commutator_mem H h1) h n v] at he
  rw [pairTailCharacter_base,pairTailCharacter_bracket,pairTailCharacter_lower,
    ← linearRemainder_mul H h0 hf hf0 n] at he
  simpa only [pairTailCharacter,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using he

 

theorem exists_actual_square_polynomials (s : ℕ) (hs : H.level (s+1)=⊥)
    {f : ℤ → G} (hf : Polynomial H 0 f) (hf0 : f 0=1) :
    ∃ P Q : ℝ[X], P.natDegree ≤ s ∧ Q.natDegree ≤ s ∧ Q.eval 0=0 ∧ Q.eval 1=0 ∧
      (∀ n : ℤ, P.eval (n:ℝ)=((ξ.comp (diagonal H h0 h1)) (f n)).toAdd) ∧
      (∀ n : ℤ, Q.eval (n:ℝ)=((ξ.comp (lower H h0)) (linearRemainder H h0 hf hf0 n)).toAdd) ∧
      ∀ h n : ℤ, ∀ v : G,
        (P+taylor (h:ℝ) Q-Q+C ((pairing H h0 h1 ξ (f 1) v).toAdd)*X).eval (n:ℝ)=
        (ξ (linearNormalizedPair H h0 h1 hf (linearRemainder H h0 hf hf0 h) h v n)).toAdd := by
  obtain ⟨P,hP,hPe⟩ := character_polynomial H s hs hf (ξ.comp (diagonal H h0 h1))
  obtain ⟨Q,hQ,hQ0,hQ1,hQe⟩ := remainder_character_polynomial H h0 h1 s hs hf hf0
    (ξ.comp (lower H h0))
  refine ⟨P,Q,hP,hQ,hQ0,hQ1,hPe,hQe,?_⟩
  intro h n v
  rw [eval_add,eval_sub,eval_add,eval_mul,eval_C,eval_X,taylor_eval,
    ← Int.cast_add,hPe,hQe,hQe,actual_square_character_identity H h0 h1 ξ hf hf0 h n v]
  ring

end LeibmanSquare

end
end
end
end
end

end OAI
