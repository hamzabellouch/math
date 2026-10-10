import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DensePolynomial01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators

namespace DenseModularPolynomial
open PolynomialWeyl _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
noncomputable section
 
theorem rough_lattice_inverse (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ N : ℕ, 0 < N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
    ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
    ∀ p : ℝ[X], p.natDegree ≤ d →
    (∀ n ∈ S, ∃ z : ℤ, |p.eval (n:ℝ)-z| ≤ ε) →
    ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ A ∧ ∃ m : ℕ → ℤ,
      ∀ j : ℕ, 0 < j → j ≤ d →
        |(q:ℝ)*p.coeff j - m j| ≤ (A:ℝ)/(N:ℝ)^j := by
  obtain ⟨R,hR⟩ := exists_nat_gt (max (1:ℝ) (16/δ))
  have hRone : (1:ℝ) ≤ R := (le_max_left _ _).trans hR.le
  have hRpos : 0 < R := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hRone)
  have hδR : 16 ≤ δ*(R:ℝ) := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hR.le)
    nlinarith only [h]
  obtain ⟨A,hA,hInverse⟩ := WeylCoefficients.coefficient_inverse d (δ/16) (by positivity)
  let ε₀ := 1/(4*Real.pi*R)
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨A*R,by positivity,ε₀,hε₀,?_⟩
  intro N hN ε hε hεsmall S hSN hS p hp hgood
  have hsmall : 2*Real.pi*R*ε ≤ (1:ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_left hεsmall (by positivity : 0 ≤ 2*Real.pi*R)
    have he : 2*Real.pi*R*ε₀ = (1:ℝ)/2 := by
      dsimp [ε₀]
      field_simp
      ring
    rwa [he] at h
  obtain ⟨a,ha,b,hb,hab,hm⟩ := FejerDetection.detect N R hN hRpos δ ε hδ hδR hε
    hsmall S hSN hS (fun n => p.eval (n:ℝ)) hgood
  let c : ℤ := (a:ℤ)-b
  have hc : c ≠ 0 := by
    dsimp [c]
    exact sub_ne_zero.mpr (by exact_mod_cast hab)
  let P := C (c:ℝ)*p
  have hP : P.natDegree ≤ d := by
    exact (natDegree_mul_le.trans (by simp)).trans hp
  have hmean : δ/16 ≤ ‖mean N (polynomialPhase P)‖ := by
    change δ/16 ≤ ‖mean N (fun n => phase (P.eval (n:ℝ)))‖
    simpa only [P,eval_mul,eval_C,c,Int.cast_sub,Int.cast_natCast] using hm
  obtain ⟨q,hq,hqA,m,hm⟩ := hInverse N hN P hP hmean
  have habound : a < R := mem_range.mp ha
  have hbbound : b < R := mem_range.mp hb
  have hcR : |c| ≤ (R:ℤ) := by
    rw [abs_le]
    dsimp [c]
    constructor <;> omega
  have hqbound : |(q:ℤ)*c| ≤ (A*R:ℕ) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg q)]
    exact_mod_cast mul_le_mul (Int.ofNat_le.mpr hqA) hcR (abs_nonneg c)
      (Int.natCast_nonneg A)
  refine ⟨(q:ℤ)*c,mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) hc,hqbound,m,?_⟩
  intro j hj hjd
  have h := hm j hj hjd
  have hAA : (A:ℝ) ≤ A*R := by nlinarith [Nat.cast_nonneg (α := ℝ) A]
  have h' := h.trans (div_le_div_of_nonneg_right hAA (by positivity))
  simpa only [P,coeff_C_mul,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,mul_assoc] using h'

 

theorem lattice_inverse (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
    ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
    ∀ p : ℝ[X], p.natDegree ≤ d →
    (∀ n ∈ S, ∃ z : ℤ, |p.eval (n:ℝ)-z| ≤ ε) →
    ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ C ∧ ∃ m : ℕ → ℤ,
      ∀ j : ℕ, 0 < j → j ≤ d →
        |(q:ℝ)*p.coeff j - m j| ≤ (C:ℝ)*ε/(N:ℝ)^j := by
  classical
  obtain ⟨A,hA,η,hη,hinv⟩ := rough_lattice_inverse d δ hδ
  let B := (d+1)*(A+1)
  let α : ℝ := δ/(2*B+3)
  have hα : 0 < α := by dsimp [α]; positivity
  let K := DensePolynomialInterpolation.coefficientConstant d *
    DensePolynomialInterpolation.uniformBound d α
  have hK : 0 ≤ K := by
    dsimp [K,DensePolynomialInterpolation.uniformBound]
    exact mul_nonneg (DensePolynomialInterpolation.coefficientConstant_pos d).le (by positivity)
  obtain ⟨C,hC⟩ := exists_nat_gt (max (A:ℝ) (K*A))
  have hAC : (A:ℝ) ≤ C := (le_max_left _ _).trans hC.le
  have hKC : K*A ≤ (C:ℝ) := (le_max_right _ _).trans hC.le
  have hCpos : 0 < C := by exact_mod_cast (Nat.cast_pos.mpr hA : (0:ℝ)<A).trans_le hAC
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max (1:ℝ) (2*(d+1)/α))
  have hN₀pos : 0 < N₀ := by
    have h := lt_of_le_of_lt (le_max_left _ _) hN₀
    exact_mod_cast (lt_trans zero_lt_one h)
  let ε₀ := min η (1/(A:ℝ))
  have hε₀ : 0 < ε₀ := lt_min hη (by positivity)
  refine ⟨C,hCpos,ε₀,hε₀,N₀,hN₀pos,?_⟩
  intro N hN₀N ε hε hεsmall S hSN hS p hp hgood
  have hN : 0 < N := hN₀pos.trans_le hN₀N
  have hεη : ε ≤ η := hεsmall.trans (min_le_left _ _)
  have hAε : (A:ℝ)*ε ≤ 1 := by
    have h := (le_div_iff₀ (Nat.cast_pos.mpr hA)).mp (hεsmall.trans (min_le_right _ _))
    nlinarith only [h]
  obtain ⟨q,hq,hqA,m,hm⟩ := hinv N hN ε hε hεη S hSN hS p hp hgood
  obtain ⟨u,r,hr,hrdeg,hrcoeff,hrbound⟩ :=
    PolynomialIntegralResidual.residual d N A hN p hp q m hm
  have hqA' : |(q:ℝ)| ≤ A := by exact_mod_cast hqA
  have hsmall : |(q:ℝ)| * ε ≤ 1 :=
    (mul_le_mul_of_nonneg_right hqA' hε).trans hAε
  let E : Finset ℤ := S.image (fun n : ℕ => (n:ℤ))
  have hEcard : E.card = S.card := card_image_of_injective _ (by intro a b h; change (a:ℤ) = b at h; exact_mod_cast h)
  have hEden : δ*N ≤ (E.card:ℝ) := by rwa [hEcard]
  have hEN : ∀ n ∈ E, (n:ℝ) ∈ Set.Icc 0 (N:ℝ) := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
    simp only [Int.cast_natCast,Set.mem_Icc]
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast (mem_range.mp (hSN hk)).le⟩
  have hlarge : (2*(d+1):ℝ) ≤ δ*N/(2*B+3) := by
    have h := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hN₀.le)
    have hNcast : (N₀:ℝ) ≤ N := by exact_mod_cast hN₀N
    have hh := mul_le_mul_of_nonneg_right hNcast hα.le
    have h' : (2*(d+1):ℝ) ≤ α*N := by nlinarith only [h,hh]
    simpa only [α,div_mul_eq_mul_div] using h'
  have hEgood : ∀ n ∈ E, ∃ z : ℤ, |r.eval (n:ℝ)-z| ≤ |(q:ℝ)| * ε := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
    obtain ⟨z,hz⟩ := hgood k hk
    exact PolynomialIntegralResidual.residual_near_integer p r u q k z ε hr
      (by simpa only [Int.cast_natCast] using hz)
  have hqC : |q| ≤ (C:ℤ) := hqA.trans (by exact_mod_cast hAC)
  refine ⟨q,hq,hqC,m,?_⟩
  intro j hj hjd
  have hc := DensePolynomialInterpolation.bounded_lattice_coefficients d N B hN
    δ (|(q:ℝ)| * ε) hδ (by positivity) hsmall hlarge E hEden hEN r hrdeg
    (fun n hn => hrbound _ (hEN n hn)) hEgood j hj hjd
  rw [hrcoeff j hj hjd] at hc
  change |(q:ℝ)*p.coeff j-m j| ≤ K*(|(q:ℝ)| * ε)/(N:ℝ)^j at hc
  apply hc.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hqK := (mul_le_mul_of_nonneg_left hqA' hK).trans hKC
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hqK hε

end
end DenseModularPolynomial

end
 

 
section

 

open scoped commutatorElement Pointwise
namespace LeibmanSquare
open CubeFaces
variable {G A : Type*} [Group G] [AddCommGroup A]
 

lemma polynomial_of_cube_mem (H : Filtration G) {k : ℕ} {f : A → G}
    (hf : f ∈ CubePolynomials.polynomials H k) : Polynomial H k f := by
  intro hs
  induction hs generalizing k f with
  | nil =>
      intro n
      exact CubePolynomials.eval_mem hf n
  | cons h hs ih =>
      have hd : diff h f ∈ CubePolynomials.polynomials H (k+1) :=
        CubePolynomials.derivative_mem hf h
      have hh := ih hd
      intro n
      simpa only [iterDiff, List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hh n

lemma cube_mem_of_polynomial (H : Filtration G) {k : ℕ} {f : A → G}
    (hf : Polynomial H k f) : f ∈ CubePolynomials.polynomials H k := by
  rw [CubePolynomials.mem_polynomials]
  intro I
  induction I using Finset.induction_on generalizing k f with
  | empty =>
      intro h n
      have he : CubePolynomials.pattern ∅ h n f = face ∅ (f n) := by
        ext v
        simp [CubePolynomials.pattern, face]
      rw [he]
      exact face_mem_cube H (Finset.empty_subset ∅) (by simpa [iterDiff] using hf [] n)
  | @insert a I ha ih =>
      intro h n
      let l := CubePolynomials.pattern I h n f
      let u := CubePolynomials.pattern I h n (diff (h a) f)
      have hd : Polynomial H (k+1) (diff (h a) f) := by
        intro hs n
        simpa only [iterDiff,List.length_cons,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using hf ((h a)::hs) n
      have hl : l ∈ cube H I k := ih hf h n
      have hu : u ∈ cube H I (k+1) := ih hd h n
      have he : CubePolynomials.pattern (insert a I) h n f = l * upper a u := by
        funext v
        have haV : a ∉ v ∩ I := fun hh => ha (Finset.mem_inter.mp hh).2
        by_cases hav : a ∈ v
        · have hv : v ∩ insert a I = insert a (v ∩ I) := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then
              (f (n + ∑ i ∈ v ∩ I, h i))⁻¹ * f ((n + ∑ i ∈ v ∩ I, h i) + h a) else 1)
          rw [hv, Finset.sum_insert haV, ite_eq_left hav, mul_inv_cancel_left]
          congr 1
          abel
        · have hv : v ∩ insert a I = v ∩ I := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then u v else 1)
          rw [hv, ite_eq_right hav, mul_one]
      rw [he]
      exact (cube H (insert a I) k).mul_mem
        (cube_mono H (Finset.subset_insert a I) k hl) (upper_cube_mem H ha k hu)

theorem polynomial_iff_cube_mem (H : Filtration G) (k : ℕ) (f : A → G) :
    Polynomial H k f ↔ f ∈ CubePolynomials.polynomials H k :=
  ⟨cube_mem_of_polynomial H,polynomial_of_cube_mem H⟩

 

theorem reduced_cube_polynomial (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) {s : ℕ} (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥)
    {f : A → G} (hf : f ∈ CubePolynomials.polynomials H 0) (t : A) (a b : G) :
    let R := restricted H h0
    letI := last_normal H h0 hs0 hs
    let π := QuotientGroup.mk' (R.level s)
    let Q := mapFiltration R π
    let p := fun n => π (restrictedConj H h0 h1 a b
      (normalizedPair H h0 (polynomial_of_cube_mem H hf) t n))
    p ∈ CubePolynomials.polynomials Q 0 ∧
      ∀ ts : List A, s ≤ ts.length → ∀ n, iterDiff ts p n = 1 := by
  dsimp only
  let := last_normal H h0 hs0 hs
  have hp := reduced_pair_polynomial H h0 h1 hs0 hs (polynomial_of_cube_mem H hf) t a b
  exact ⟨cube_mem_of_polynomial _ hp.1,hp.2⟩

end LeibmanSquare

end
end
end
end

end OAI
