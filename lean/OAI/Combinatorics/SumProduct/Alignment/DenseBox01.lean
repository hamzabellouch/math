import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BoxPolynomial01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace DenseBoxComplete
open scoped BigOperators
open Finset PolynomialLineCoefficients TriangularLatticeRecovery DenseBoxModularPolynomial
noncomputable section

lemma degree_eq_zero {n d : ℕ} (e : Grid n d) : totalDegree e = 0 ↔ e = 0 := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have hh := Finset.single_le_sum (f := fun i => (e i).val)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    change _ ≤ totalDegree e at hh
    simpa [h] using hh
  · rintro rfl
    simp [totalDegree]

lemma monomial_bound {n d N : ℕ} (e : Grid n d) (x : Fin n → ℕ)
    (hx : ∀ i, x i ≤ N) : (∏ i, (x i : ℝ)^(e i).val) ≤ (N:ℝ)^totalDegree e := by
  rw [totalDegree,← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (Nat.cast_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (hx i)) _)

lemma constant_coefficient {n d N q : ℕ} (a : Grid n d → ℝ) (x : Fin n → ℕ)
    (hx : ∀ i, x i ≤ N) (ε A : ℝ) (hA : 0 ≤ A) (hnear : circleNorm (eval a x) ≤ ε)
    (hcoeff : ∀ e : Grid n d, 0 < totalDegree e →
      circleNorm ((q:ℝ)*a e)*(N:ℝ)^totalDegree e ≤ A) :
    circleNorm ((q:ℝ)*a 0) ≤ (q:ℝ)*ε + (Fintype.card (Grid n d):ℝ)*A := by
  classical
  let b : Grid n d → ℝ := fun e => (q:ℝ)*a e
  let S := (Finset.univ : Finset (Grid n d)).erase 0
  have heval : eval b x = (q:ℝ)*eval a x := by
    simp only [DenseBoxModularPolynomial.eval,b,Finset.mul_sum,mul_assoc]
  have heq : b 0 = eval b x - ∑ e ∈ S, b e * ∏ i, (x i:ℝ)^(e i).val := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Grid n d)))
      (fun e => b e*∏ i, (x i:ℝ)^(e i).val) (Finset.mem_univ (0:Grid n d))
    simp only [Pi.zero_apply,Fin.val_zero,pow_zero,Finset.prod_const_one,mul_one] at h
    change (∑ e ∈ S, b e*∏ i, (x i:ℝ)^(e i).val) + b 0 = eval b x at h
    linarith only [h]
  have hsum : circleNorm (∑ e ∈ S, b e*∏ i, (x i:ℝ)^(e i).val) ≤
      (S.card:ℝ)*A := by
    apply (circleNorm_sum_le S _).trans
    calc
      _ ≤ ∑ _e ∈ S, A := by
        apply Finset.sum_le_sum
        intro e he
        have hepos : 0 < totalDegree e := Nat.pos_of_ne_zero (mt (degree_eq_zero e).mp
          (Finset.mem_erase.mp he).1)
        have hc := circleNorm_nat_mul (∏ i, x i^(e i).val) (b e)
        simp only [Nat.cast_prod,Nat.cast_pow] at hc
        rw [mul_comm (b e)]
        exact hc.trans ((mul_le_mul_of_nonneg_right (monomial_bound e x hx)
          (circleNorm_nonneg _)).trans (by simpa only [b, mul_comm] using hcoeff e hepos))
      _ = _ := by simp
  have hsum' : circleNorm (∑ e ∈ S, b e*∏ i, (x i:ℝ)^(e i).val) ≤
      (Fintype.card (Grid n d):ℝ)*A :=
    hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast S.card_le_univ) hA)
  change circleNorm (b 0) ≤ _
  rw [heq]
  calc
    _ ≤ circleNorm (eval b x) + circleNorm (∑ e ∈ S, b e*∏ i, (x i:ℝ)^(e i).val) :=
      circleNorm_sub_le _ _
    _ ≤ (q:ℝ)*ε + (Fintype.card (Grid n d):ℝ)*A := by
      apply add_le_add _ hsum'
      rw [heval]
      exact (circleNorm_nat_mul q _).trans (mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg _))

 

theorem lattice_inverse_all (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C N₀ : ℕ, 0 < C ∧ 0 < N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ S : Set (Fin n → ℕ), ∀ a : Grid n d → ℝ,
        (∀ x ∈ S, ∃ z : ℤ, |eval a x-z| ≤ ε) →
        δ*(N:ℝ)^n ≤ (BoxCounting.count n N S:ℝ) →
        ∃ q : ℕ, 0 < q ∧ q ≤ C ∧ ∀ e : Grid n d,
          circleNorm ((q:ℝ)*a e)*(N:ℝ)^totalDegree e ≤ (C:ℝ)*ε := by
  classical
  obtain ⟨C,N₀,hC,hN₀,ε₀,hε₀,h⟩ := lattice_inverse_cardinal n d δ hδ
  let C' := C*(1+Fintype.card (Grid n d))
  have hCC' : C ≤ C' := by
    dsimp [C']
    simpa only [mul_one] using Nat.mul_le_mul_left C
      (Nat.le_add_right 1 (Fintype.card (Grid n d)))
  refine ⟨C',N₀,hC.trans_le hCC',hN₀,ε₀,hε₀,?_⟩
  intro N hN ε hε hεsmall S a hgood hcount
  obtain ⟨q,hq,hqC,hqa⟩ := h N hN ε hε hεsmall S a hgood hcount
  have hcountpos : 0 < BoxCounting.count n N S := by
    exact_mod_cast (lt_of_lt_of_le (mul_pos hδ (pow_pos
      (Nat.cast_pos.mpr (hN₀.trans_le hN)) _)) hcount)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hcountpos
  change x ∈ (univ.filter (fun x : Fin n → Fin N => (fun i => (x i).val) ∈ S)) at hx
  obtain ⟨z,hz⟩ := hgood (fun i => (x i).val) (Finset.mem_filter.mp hx).2
  have hnear := (circleNorm_le_integer_error (eval a (fun i => (x i).val)) z).trans hz
  have hc := constant_coefficient a (fun i => (x i).val) (fun i => (x i).isLt.le)
    ε ((C:ℝ)*ε) (by positivity) hnear hqa
  refine ⟨q,hq,hqC.trans hCC',?_⟩
  intro e
  by_cases he : e = 0
  · subst e
    simp only [(degree_eq_zero (0:Grid n d)).mpr rfl,pow_zero,mul_one]
    calc
      _ ≤ (q:ℝ)*ε + (Fintype.card (Grid n d):ℝ)*((C:ℝ)*ε) := hc
      _ ≤ (C:ℝ)*ε + (Fintype.card (Grid n d):ℝ)*((C:ℝ)*ε) := by gcongr
      _ = (C':ℝ)*ε := by dsimp [C']; push_cast; ring
  · exact (hqa e (Nat.pos_of_ne_zero (mt (degree_eq_zero e).mp he))).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCC') hε)

end
end DenseBoxComplete
end
 

 
section
noncomputable section
namespace SquareInduction
 
theorem finite_dense_choice_general {α β : Type*} (U : Finset α) (S : Finset β)
    (ρ T : ℝ) (hρ : 0<ρ) (hT : 0<T) (hS : ρ*T ≤ (S.card:ℝ))
    (P : β→α→Prop) (hget : ∀ h∈S, ∃ a∈U, P h a) :
    ∃ B : Finset β, B⊆S ∧ B.Nonempty ∧ ρ/((U.card:ℝ)+1)*T ≤ (B.card:ℝ) ∧
      ∃ a∈U, ∀ h∈B, P h a := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos hρ hT).trans_le hS)
  obtain ⟨h₀,hh₀⟩ := hSne
  obtain ⟨a₀,ha₀,_⟩ := hget h₀ hh₀
  choose a ha hPa using hget
  let f : β→α := fun h => if hh : h∈S then a h hh else a₀
  have hmap : ∀ h∈S, f h∈U := by
    intro h hh
    simpa only [f,dite_eq_left hh] using ha h hh
  have hcard : U.card • (ρ/((U.card:ℝ)+1)*T) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul]
    have hu : (U.card:ℝ)/((U.card:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    calc
      _ = ((U.card:ℝ)/((U.card:ℝ)+1))*(ρ*T) := by ring
      _ ≤ 1*(ρ*T) := mul_le_mul_of_nonneg_right hu (mul_pos hρ hT).le
      _ ≤ _ := by simpa only [one_mul] using hS
  obtain ⟨a',ha',hfiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap ⟨a₀,ha₀⟩ hcard
  let B := S.filter (fun h => f h=a')
  refine ⟨B,Finset.filter_subset _ _,?_,hfiber,a',ha',?_⟩
  · apply Finset.card_pos.mp
    have hp : 0<ρ/((U.card:ℝ)+1)*T := by positivity
    exact_mod_cast hp.trans_le hfiber
  · intro h hh
    have hhS := (Finset.mem_filter.mp hh).1
    have he : a h hhS=a' := by simpa only [f,dite_eq_left hhS] using (Finset.mem_filter.mp hh).2
    exact he ▸ hPa h hhS

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialWeyl BoxPolynomialLines
 

lemma dense_large_values {α : Type*} [Fintype α] [Nonempty α]
    (f : α→ℂ) (hf : ∀ x, ‖f x‖≤1) (δ : ℝ) (hδ : 0<δ)
    (hm : 3*δ/4 ≤ ‖𝔼 x : α, f x‖) :
    δ/4*(Fintype.card α:ℝ) ≤
      ((Finset.univ.filter (fun x => δ/2≤‖f x‖)).card:ℝ) := by
  classical
  let S := Finset.univ.filter (fun x => δ/2≤‖f x‖)
  have hsum : (∑ x : α, ‖f x‖) ≤ (Fintype.card α:ℝ)*(δ/2)+(S.card:ℝ) := by
    calc
      _ ≤ ∑ x : α, (δ/2+(if x∈S then (1:ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x∈S
        · rw [ite_eq_left hx]; linarith [hf x]
        · rw [ite_eq_right hx]; have hn : ¬δ/2≤‖f x‖ := by simpa [S] using hx
          linarith
      _ = _ := by simp [Finset.sum_add_distrib,S,Finset.sum_boole]
  have hnorm := hm.trans (RCLike.norm_expect_le (K:=ℂ) (s:=Finset.univ) (f:=f))
  rw [Finset.expect_eq_sum_div_card,Finset.card_univ] at hnorm
  have hc : 0<(Fintype.card α:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hlow := (le_div_iff₀ hc).mp hnorm
  change δ/4*(Fintype.card α:ℝ) ≤ (S.card:ℝ)
  nlinarith only [hsum,hlow]

 

theorem dense_correlated_lines (v : ℕ) {N H : ℕ} (hN : 0<N) (hH : 0<H)
    (f : (Fin v→ℕ)→ℂ) (hf : ∀ x, ‖f x‖≤1) (q : Fin v→ℕ)
    (δ : ℝ) (hδ : 0<δ) (hdisc : δ≤‖boxMean v N f‖)
    (hshort : 2*(H:ℝ)*(∑ i, q i:ℕ)/N ≤ δ/4) :
    δ/4*(N:ℝ)^v ≤
      ((Finset.univ.filter (fun x : Fin v→Fin N =>
        δ/2≤‖mean H (fun z => f (fun i => (x i).val+z*q i))‖)).card:ℝ) := by
  classical
  let : NeZero N := ⟨ne_of_gt hN⟩
  let F (x : Fin v→Fin N) := mean H (fun z => f (fun i => (x i).val+z*q i))
  have hF (x) : ‖F x‖≤1 := by
    apply (RCLike.norm_expect_le (K:=ℂ)).trans
    exact Finset.expect_le (Finset.nonempty_range_iff.mpr (ne_of_gt hH)) (fun z _ => hf _)
  have her := (line_average_error v hN hH f hf q).trans hshort
  rw [BoxCounting.boxMean_eq_fin] at her
  have htri := norm_sub_le_norm_sub_add_norm_sub (boxMean v N f) (𝔼 x : Fin v→Fin N, F x) 0
  simp only [sub_zero] at htri
  rw [norm_sub_rev] at her
  have hav : 3*δ/4 ≤ ‖𝔼 x : Fin v→Fin N, F x‖ := by
    change ‖boxMean v N f-(𝔼 x : Fin v→Fin N, F x)‖≤δ/4 at her
    linarith only [htri,her,hdisc]
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
    dense_large_values F hF δ hδ hav

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
namespace LeibmanSquare
open CubeFaces
variable {A B G : Type*} [AddCommGroup A] [AddCommGroup B] [Group G]
 

lemma iterDiff_affine (φ : A→+B) (x : B) (hs : List A) (f : B→G) :
    iterDiff hs (fun z => f (x+φ z)) = fun z => iterDiff (hs.map φ) f (x+φ z) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    change iterDiff hs (diff h (fun z => f (x+φ z))) = _
    have he : diff h (fun z => f (x+φ z)) = fun z => diff (φ h) f (x+φ z) := by
      funext z
      simp only [diff,map_add]
      rw [add_assoc]
    rw [he,ih]
    rfl

lemma polynomial_affine (H : Filtration G) {k : ℕ} {f : B→G}
    (hf : Polynomial H k f) (φ : A→+B) (x : B) :
    Polynomial H k (fun z => f (x+φ z)) := by
  intro hs z
  rw [iterDiff_affine]
  simpa only [List.length_map] using hf (hs.map φ) (x+φ z)

 
def integerDirection {v : ℕ} (q : Fin v→ℤ) : ℤ→+(Fin v→ℤ) where
  toFun z := fun i => z*q i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp [add_mul]

lemma polynomial_integer_line (H : Filtration G) {v k : ℕ} {f : (Fin v→ℤ)→G}
    (hf : Polynomial H k f) (x q : Fin v→ℤ) :
    Polynomial H k (fun z => f (fun i => x i+z*q i)) :=
  polynomial_affine H hf (integerDirection q) x

end LeibmanSquare

end
end
end
end
end

end OAI
