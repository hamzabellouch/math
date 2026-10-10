import OAI.NumberTheory.DukePrimeDegree.Entropy.AdaptiveFutureLifts
import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRadius

namespace OAI

/-! # Exponentially shrinking radial cells give triangular future lifts -/

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma LocalInjectivityAt.injOn {n : ℕ} {r : ℝ} {x : X n}
    (h : LocalInjectivityAt r x) :
    Set.InjOn (fun g => rightAction x g) (matrixBall n r) := by
  obtain ⟨U,_,hx,hi⟩ := h
  exact hi x hx

/-- The chosen lift remains in the height-dependent small matrix ball at
every future time; the same radius is an injectivity radius at each point. -/
theorem exists_radial_radius_small_conjugate_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) (R : ℝ) (hR : 0 < R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ r₀ ≤ R ∧
      (∀ x, Set.InjOn (fun g => rightAction x g)
        (matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))))) ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g=y ∧ (∀ i j, ell j < ell i → g.val i j=0) ∧
          ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
            diagonalOneParameter ell hell (-(k:ℝ)) ∈
            matrixBall n (r₀*Real.exp (-(4*B)*
              (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ))) := by
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun x => rightAction x a
  have hneg : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion (fun i => -ell i) hneg
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hparam : diagonalOneParameter (fun i => -ell i) hneg (-1) = a⁻¹ := by
    calc
      _ = diagonalOneParameter ell hell 1 := by
        simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
      _ = _ := by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv]
  have hex (s : ℝ) (hs : 0 < s) :
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s) :=
    hparam ▸ hexpand s hs
  obtain ⟨b,hb,hinj⟩ := exists_uniform_logarithmic_injectivity_radius hn
  let c := b/(2*(n:ℝ)*Real.exp (2*(B+matrixLogLength a+1)))
  have hc : 0 < c := by dsimp [c]; positivity
  let r₀ := min R (min 1 (c/L))
  have hr₀ : 0 < r₀ := lt_min hR (lt_min zero_lt_one (div_pos hc hLp))
  have hLr₀ : L*r₀ ≤ c := by
    have hh := (le_div_iff₀ hLp).mp ((min_le_right R (min 1 (c/L))).trans (min_le_right 1 (c/L)))
    simpa only [mul_comm] using hh
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  have hr (m : ℕ) : 0 < r m := mul_pos hr₀ (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    have he : Real.exp (-(4*B)*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg m)])
    exact (mul_le_of_le_one_right hr₀.le he).trans ((min_le_right R (min 1 (c/L))).trans (min_le_left 1 (c/L)))
  have hrad (m : ℕ) : L*r m ≤
      b/(2*(n:ℝ)*Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1))) := by
    have he : Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1)) =
        Real.exp (2*(B+matrixLogLength a+1))*Real.exp ((4*B)*(m:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have heq : c*Real.exp (-(4*B)*(m:ℝ)) =
        b/(2*(n:ℝ)*Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1))) := by
      rw [he,neg_mul,Real.exp_neg]
      dsimp [c]
      field_simp
    rw [←heq]
    dsimp [r]
    nlinarith [Real.exp_pos (-(4*B)*(m:ℝ))]
  have hi (x : X n) : LocalInjectivityAt (L*r (H x)) x := by
    apply (hinj (2*B*(H x:ℝ)+B+matrixLogLength a) x ?_).mono (hrad (H x))
    exact (hheight x).trans (by linarith [matrixLogLength_nonneg a])
  have hnext (x : X n) : LocalInjectivityAt (L*r (H x)) (T x) := by
    apply (hinj (2*B*(H x:ℝ)+B+matrixLogLength a) (T x) ?_).mono (hrad (H x))
    have hh := (abs_le.mp (quotientLogDistance_right_bound
      (Quotient.mk _ (1 : G n)) x a)).2
    change quotientLogDistance (Quotient.mk _ (1 : G n)) (T x)-
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ matrixLogLength a at hh
    linarith [hheight x]
  have hirad (x : X n) : Set.InjOn (fun g => rightAction x g)
      (matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ)))) :=
    (hi x).injOn.mono (matrixBall_mono (le_mul_of_one_le_left (hr _).le hL))
  refine ⟨r₀,hr₀,(min_le_right _ _).trans (min_le_left _ _),min_le_left _ _,hirad,?_⟩
  intro Q hsmall x y hxy
  let s := fun k : ℕ => r (H (T^[k] x))
  choose g hg hlift using fun k => hsmall (T^[k] x) (T^[k] y) (hxy k)
  have hconj := variable_future_lifts_conjugate a x y L s (fun k => hr _) hex
    (fun k => ?_) (fun k => ?_) g hg hlift
  · have he (k : ℕ) : diagonalOneParameter ell hell (k:ℝ) * g 0 *
        diagonalOneParameter ell hell (-(k:ℝ)) = g k := by
      have hp : a^k = diagonalOneParameter ell hell (-(k:ℝ)) := by
        dsimp [a]
        rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
      calc
        _ = (MulAut.conj a⁻¹)^[k] (g 0) := by
          rw [conjugation_iterate,hp,←diagonalOneParameter_neg,neg_neg]
        _ = g k := (hconj k).symm
    refine ⟨g 0,?_,by simpa only [Function.iterate_zero,Function.id_def] using hlift 0,?_,?_⟩
    · simpa only [s, r, Function.iterate_zero, Function.id_def] using hg 0
    · intro i j hij
      apply conjugation_expanding_entry_eq_zero ell hell (g 0)
        tendsto_natCast_atTop_atTop 2 _ hij
      apply Eventually.of_forall
      intro k p q
      rw [he k]
      have hh := hg k p q
      change |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q| < s k at hh
      have hone : |(1 : Matrix (Fin n) (Fin n) ℝ) p q| ≤ 1 := by
        simp only [Matrix.one_apply]
        split_ifs <;> norm_num
      have ht := abs_add_le ((g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q)
        ((1 : Matrix (Fin n) (Fin n) ℝ) p q)
      rw [sub_add_cancel] at ht
      have hs : s k ≤ 1 := hr1 _
      linarith
    · intro k
      rw [he k]
      exact hg k
  · exact (hi (T^[k] x)).injOn.mono (matrixBall_mono
      (le_mul_of_one_le_left (hr _).le hL))
  · simpa only [Function.iterate_succ_apply'] using (hnext (T^[k] x)).injOn

/-- Future fibers admit small triangular lifts. -/
theorem exists_radial_radius_small_triangular_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) (R : ℝ) (hR : 0 < R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ r₀ ≤ R ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  obtain ⟨r,hr,hr1,hrR,_,h⟩ := exists_radial_radius_small_conjugate_lifts
    hn ell hell B hB H hheight R hR
  refine ⟨r,hr,hr1,hrR,?_⟩
  intro Q hQ x y hxy
  obtain ⟨g,hg,hgx,hgt,_⟩ := h Q hQ x y hxy
  exact ⟨g,hg,hgx,hgt⟩


/-- Future fibers admit triangular lifts. -/
theorem exists_radial_radius_triangular_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G n, rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  obtain ⟨r,hr,hr1,_,h⟩ := exists_radial_radius_small_triangular_lifts
    hn ell hell B hB H hheight 1 zero_lt_one
  refine ⟨r,hr,hr1,?_⟩
  intro Q hQ x y hxy
  obtain ⟨g,_,hg⟩ := h Q hQ x y hxy
  exact ⟨g,hg⟩

end DukePrimeDegree

end

end OAI
