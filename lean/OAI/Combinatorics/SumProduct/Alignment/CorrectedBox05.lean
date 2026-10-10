import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients

lemma grid_totalDegree_bound {v s : ℕ} (e : Grid v s) : totalDegree e≤v*s := by
  calc
    _ ≤ ∑ _ : Fin v, s := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (e i).isLt)
    _ = _ := by simp

 

theorem grid_totalDegree {v s : ℕ} {f : (Fin v→ℤ)→ℝ}
    (hf : LinePolynomial v s f) (a : Grid v s→ℝ)
    (ha : ∀ x, gridEval a (fun i => (x i:ℝ))=f x) :
    ∀ e, s<totalDegree e → a e=0 := by
  classical
  let L := v*s+1
  have hL : 0<L := by dsimp [L]; omega
  have hD (e : Grid v s) : (gridExponent e).sum (fun _ k => k)≤v*s := by
    rw [gridExponent_degree]
    exact grid_totalDegree_bound e
  let Q := (Finset.univ : Finset (Fin v→Fin L))
  have hden : (v*s:ℕ)/(L:ℚ≥0)<(Q.card:ℚ≥0)/(L:ℚ≥0)^v := by
    have hLp : (0:ℚ≥0)<L := Nat.cast_pos.mpr hL
    have hpow : (L:ℚ≥0)^v≠0 := ne_of_gt (pow_pos hLp _)
    simp only [Q,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,div_self hpow]
    apply (div_lt_one hLp).mpr
    exact_mod_cast (show v*s<L by dsimp [L]; omega)
  obtain ⟨B,hB,w,hw⟩ := dense_grid_integer_weights gridExponent (gridExponent_injective v s)
    (v*s) hD L Q hden
  intro e he
  have hz (q : Q) : (∑ f : Grid v s, (if totalDegree f=totalDegree e then a f else 0)*
      (gridMonomial gridExponent q.val f:ℝ))=0 := by
    simp only [gridMonomial_eq_prod]
    rw [← lineCoefficient_origin hf a ha (fun i => (q.val i).val) (totalDegree e)]
    exact lineCoefficient_above hf 0 _ he
  have hrec := TriangularLatticeRecovery.reconstruct_slice totalDegree (fun q : Q => gridMonomial gridExponent q.val)
    w B hw a (totalDegree e) e rfl
  simp only [hz,mul_zero,Finset.sum_const_zero] at hrec
  exact (mul_eq_zero.mp hrec.symm).resolve_left (Nat.cast_ne_zero.mpr (ne_of_gt hB))

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction TriangularLatticeRecovery BoxPolynomialLines PolynomialLineCoefficients
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance correctedBox05MonomialTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem box_monomial_all_lengths
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ≤‖boxMean v N (fun x => F (QuotientGroup.mk (f (fun i => (x i:ℤ)))))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ a : Grid v s→ℝ, (∀ x, gridEval a (fun i => (x i:ℝ))=(ξ (f x)).toAdd) ∧
          (∀ e, s<totalDegree e → a e=0) ∧
          ∀ e, 0<totalDegree e → circleNorm (a e)*(N:ℝ)^(totalDegree e)≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := box_monomial_large c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v δ hδ
  let B := A+(N₀:ℝ)^(v*s)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨U,B,hB,?_⟩
  intro N hN f hf hd
  have hscalar (ξ : G→*Multiplicative ℝ) : LinePolynomial v s (fun x => (ξ (f x)).toAdd) := by
    intro x z
    exact character_polynomial H s hs (polynomial_integer_line H hf x z) ξ
  by_cases hlarge : N₀≤N
  · obtain ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hb⟩ := hprod N hlarge f hf hd
    refine ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,grid_totalDegree (hscalar ξ) a ha,?_⟩
    intro e he
    exact (hb e he).trans (by dsimp [B]; linarith [pow_nonneg (Nat.cast_nonneg N₀ : (0:ℝ)≤N₀) (v*s)])
  · obtain ⟨F,hFL,hFn,hdisc⟩ := hd
    let I := ∫ y,F y ∂μ
    have hd' : δ≤‖boxMean v N (fun x => F (QuotientGroup.mk (f (fun i => (x i:ℤ))))-I)‖ := by
      rw [boxMean_sub,boxMean_const v hN]
      exact hdisc
    obtain ⟨x,hx,hxd⟩ := exists_norm_ge v hN _ hd'
    let g : (Fin v→ℤ)→G := fun _ => f (fun i => (x i:ℤ))
    have hg : LeibmanSquare.Polynomial H 0 g := polynomial_of_cube_mem H (const_mem (by rw [h0]; trivial))
    have hgd : δ≤‖boxMean v N₀ (fun y => F (QuotientGroup.mk (g (fun i => (y i:ℤ)))))-I‖ := by
      dsimp [g]
      rw [boxMean_const v hN₀]
      exact hxd
    obtain ⟨ξ,hξ,hξne,hξc,hξΓ,_⟩ := hprod N₀ le_rfl g hg ⟨F,hFL,hFn,hgd⟩
    obtain ⟨a,ha⟩ := character_grid_expansion H s hs hf ξ
    refine ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,grid_totalDegree (hscalar ξ) a ha,?_⟩
    intro e he
    have hdeg := grid_totalDegree_bound e
    have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
    have hNN : (N:ℝ)≤N₀ := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))
    calc
      _ ≤ 1*(N:ℝ)^(totalDegree e) := mul_le_mul_of_nonneg_right
        (DenseBoxModularPolynomial.circleNorm_le_one _) (by positivity)
      _ ≤ (N₀:ℝ)^(v*s) := by
        rw [one_mul]
        exact (pow_le_pow_right₀ hNr hdeg).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hNN _)
      _ ≤ B := by dsimp [B]; linarith

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
namespace CorrectedBoxLeibman
open RationalFactorPeriods BinomialDifference

def chooseSequence : Polynomial.Sequence ℝ where
  elems' := choosePolynomial
  degree_eq' j := by
    rw [choosePolynomial,Polynomial.degree_C_mul (by positivity),
      Polynomial.degree_eq_natDegree (monic_descPochhammer ℝ j).ne_zero,
      descPochhammer_natDegree]

lemma newton_expansion (s : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ s) :
    P=∑ j : Fin (s+1), (coefficient ℝ j.val P) • choosePolynomial j.val := by
  classical
  have hr : Set.range (fun j : Fin (s+1) => choosePolynomial j.val)=
      chooseSequence '' Set.Iio (s+1) := by
    ext Q
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  have hmem : P∈Submodule.span ℝ (Set.range (fun j : Fin (s+1) => choosePolynomial j.val)) := by
    rw [hr,chooseSequence.span_degreeLT (fun i _ => isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr (chooseSequence.ne_zero i))),Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (Nat.lt_succ_of_le hP))
  obtain ⟨b,hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hc (k : Fin (s+1)) : coefficient ℝ k.val P=b k := by
    rw [← hb,map_sum]
    simp only [map_smul,smul_eq_mul,coefficient_choose,Fin.val_inj,mul_ite,mul_one,mul_zero]
    simp
  simpa only [hc] using hb.symm

lemma power_binomial_expansion {s : ℕ} (j : Fin (s+1)) (x : ℤ) :
    (x:ℝ)^j.val=∑ i : Fin (s+1), (matrix i.val j.val:ℝ)*(Ring.choose x i.val:ℤ) := by
  have he := congrArg (fun P : ℝ[X] => P.eval (x:ℝ))
    (newton_expansion s (X^j.val) (by simpa using Nat.le_of_lt_succ j.isLt))
  simpa only [eval_pow,eval_X,eval_finsetSum,eval_smul,smul_eq_mul,
    coefficient_X_pow,choosePolynomial_int] using he

 

def tensorMatrix {v s : ℕ} (I J : Grid v s) : ℤ :=
  ∏ i, matrix (I i).val (J i).val

def tensorNewton {v s : ℕ} (a : Grid v s→ℝ) (I : Grid v s) : ℝ :=
  ∑ J, a J*(tensorMatrix I J:ℝ)

def binomialGridEval {v s : ℕ} (α : Grid v s→ℝ) (x : Fin v→ℤ) : ℝ :=
  ∑ I, α I*∏ i, (Ring.choose (x i) (I i).val:ℤ)

lemma tensor_newton_expansion {v s : ℕ} (a : Grid v s→ℝ) (x : Fin v→ℤ) :
    gridEval a (fun i => (x i:ℝ))=binomialGridEval (tensorNewton a) x := by
  classical
  simp only [gridEval,binomialGridEval]
  simp_rw [power_binomial_expansion,Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp only [tensorNewton,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.prod_mul_distrib]
  simp only [tensorMatrix,Int.cast_prod]
  ring

lemma tensorMatrix_low {v s : ℕ} (I J : Grid v s)
    (h : ∃ i, (J i).val<(I i).val) : tensorMatrix I J=0 := by
  obtain ⟨i,hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (matrix_low _ _ hi)

lemma tensorMatrix_degree {v s : ℕ} (I J : Grid v s)
    (h : tensorMatrix I J≠0) : PolynomialLineCoefficients.totalDegree I ≤
      PolynomialLineCoefficients.totalDegree J := by
  apply Finset.sum_le_sum
  intro i _
  by_contra hh
  exact h (tensorMatrix_low I J ⟨i,by omega⟩)

lemma tensorNewton_totalDegree {v s : ℕ} (a : Grid v s→ℝ)
    (ha : ∀ J, s<PolynomialLineCoefficients.totalDegree J → a J=0) :
    ∀ I, s<PolynomialLineCoefficients.totalDegree I → tensorNewton a I=0 := by
  intro I hI
  apply Finset.sum_eq_zero
  intro J _
  by_cases hmat : tensorMatrix I J=0
  · simp [hmat]
  · rw [ha J (lt_of_lt_of_le hI (tensorMatrix_degree I J hmat)),zero_mul]

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients TriangularLatticeRecovery

def tensorConversionBound (v s : ℕ) : ℝ :=
  1+∑ I : Grid v s, ∑ J : Grid v s, |(tensorMatrix I J:ℝ)|

lemma tensorConversionBound_pos (v s : ℕ) : 0<tensorConversionBound v s := by
  have h : 0≤∑ I : Grid v s, ∑ J : Grid v s, |(tensorMatrix I J:ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  unfold tensorConversionBound
  linarith

lemma tensor_row_bound {v s : ℕ} (I : Grid v s) :
    (∑ J : Grid v s, |(tensorMatrix I J:ℝ)|)≤tensorConversionBound v s := by
  have hh := Finset.single_le_sum (f := fun I : Grid v s => ∑ J : Grid v s, |(tensorMatrix I J:ℝ)|)
    (fun I _ => Finset.sum_nonneg (fun J _ => abs_nonneg _)) (Finset.mem_univ I)
  unfold tensorConversionBound
  linarith

 

lemma tensorNewton_bound {v s : ℕ} (a : Grid v s→ℝ) (N A : ℝ)
    (hN : 1≤N) (hA : 0≤A)
    (ha : ∀ J, 0<totalDegree J → circleNorm (a J)*N^(totalDegree J)≤A)
    (I : Grid v s) (hI : 0<totalDegree I) :
    circleNorm (tensorNewton a I)*N^(totalDegree I)≤tensorConversionBound v s*A := by
  classical
  have hN0 : 0≤N := le_trans zero_le_one hN
  have hb (J : Grid v s) : |(tensorMatrix I J:ℝ)| *(circleNorm (a J)*N^(totalDegree I))≤
      |(tensorMatrix I J:ℝ)| *A := by
    by_cases hm : tensorMatrix I J=0
    · simp [hm]
    · have hd := tensorMatrix_degree I J hm
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hd)
        (norm_nonneg _)).trans (ha J (hI.trans_le hd))
  have he : tensorNewton a I=∑ J : Grid v s, (tensorMatrix I J:ℝ)*a J := by
    simp only [tensorNewton,mul_comm]
  rw [he]
  calc
    _ ≤ (∑ J : Grid v s, |(tensorMatrix I J:ℝ)| *circleNorm (a J))*N^(totalDegree I) :=
      mul_le_mul_of_nonneg_right (integer_linear_bound _ _ _) (pow_nonneg hN0 _)
    _ = ∑ J : Grid v s, |(tensorMatrix I J:ℝ)| *(circleNorm (a J)*N^(totalDegree I)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro J _
      ring
    _ ≤ ∑ J : Grid v s, |(tensorMatrix I J:ℝ)| *A := Finset.sum_le_sum (fun J _ => hb J)
    _ = (∑ J : Grid v s, |(tensorMatrix I J:ℝ)|)*A := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (tensor_row_bound I) hA

end CorrectedBoxLeibman

end
end
end
end
end

end OAI
