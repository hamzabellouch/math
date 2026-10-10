import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients

def originPolynomial {v s : ℕ} (a : Grid v s→ℝ) (q : Fin v→ℕ) : ℝ[X] :=
  ∑ e, C (a e*∏ i, (q i:ℝ)^(e i).val)*X^(totalDegree e)

lemma originPolynomial_eval {v s : ℕ} (a : Grid v s→ℝ) (q : Fin v→ℕ) (z : ℤ) :
    (originPolynomial a q).eval (z:ℝ)=gridEval a (fun i => (z:ℝ)*(q i:ℝ)) := by
  classical
  simp only [originPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,gridEval]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_pow,Finset.prod_mul_distrib,totalDegree]
  rw [Finset.prod_pow_eq_pow_sum]
  ring

lemma originPolynomial_coeff {v s : ℕ} (a : Grid v s→ℝ) (q : Fin v→ℕ) (j : ℕ) :
    (originPolynomial a q).coeff j=
      ∑ e, (if totalDegree e=j then a e else 0)*∏ i, (q i:ℝ)^(e i).val := by
  classical
  simp only [originPolynomial,finsetSum_coeff,coeff_C_mul,coeff_X_pow]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

 

theorem lineCoefficient_origin {v s : ℕ} {f : (Fin v→ℤ)→ℝ}
    (hf : LinePolynomial v s f) (a : Grid v s→ℝ)
    (ha : ∀ x : Fin v→ℤ, gridEval a (fun i => (x i:ℝ))=f x)
    (q : Fin v→ℕ) (j : ℕ) :
    lineCoefficient (s:=s) f (fun i => (q i:ℤ)) j 0=
      ∑ e, (if totalDegree e=j then a e else 0)*∏ i, (q i:ℝ)^(e i).val := by
  obtain ⟨P,hP,he⟩ := hf 0 (fun i => (q i:ℤ))
  have hOP : originPolynomial a q=P := by
    apply Polynomial.eq_of_eval_nat_eq
    intro n
    rw [← Int.cast_natCast (R:=ℝ),originPolynomial_eval,he]
    have hha := ha (fun i => (0 : Fin v→ℤ) i+(n:ℤ)*(q i:ℤ))
    simpa only [Pi.zero_apply,zero_add,Int.cast_mul,Int.cast_natCast] using hha
  rw [lineCoefficient_eq 0 (fun i => (q i:ℤ)) P hP he,← hOP,originPolynomial_coeff]

lemma lineCoefficient_above {v s : ℕ} {f : (Fin v→ℤ)→ℝ}
    (hf : LinePolynomial v s f) (x q : Fin v→ℤ) {j : ℕ} (hj : s<j) :
    lineCoefficient (s:=s) f q j x=0 := by
  obtain ⟨P,hP,he⟩ := hf x q
  rw [lineCoefficient_eq x q P hP he]
  exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt hj)

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open TriangularLatticeRecovery

 

theorem dense_origin_multiplier (v s : ℕ) (ρ : ℝ) (hρ : 0<ρ) :
    ∃ C N₀ : ℕ, 0<C ∧ 0<N₀ ∧ ∃ ε₀ : ℝ, 0<ε₀ ∧
    ∀ N : ℕ, N₀≤N → ∀ H : ℕ, 0<H → ∀ A : ℝ, 0≤A → A/H≤ε₀ →
    ∀ f : (Fin v→ℤ)→ℝ, LinePolynomial v s f → ∀ q : Fin v→ℤ,
    ∀ S : Set (Fin v→ℕ),
      (∀ x∈S, ∀ j : ℕ, 0<j → circleNorm
        (lineCoefficient (s:=s) f q j (fun i => (x i:ℤ)))≤A/(H:ℝ)^j) →
      ρ*(N:ℝ)^v≤(BoxCounting.count v N S:ℝ) →
      ∃ r : ℕ, 0<r ∧ r≤C^(s+1) ∧ ∀ j : ℕ, 0<j →
        circleNorm ((r:ℝ)*lineCoefficient (s:=s) f q j 0)*(H:ℝ)^j≤(C:ℝ)^(s+2)*A := by
  classical
  obtain ⟨C,N₀,hC,hN₀,ε₀,hε₀,hinv⟩ := dense_line_constant v s ρ hρ
  refine ⟨C,N₀,hC,hN₀,ε₀,hε₀,?_⟩
  intro N hN H hH A hA hsmall f hf q S hgood hcount
  have hHR : 0<(H:ℝ) := Nat.cast_pos.mpr hH
  have hH1 : 1≤(H:ℝ) := by exact_mod_cast hH
  have hchoice (j : Fin (s+1)) : ∃ r : ℕ, 0<r ∧ r≤C ∧ (0<j.val →
      circleNorm ((r:ℝ)*lineCoefficient (s:=s) f q j.val 0)*(H:ℝ)^j.val≤(C:ℝ)*A) := by
    by_cases hj : 0<j.val
    · have hp : (H:ℝ)≤(H:ℝ)^j.val := by
        simpa only [pow_one] using pow_le_pow_right₀ hH1 hj
      have hes : A/(H:ℝ)^j.val≤ε₀ := (div_le_div_of_nonneg_left hA hHR hp).trans hsmall
      obtain ⟨r,hr,hrC,hrb⟩ := hinv N hN (A/(H:ℝ)^j.val) (by positivity) hes
        f hf q j.val S (fun x hx => hgood x hx j.val hj) hcount
      refine ⟨r,hr,hrC,fun _ => ?_⟩
      have hh := mul_le_mul_of_nonneg_right hrb (pow_nonneg hHR.le j.val)
      have heq : (C:ℝ)*(A/(H:ℝ)^j.val)*(H:ℝ)^j.val=(C:ℝ)*A := by
        field_simp
      rwa [heq] at hh
    · exact ⟨1,by omega,by omega,fun h => (hj h).elim⟩
  choose r hr hrC hrb using hchoice
  let R := ∏ j : Fin (s+1), r j
  have hR : 0<R := Finset.prod_pos (fun j _ => hr j)
  have hRC : R≤C^(s+1) := by
    calc
      R ≤ ∏ _ : Fin (s+1), C := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun j _ => hrC j)
      _ = _ := by simp
  refine ⟨R,hR,hRC,?_⟩
  intro j hj
  by_cases hjs : j ≤ s
  · let k : Fin (s+1) := ⟨j,Nat.lt_succ_of_le hjs⟩
    have hd : r k ∣ R := Finset.dvd_prod_of_mem r (Finset.mem_univ k)
    have heR : (R:ℝ)=((R/r k:ℕ):ℝ)*(r k:ℝ) := by exact_mod_cast (Nat.div_mul_cancel hd).symm
    rw [heR,mul_assoc]
    calc
      _ ≤ (((R/r k:ℕ):ℝ)*circleNorm ((r k:ℝ)*lineCoefficient (s:=s) f q j 0))*(H:ℝ)^j :=
        mul_le_mul_of_nonneg_right (circleNorm_nat_mul _ _) (pow_nonneg hHR.le _)
      _ = ((R/r k:ℕ):ℝ)*(circleNorm ((r k:ℝ)*lineCoefficient (s:=s) f q j 0)*(H:ℝ)^j) := by ring
      _ ≤ ((R/r k:ℕ):ℝ)*((C:ℝ)*A) := mul_le_mul_of_nonneg_left (hrb k hj) (Nat.cast_nonneg _)
      _ ≤ (C:ℝ)^(s+1)*((C:ℝ)*A) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hA)
        exact_mod_cast (Nat.div_le_self R (r k)).trans hRC
      _ = _ := by rw [← mul_assoc,← pow_succ]
  · rw [lineCoefficient_above hf 0 q (Nat.lt_of_not_ge hjs),mul_zero,circleNorm_zero,zero_mul]
    positivity

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialWeyl BoxPolynomialLines TriangularLatticeRecovery

lemma count_finset_image {v N : ℕ} (B : Finset (Fin v→Fin N)) :
    BoxCounting.count v N ((fun x : Fin v→Fin N => fun i => (x i).val) '' (B : Set (Fin v→Fin N)))=B.card := by
  classical
  unfold BoxCounting.count
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_image,Finset.mem_coe]
  constructor
  · rintro ⟨y,hy,he⟩
    have : y=x := by funext i; exact Fin.ext (congrFun he i)
    exact this ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

 

theorem dense_basepoint_characters {v s N H : ℕ} (hN : 0<N) (hH : 0<H)
    {α : Type*} (U : Finset α) (A δ : ℝ) (hδ : 0<δ)
    (F : (Fin v→ℕ)→ℂ) (hF : ∀ x, ‖F x‖≤1) (I : ℂ) (hI : ‖I‖≤1)
    (hdisc : δ≤‖boxMean v N F-I‖) (q : Fin v→ℕ)
    (hshort : 2*(H:ℝ)*(∑ i,q i:ℕ)/N≤δ/8)
    (a : α→(Fin v→ℤ)→ℝ)
    (hprod : ∀ x : Fin v→Fin N,
      δ/2≤‖mean H (fun z => F (fun i => (x i).val+z*q i))-I‖ →
      ∃ ξ∈U, ∀ j : ℕ, 0<j → circleNorm
        (lineCoefficient (s:=s) (a ξ) (fun i => (q i:ℤ)) j (fun i => ((x i).val:ℤ)))≤A/(H:ℝ)^j) :
    ∃ ξ∈U, ∃ S : Set (Fin v→ℕ),
      (δ/8)/((U.card:ℝ)+1)*(N:ℝ)^v≤(BoxCounting.count v N S:ℝ) ∧
      ∀ x∈S, ∀ j : ℕ, 0<j → circleNorm
        (lineCoefficient (s:=s) (a ξ) (fun i => (q i:ℤ)) j (fun i => (x i:ℤ)))≤A/(H:ℝ)^j := by
  classical
  let g : (Fin v→ℕ)→ℂ := fun x => (F x-I)/2
  have hg (x) : ‖g x‖≤1 := by
    dsimp [g]
    rw [norm_div]
    norm_num
    have hh := norm_sub_le (F x) I
    linarith [hF x]
  have heq : boxMean v N g=(boxMean v N F-I)/2 := by
    rw [BoxCounting.boxMean_eq_fin,BoxCounting.boxMean_eq_fin]
    simp only [g,← Finset.expect_div,Finset.expect_sub_distrib]
    have hn : (Finset.univ : Finset (Fin v→Fin N)).Nonempty := by
      let : NeZero N := ⟨ne_of_gt hN⟩
      exact Finset.univ_nonempty
    rw [Finset.expect_const hn]
  have hnorm : δ/2≤‖boxMean v N g‖ := by
    rw [heq,norm_div]
    norm_num
    linarith
  have hdense := dense_correlated_lines v hN hH g hg q (δ/2) (by positivity) hnorm (by linarith)
  let B := Finset.univ.filter (fun x : Fin v→Fin N => δ/4≤‖mean H (fun z => g (fun i => (x i).val+z*q i))‖)
  have hB : δ/8*(N:ℝ)^v≤(B.card:ℝ) := by
    simpa only [B,show δ/2/4=δ/8 by ring,show δ/2/2=δ/4 by ring] using hdense
  let P (x : Fin v→Fin N) (ξ : α) := ∀ j : ℕ, 0<j → circleNorm
    (lineCoefficient (s:=s) (a ξ) (fun i => (q i:ℤ)) j (fun i => ((x i).val:ℤ)))≤A/(H:ℝ)^j
  have hget (x) (hx : x∈B) : ∃ ξ∈U, P x ξ := by
    apply hprod x
    have hh := (Finset.mem_filter.mp hx).2
    have hem : mean H (fun z => g (fun i => (x i).val+z*q i))=
        (mean H (fun z => F (fun i => (x i).val+z*q i))-I)/2 := by
      simp only [mean,g,← Finset.expect_div,Finset.expect_sub_distrib]
      rw [Finset.expect_const (Finset.nonempty_range_iff.mpr (ne_of_gt hH))]
    rw [hem,norm_div] at hh
    norm_num at hh
    linarith
  obtain ⟨B',hB'B,hB'ne,hB'c,ξ,hξ,hξB⟩ := SquareInduction.finite_dense_choice_general U B
    (δ/8) ((N:ℝ)^v) (by positivity) (pow_pos (Nat.cast_pos.mpr hN) _) hB P hget
  refine ⟨ξ,hξ,(fun x : Fin v→Fin N => fun i => (x i).val) '' (B' : Set (Fin v→Fin N)),?_,?_⟩
  · rwa [count_finset_image]
  · rintro x ⟨y,hy,rfl⟩ j hj
    exact hξB y hy j hj

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace CorrectedBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction TriangularLatticeRecovery BoxPolynomialLines
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

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem box_line_data
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      (∀ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ ∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
      ∀ N M : ℕ, 0<N → 0<M → ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      ∀ F : C(G⧸Γ,ℂ), LipschitzWith 1 F → ‖F‖≤1 →
      δ≤‖boxMean v N (fun x => F (QuotientGroup.mk (f (fun i => (x i:ℤ)))))-(∫ y,F y ∂μ)‖ →
      ∀ z : Fin v→ℕ, 2*(M:ℝ)*(∑ i,z i:ℕ)/N≤δ/8 →
      ∃ ξ∈U, ∃ S : Set (Fin v→ℕ),
        (δ/8)/((U.card:ℝ)+1)*(N:ℝ)^v≤(BoxCounting.count v N S:ℝ) ∧
        ∀ x∈S, ∀ j : ℕ, 0<j → circleNorm
          (lineCoefficient (s:=s) (fun x => (ξ (f x)).toAdd) (fun i => (z i:ℤ)) j
            (fun i => (x i:ℤ)))≤A/(M:ℝ)^j := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,hA,hprod⟩ := degree_general_metric_producer c hsk H h0 h1 s hs
    q hqbound hq Γ hΓ htop μ (δ/2) (by positivity)
  let V := U.filter (fun ξ : G→*Multiplicative ℝ => ξ≠1 ∧ Continuous ξ ∧ ∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z)
  refine ⟨V,A,hA,fun ξ hξ => (Finset.mem_filter.mp hξ).2,?_⟩
  intro N M hN hM f hf F hFL hFn hd z hz
  have hFn' (x : Fin v→ℕ) : ‖F (QuotientGroup.mk (f (fun i => (x i:ℤ))))‖≤1 :=
    (F.norm_coe_le_norm _).trans hFn
  have hI : ‖∫ y,F y ∂μ‖≤1 := by
    apply le_trans _ hFn
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=μ)
      (Filter.Eventually.of_forall F.norm_coe_le_norm)
  apply dense_basepoint_characters hN hM V A δ hδ _ hFn' _ hI hd z hz
    (fun ξ x => (ξ (f x)).toAdd)
  intro x hx
  let g : ℤ→G := fun n => f (fun i => ((x i).val:ℤ)+n*(z i:ℤ))
  have hg := polynomial_integer_line H hf (fun i => ((x i).val:ℤ)) (fun i => (z i:ℤ))
  have hdisc : δ/2≤‖FourierObstruction.discrepancy μ M (fun k => QuotientGroup.mk (g k)) F‖ := by
    convert hx using 1
    simp only [FourierObstruction.discrepancy,g,Nat.cast_add,Nat.cast_mul]
    rfl
  obtain ⟨ξ,hξ,hξne,hξc,hξZ,P,hP,hPe,hPb⟩ := hprod M hM g hg ⟨F,hFL,hFn,hdisc⟩
  refine ⟨ξ,Finset.mem_filter.mpr ⟨hξ,hξne,hξc,hξZ⟩,?_⟩
  intro j hj
  rw [lineCoefficient_eq _ _ P hP hPe j]
  obtain ⟨k,hk⟩ := hPb j hj
  exact (DenseBoxModularPolynomial.circleNorm_le_integer_error _ k).trans hk

end CorrectedBoxLeibman

end
end
end
end
end

end OAI
