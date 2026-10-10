import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ComparableBox01
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
open _root_.Polynomial _root_.OAI.Polynomial
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients TriangularLatticeRecovery

def translationEntry (b : ℤ) (i j : ℕ) : ℤ := ((X+C b)^j : ℤ[X]).coeff i

def translationMatrix {v s : ℕ} (b : Fin v→ℤ) (I J : Grid v s) : ℤ :=
  ∏ k, translationEntry (b k) (I k).val (J k).val

def gridTranslate {v s : ℕ} (a : Grid v s→ℝ) (b : Fin v→ℤ) (I : Grid v s) : ℝ :=
  ∑ J, a J*(translationMatrix b I J:ℝ)

lemma translationEntry_low {b : ℤ} {i j : ℕ} (h : j < i) : translationEntry b i j=0 := by
  simp only [translationEntry,coeff_X_add_C_pow,Nat.choose_eq_zero_of_lt h,Nat.cast_zero,mul_zero]

lemma translationEntry_eval (s : ℕ) (j : Fin (s+1)) (b : ℤ) (x : ℝ) :
    (x+(b:ℝ))^j.val=∑ i : Fin (s+1), (translationEntry b i.val j.val:ℝ)*x^i.val := by
  have hd : ((X+C (b:ℝ))^j.val : ℝ[X]).natDegree ≤ s := by
    have hx : (X+C (b:ℝ) : ℝ[X]).natDegree≤1 := natDegree_add_le_of_degree_le
      (by simp) (by simp)
    exact (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hx)).trans (by simpa using Nat.le_of_lt_succ j.isLt)
  have he := Polynomial.eval_eq_sum_range' (p:=((X+C (b:ℝ))^j.val : ℝ[X])) (Nat.lt_succ_of_le hd) (x:=x)
  simp only [eval_pow,eval_add,eval_X,eval_C] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  simpa only [translationEntry,coeff_X_add_C_pow,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using he

lemma gridTranslate_eval {v s : ℕ} (a : Grid v s→ℝ) (b : Fin v→ℤ) (x : Fin v→ℝ) :
    gridEval (gridTranslate a b) x=gridEval a (fun i => x i+(b i:ℝ)) := by
  classical
  symm
  simp only [gridEval]
  simp_rw [translationEntry_eval s,Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp only [gridTranslate,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.prod_mul_distrib]
  simp only [translationMatrix,Int.cast_prod]
  ring

lemma translationMatrix_le {v s : ℕ} (b : Fin v→ℤ) (I J : Grid v s)
    (h : translationMatrix b I J≠0) : ∀ i,(I i).val≤(J i).val := by
  intro i
  by_contra hi
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) (translationEntry_low (by omega)))

lemma gridTranslate_totalDegree {v s : ℕ} (a : Grid v s→ℝ) (b : Fin v→ℤ)
    (ha : ∀ J,s<totalDegree J → a J=0) :
    ∀ I,s<totalDegree I → gridTranslate a b I=0 := by
  intro I hI
  apply Finset.sum_eq_zero
  intro J _
  by_cases hm : translationMatrix b I J=0
  · simp [hm]
  · have hd : totalDegree I≤totalDegree J := Finset.sum_le_sum (fun i _ => translationMatrix_le b I J hm i)
    rw [ha J (hI.trans_le hd),zero_mul]

lemma translationEntry_bound {s : ℕ} (i j : Fin (s+1)) (b : ℤ) (Z C : ℝ)
    (hZ : 0≤Z) (hC : 1≤C) (hb : |(b:ℝ)|≤C*Z) :
    |(translationEntry b i.val j.val:ℝ)| * Z^i.val≤(2^s*C^s)*Z^j.val := by
  by_cases hij : i.val≤j.val
  · have hchoose : (j.val.choose i.val:ℝ)≤(2:ℝ)^s := by
      exact_mod_cast ((Nat.choose_le_two_pow j.val i.val).trans (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ j.isLt)))
    have hd : j.val-i.val+i.val=j.val := Nat.sub_add_cancel hij
    have hdle : j.val-i.val ≤ s := (Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt)
    simp only [translationEntry,coeff_X_add_C_pow,Int.cast_mul,Int.cast_pow,Int.cast_natCast,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg (j.val.choose i.val) : (0:ℝ)≤(j.val.choose i.val:ℝ))]
    calc
      _ ≤ ((C*Z)^(j.val-i.val)*2^s)*Z^i.val := by gcongr
      _ = (2^s*C^(j.val-i.val))*Z^j.val := by
        have hp : Z^(j.val-i.val)*Z^i.val=Z^j.val := by rw [← pow_add,hd]
        rw [mul_pow]
        calc
          _ = (2^s*C^(j.val-i.val))*(Z^(j.val-i.val)*Z^i.val) := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by gcongr
  · rw [translationEntry_low (by omega)]
    simp only [Int.cast_zero,abs_zero,zero_mul]
    positivity

lemma translationMatrix_bound {v s : ℕ} (b : Fin v→ℤ) (I J : Grid v s) (Z C : ℝ)
    (hZ : 0≤Z) (hC : 1≤C) (hb : ∀ i, |(b i:ℝ)|≤C*Z) :
    |(translationMatrix b I J:ℝ)| * Z^(totalDegree I)≤(2^s*C^s)^v*Z^(totalDegree J) := by
  have hh := Finset.prod_le_prod₀ (fun i (_ : i∈(Finset.univ : Finset (Fin v))) =>
    mul_nonneg (abs_nonneg (translationEntry (b i) (I i).val (J i).val:ℝ)) (pow_nonneg hZ _))
    (fun i _ => translationEntry_bound (I i) (J i) (b i) Z C hZ hC (hb i))
  simpa only [Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum,translationMatrix,
    Int.cast_prod,Finset.abs_prod,totalDegree,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using hh

 

lemma gridTranslate_bound {v s : ℕ} (a : Grid v s→ℝ) (b : Fin v→ℤ) (Z C A : ℝ)
    (hZ : 0≤Z) (hC : 1≤C) (hA : 0≤A) (hb : ∀ i, |(b i:ℝ)|≤C*Z)
    (ha : ∀ J,0<totalDegree J → circleNorm (a J)*Z^(totalDegree J)≤A)
    (I : Grid v s) (hI : 0<totalDegree I) :
    circleNorm (gridTranslate a b I)*Z^(totalDegree I)≤
      ((s+1:ℕ)^v:ℝ)*(2^s*C^s)^v*A := by
  classical
  have hterm (J : Grid v s) : |(translationMatrix b I J:ℝ)| * circleNorm (a J)*Z^(totalDegree I)≤
      (2^s*C^s)^v*A := by
    by_cases hm : translationMatrix b I J=0
    · simp only [hm,Int.cast_zero,abs_zero,zero_mul]
      positivity
    · have hd : totalDegree I≤totalDegree J := Finset.sum_le_sum (fun i _ => translationMatrix_le b I J hm i)
      calc
        _ = (|(translationMatrix b I J:ℝ)| * Z^(totalDegree I))*circleNorm (a J) := by ring
        _ ≤ ((2^s*C^s)^v*Z^(totalDegree J))*circleNorm (a J) :=
          mul_le_mul_of_nonneg_right (translationMatrix_bound b I J Z C hZ hC hb) (norm_nonneg _)
        _ = (2^s*C^s)^v*(circleNorm (a J)*Z^(totalDegree J)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ha J (hI.trans_le hd)) (by positivity)
  have he : gridTranslate a b I=∑ J : Grid v s, (translationMatrix b I J:ℝ)*a J := by simp only [gridTranslate,mul_comm]
  rw [he]
  calc
    _ ≤ (∑ J : Grid v s, |(translationMatrix b I J:ℝ)| * circleNorm (a J))*Z^(totalDegree I) :=
      mul_le_mul_of_nonneg_right (integer_linear_bound _ _ _) (pow_nonneg hZ _)
    _ = ∑ J : Grid v s, |(translationMatrix b I J:ℝ)| * circleNorm (a J)*Z^(totalDegree I) := Finset.sum_mul _ _ _
    _ ≤ ∑ _ : Grid v s, (2^s*C^s)^v*A := Finset.sum_le_sum (fun J _ => hterm J)
    _ = _ := by simp [Grid,IntegerGridInterpolation.Grid]; ring

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients TriangularLatticeRecovery

lemma grid_scale_change {v s : ℕ} (a : Grid v s→ℝ) (N Z K A : ℝ)
    (hN : 0≤N) (hZ : 0≤Z) (hK : 1≤K) (hA : 0≤A) (hZN : Z≤K*N)
    (ha : ∀ J,0<totalDegree J → circleNorm (a J)*N^(totalDegree J)≤A) :
    ∀ J,0<totalDegree J → circleNorm (a J)*Z^(totalDegree J)≤K^(v*s)*A := by
  intro J hJ
  have hK0 : 0≤K := zero_le_one.trans hK
  calc
    _ ≤ circleNorm (a J)*(K*N)^(totalDegree J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ hZN _) (norm_nonneg _)
    _ = K^(totalDegree J)*(circleNorm (a J)*N^(totalDegree J)) := by rw [mul_pow]; ring
    _ ≤ K^(totalDegree J)*A := mul_le_mul le_rfl (ha J hJ)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hN _)) (pow_nonneg hK0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (grid_totalDegree_bound J)) hA

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
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

open SquareInduction BoxPolynomialLines PolynomialLineCoefficients
open CorrectedBoxLeibman TriangularLatticeRecovery

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem comparable_integer_box_unit
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ δ : ℝ) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A Z₀ : ℝ, 0<A ∧ 0<Z₀ ∧
      ∀ Z : ℝ, Z₀≤Z → ∀ a₀ : Fin v→ℤ, ∀ L : Fin v→ℕ,
      (∀ i,c₀*Z≤(L i:ℝ)) →
      (∀ i (k : ℕ),k<L i → |((a₀ i+(k:ℤ):ℤ):ℝ)|≤C₀*Z) →
      ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ≤‖rectMean v L (fun x => F (QuotientGroup.mk (f (fun i => a₀ i+(x i:ℤ)))))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ a : PolynomialLineCoefficients.Grid v s→ℝ, (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f x)).toAdd) ∧
          (∀ I,s<totalDegree I → a I=0) ∧
          ∀ I,0<totalDegree I → circleNorm (a I)*Z^(totalDegree I)≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,hA,hprod⟩ := box_monomial_all_lengths c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v (δ/2) (by positivity)
  obtain ⟨T,hT,hscale⟩ := choose_rectangle_scale v c₀ δ hc₀ hδ
  let C := max 1 C₀
  let K : ℝ := 4*T
  let B : ℝ := ((s+1:ℕ)^v:ℝ)*(2^s*C^s)^v*(K^(v*s)*A)
  have hC : 1≤C := le_max_left _ _
  have hK : 1≤K := by
    dsimp [K]
    have ht : 1≤(T:ℝ) := by exact_mod_cast hT
    linarith
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨U,B,2*T,hB,by positivity,?_⟩
  intro Z hZ a₀ L hL hloc f hf hd
  obtain ⟨N,hN,hZN,hNZ,hshort⟩ := hscale Z hZ
  have hZp : 0<Z := lt_of_lt_of_le (by positivity : (0:ℝ)<2*T) hZ
  have hLp : ∀ i,0<L i := by
    intro i
    exact_mod_cast (mul_pos hc₀ hZp).trans_le (hL i)
  obtain ⟨F,hFL,hFn,hdisc⟩ := hd
  let f₀ : (Fin v→ℕ)→ℂ := fun x => F (QuotientGroup.mk (f (fun i => a₀ i+(x i:ℤ))))
  have hf₀ : ∀ x,‖f₀ x‖≤1 := fun x => (F.norm_coe_le_norm _).trans hFn
  obtain ⟨y,hy,hcube⟩ := rectMean_bad_cube v hLp N hN f₀ hf₀ (∫ z,F z ∂μ) δ hδ hdisc (hshort L hL)
  let b : Fin v→ℤ := fun i => a₀ i+(y i:ℤ)
  let g : (Fin v→ℤ)→G := fun x => f (b+x)
  have hg : LeibmanSquare.Polynomial H 0 g := polynomial_affine H hf (AddMonoidHom.id _) b
  have hdg : δ/2≤‖boxMean v N (fun x => F (QuotientGroup.mk (g (fun i => (x i:ℤ)))))-(∫ z,F z ∂μ)‖ := by
    convert hcube using 1
    congr 3
    funext x
    change F (QuotientGroup.mk (f (b+(fun i => (x i:ℤ))))) = F (QuotientGroup.mk (f (fun i => a₀ i+((y i+x i:ℕ):ℤ))))
    congr 3
    ext i
    simp [b,Pi.add_apply,add_assoc]
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hat,hac⟩ := hprod N hN g hg ⟨F,hFL,hFn,hdg⟩
  have hAZ : ∀ J,0<totalDegree J → circleNorm (a J)*Z^(totalDegree J)≤K^(v*s)*A :=
    grid_scale_change a N Z K A (Nat.cast_nonneg _) hZp.le hK hA.le hZN hac
  have hb : ∀ i,|((-b i:ℤ):ℝ)|≤C*Z := by
    intro i
    rw [Int.cast_neg,abs_neg]
    apply (hloc i (y i) (hy i)).trans
    simpa only [mul_comm] using
      mul_le_mul (le_refl Z) (le_max_right (1:ℝ) C₀) hC₀.le hZp.le
  refine ⟨ξ,hξ,hξne,hξc,hξΓ,gridTranslate a (fun i => -b i),?_,gridTranslate_totalDegree a _ hat,?_⟩
  · intro x
    rw [gridTranslate_eval]
    have he : (fun i => (x i:ℝ)+((-b i:ℤ):ℝ))=(fun i => ((x i-b i:ℤ):ℝ)) := by
      ext i
      simp [sub_eq_add_neg]
    rw [he,ha]
    congr 2
    change f (b+(fun i => x i-b i))=f x
    congr 1
    ext i
    simp
  · intro I hI
    exact gridTranslate_bound a (fun i => -b i) Z C (K^(v*s)*A) hZp.le hC (by positivity) hb hAZ I hI

end ComparableBoxLeibman

end
end
end
end
end

end OAI
