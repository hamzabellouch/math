import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox07
import OAI.Combinatorics.SumProduct.Alignment.CubeTaylor01
import OAI.Combinatorics.SumProduct.Alignment.ScalarDifference01
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
open scoped BigOperators Topology
namespace CubeTaylorExpansion
open MvPolynomial CubeFaces HorizontalCubeCharacter BooleanBinomial CubeHorizontalIrrationality RationalLattice
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)

lemma faceBinomial_totalDegree (k : ℕ) (D : Finset ι) : (faceBinomial k D).totalDegree≤k := by
  apply Finset.sup_le
  intro e he
  exact (faceBinomial_support k D he).2

 

def facePower (k : ℕ) (a : H.level k) (D : Finset ι) (hD : D.card≤k) :
    Multiplicative ℝ→*cube H (Finset.univ : Finset ι) 0 where
  toFun t := faceLift H Finset.univ D k (Finset.subset_univ D) hD (levelPower c H S hH k a t.toAdd)
  map_one' := by simp
  map_mul' t u := by simp only [toAdd_mul,levelPower_add,map_mul]

omit [IsTopologicalGroup G] in
lemma facePower_mem [IsTopologicalGroup G]
    (k : ℕ) (a : H.level k) (D : Finset ι) (hD : D.card≤k) (t : ℝ) :
    facePower c H S hH k a D hD (Multiplicative.ofAdd t)∈
      (CubeMaxFiltration.filtration H (Finset.univ : Finset ι)).level k := by
  change face D (levelPower c H S hH k a t : G)∈CubeMaxFiltration.level H Finset.univ k
  exact CubeMaxFiltration.taylor_face_mem H Finset.univ (Finset.subset_univ D)
    le_rfl hD (levelPower c H S hH k a t).property

 
theorem faceFactor_polynomial (k : ℕ) (a : H.level k) (D : Finset ι) :
    LeibmanSquare.Polynomial (CubeMaxFiltration.filtration H (Finset.univ : Finset ι)) 0
      (faceFactor c H S hH k a D) := by
  change LeibmanSquare.Polynomial _ 0 (fun b => faceFactor c H S hH k a D b)
  by_cases hD : D.card≤k
  · have hp := ScalarDifferenceDegree.polynomial_power
      (CubeMaxFiltration.filtration H (Finset.univ : Finset ι)) (facePower c H S hH k a D hD)
      k (facePower_mem c H S hH k a D hD)
      (ScalarDifferenceDegree.eval_polynomial (faceBinomial k D) (faceBinomial_totalDegree k D))
    simpa only [faceFactor,dite_eq_left hD,facePower,MonoidHom.coe_mk,OneHom.coe_mk,toAdd_ofAdd] using hp
  · have hp := LeibmanSquare.polynomial_of_cube_mem (CubeMaxFiltration.filtration H (Finset.univ : Finset ι))
      (CubePolynomials.polynomials (A:=Option ι→ℝ) (CubeMaxFiltration.filtration H Finset.univ) 0).one_mem
    simpa only [faceFactor,dite_eq_right hD,Pi.one_def] using hp

lemma polynomial_list_prod {A K T : Type*} [AddCommGroup A] [Group K]
    (F : Filtration K) (L : List T) (f : T→A→K)
    (hf : ∀ t∈L,LeibmanSquare.Polynomial F 0 (f t)) :
    LeibmanSquare.Polynomial F 0 (fun x => (L.map (fun t => f t x)).prod) := by
  apply LeibmanSquare.polynomial_of_cube_mem
  induction L with
  | nil => exact (CubePolynomials.polynomials F 0).one_mem
  | cons t L ih =>
    have ht := LeibmanSquare.cube_mem_of_polynomial F (hf t List.mem_cons_self)
    have hl := ih (fun u hu => hf u (List.mem_cons_of_mem _ hu))
    exact (CubePolynomials.polynomials F 0).mul_mem ht hl

lemma cubeFactor_polynomial (k : ℕ) (a : H.level k) :
    LeibmanSquare.Polynomial (CubeMaxFiltration.filtration H (Finset.univ : Finset ι)) 0
      (cubeFactor c H S hH k a) := by
  apply polynomial_list_prod
  intro D _
  exact faceFactor_polynomial c H S hH k a D

 

theorem cubePolynomial_adapted (a : ∀ k : ℕ,H.level k) (s : ℕ) :
    LeibmanSquare.Polynomial (CubeMaxFiltration.filtration H (Finset.univ : Finset ι)) 0
      (cubePolynomial c H S hH a s) := by
  apply polynomial_list_prod
  intro k _
  exact cubeFactor_polynomial c H S hH k (a k)

end CubeTaylorExpansion
end
end
 

 
section

noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open MvPolynomial PolynomialLineCoefficients

lemma exponent_le_sum {σ : Type*} [Fintype σ] (e : σ →₀ ℕ) (i : σ) :
    e i≤e.sum (fun _ k => k) := by
  classical
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)

def exponentGrid {v s : ℕ} (e : Fin v →₀ ℕ) (he : e.sum (fun _ k => k) ≤ s) : Grid v s :=
  fun i => ⟨e i,Nat.lt_succ_of_le ((exponent_le_sum e i).trans he)⟩

@[simp] lemma gridExponent_exponentGrid {v s : ℕ} (e : Fin v →₀ ℕ) (he : e.sum (fun _ k => k) ≤ s) :
    gridExponent (exponentGrid e he)=e := by ext i; rfl

lemma exponentGrid_degree {v s : ℕ} (e : Fin v →₀ ℕ) (he : e.sum (fun _ k => k) ≤ s) :
    totalDegree (exponentGrid e he)=e.sum (fun _ k => k) := by
  rw [←gridExponent_degree,gridExponent_exponentGrid]

 

def polynomialGrid {v s : ℕ} (p : MvPolynomial (Fin v) ℝ) : Grid v s → ℝ :=
  fun e => p.coeff (gridExponent e)

lemma polynomial_eq_grid {v s : ℕ} (p : MvPolynomial (Fin v) ℝ) (hp : p.totalDegree ≤ s) :
    p=∑ e : Grid v s,monomial (gridExponent e) (polynomialGrid p e) := by
  classical
  ext m
  simp only [coeff_sum,coeff_monomial]
  by_cases hm : ∀ i,m i ≤ s
  · let e : Grid v s := fun i => ⟨m i,Nat.lt_succ_of_le (hm i)⟩
    have he : gridExponent e=m := by ext i; rfl
    rw [Finset.sum_eq_single e]
    · simp only [he,ite_true,polynomialGrid]
    · intro f _ hfe
      have hh : gridExponent f≠m := by
        intro h
        exact hfe (gridExponent_injective v s (h.trans he.symm))
      simp only [hh,ite_false]
    · simp
  · have hc : p.coeff m=0 := by
      by_contra hn
      have hmem := MvPolynomial.mem_support_iff.mpr hn
      exact hm (fun i => (le_degreeOf_of_mem_support i hmem).trans ((degreeOf_le_totalDegree p i).trans hp))
    rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro e _
    have hh : gridExponent e≠m := by
      intro h
      apply hm
      intro i
      have he := congrArg (fun x : Fin v →₀ ℕ => x i) h
      rw [←he]
      exact Nat.le_of_lt_succ (e i).isLt
    simp only [hh,ite_false]

lemma gridEval_polynomial {v s : ℕ} (p : MvPolynomial (Fin v) ℝ) (hp : p.totalDegree ≤ s)
    (x : Fin v → ℝ) : gridEval (polynomialGrid p : Grid v s → ℝ) x=eval x p := by
  have he := congrArg (eval x) (polynomial_eq_grid p hp)
  classical
  have hm (e : Grid v s) : (gridExponent e).prod (fun i k => x i^k)=∏ i,x i^(e i).val := by
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    rfl
  simpa only [map_sum,eval_monomial,hm,gridEval] using he.symm

end CorrectedBoxLeibman
end
end
 

 
section

noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeHorizontalIrrationality
open CubeFaces HorizontalCubeCharacter Filter BooleanBinomial MvPolynomial
open CubeTaylorExpansion CorrectedBoxLeibman PolynomialLineCoefficients PolynomialWeyl TriangularLatticeRecovery
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma scalarPolynomial_totalDegree [TopologicalSpace G] [IsTopologicalGroup G] (H : Filtration G)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (a : ∀ k : ℕ,H.level k) (s : ℕ) : (scalarPolynomial H χ a s).totalDegree ≤ s := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  apply MvPolynomial.totalDegree_finsetSum_le
  intro D _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C,zero_add] using
      (faceBinomial_totalDegree k D).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

omit [Fintype ι] [DecidableEq ι] in
lemma renamed_degree [Fintype ι] [DecidableEq ι]
    {v : ℕ} (e : Option ι ≃ Fin v) (m : Exponent ι) :
    (m.mapDomain e).sum (fun _ k => k)=degree m := by
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

 

theorem grid_irrationality {n v : ℕ} (c : RationalLattice.RealCoordinates G n)
    (H : Filtration G) (S : ℕ→Set (Fin n))
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
    (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
    (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)
    (χ : cube H (Finset.univ : Finset ι) 0→*Multiplicative ℝ)
    (hχne : χ≠1) (hχ : Continuous χ)
    (hχΓ : ∀ x : cube H (Finset.univ : Finset ι) 0,
      (∀ w,(x:Finset ι→G) w∈Γ) → ∃ z : ℤ,(χ x).toAdd=z) :
    ∃ b : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
      (∀ N (x : Fin v→ℤ),gridEval (b N) (fun i => (x i:ℝ))=
        (χ (cubePolynomial c H S hH (a N) s (fun i => (x (e i):ℝ)))).toAdd) ∧
      ∃ I,0 < PolynomialLineCoefficients.totalDegree I ∧
        Tendsto (fun N => circleNorm (b N I)*(N:ℝ)^(PolynomialLineCoefficients.totalDegree I)) atTop atTop := by
  let p (N : ℕ) : MvPolynomial (Fin v) ℝ := rename e (scalarPolynomial H χ (a N) s)
  have hp (N : ℕ) : (p N).totalDegree ≤ s :=
    (MvPolynomial.totalDegree_rename_le _ _).trans (scalarPolynomial_totalDegree H χ (a N) s)
  refine ⟨fun N => polynomialGrid (p N),?_,?_⟩
  · intro N x
    rw [gridEval_polynomial _ (hp N)]
    exact (MvPolynomial.eval_rename _ _ _).trans (scalarPolynomial_eval c H S hH (a N) s _ χ hχ)
  · obtain ⟨m,hm,hmS,hlim⟩ := coefficient_divergence H Γ h01 s hs a hirr χ hχne hχ hχΓ
    have hm' : (m.mapDomain e).sum (fun _ k => k) ≤ s := by rwa [renamed_degree]
    refine ⟨exponentGrid (m.mapDomain e) hm',?_,?_⟩
    · rwa [exponentGrid_degree,renamed_degree]
    · simpa only [circleNorm,polynomialGrid,gridExponent_exponentGrid,p,
        coeff_rename_mapDomain e e.injective,exponentGrid_degree,renamed_degree] using hlim

end CubeHorizontalIrrationality
end
end
 

 
section

noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

lemma iterDiff_comp {A B K : Type*} [AddCommGroup A] [AddCommGroup B] [Group K]
    (φ : A→+B) (f : B→K) (L : List A) :
    iterDiff L (fun x => f (φ x))=fun x => iterDiff (L.map φ) f (φ x) := by
  induction L generalizing f with
  | nil => rfl
  | cons h L ih =>
    rw [iterDiff,List.map_cons,iterDiff]
    have he : diff h (fun x => f (φ x))=fun x => diff (φ h) f (φ x) := by
      funext x
      simp only [diff,map_add]
    rw [he,ih]

lemma polynomial_comp {A B K : Type*} [AddCommGroup A] [AddCommGroup B] [Group K]
    (H : Filtration K) {k : ℕ} {f : B→K} (hf : LeibmanSquare.Polynomial H k f)
    (φ : A→+B) : LeibmanSquare.Polynomial H k (fun x => f (φ x)) := by
  intro L x
  rw [iterDiff_comp]
  simpa only [List.length_map] using hf (L.map φ) (φ x)

 

def cubeLattice (H : Filtration G) (Γ : Subgroup G) :
    Subgroup (cube H (Finset.univ : Finset ι) 0) where
  carrier := {x | ∀ w,(x:Finset ι→G) w∈Γ}
  one_mem' := fun _ => Γ.one_mem
  mul_mem' hx hy := fun w => Γ.mul_mem (hx w) (hy w)
  inv_mem' hx := fun w => Γ.inv_mem (hx w)

variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H Γ ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) (QuotientGroup.instTopologicalSpace (cubeLattice H Γ)) inferInstance]
variable [mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H Γ))
local instance : TopologicalSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include h01 hs hsk hqbound hq hΓ htop in
 

theorem haar_limit
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ) :
    letI : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_compact cc (cubeLattice H Γ) hΓ mtr htop
    letI : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_borelSpace (cubeLattice H Γ) mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(N:ℝ)≤hi i-lo i) →
      (∀ i,-C₀*(N:ℝ)≤lo i ∧ hi i≤C₀*(N:ℝ)) →
      ∀ F : C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ),
        LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (cubePolynomial c H S hH (a N) s
            (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))))-(∫ y,F y ∂μ)‖<η := by
  let K := CubeMaxFiltration.filtration H (Finset.univ : Finset ι)
  have hK0 : K.level 0=⊤ := CubeMaxFiltration.filtration_zero H Finset.univ
  have hK1 : K.level 1=⊤ := CubeMaxFiltration.filtration_one H Finset.univ h01
  let : ∀ k,(K.level k).Normal := fun k => LeibmanSquare.level_normal K hK0 k
  let φ : (Fin v→ℤ)→+(Option ι→ℝ) :=
    { toFun := fun x i => (x (e i):ℝ)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let f (N : ℕ) (x : Fin v→ℤ) := cubePolynomial c H S hH (a N) s (φ x)
  have hf (N : ℕ) : LeibmanSquare.Polynomial K 0 (f N) :=
    polynomial_comp K (cubePolynomial_adapted c H S hH (a N) s) φ
  exact haar_limit_fixed_progression cc hsk K hK0 hK1 s
    (CubeMaxFiltration.filtration_bot H Finset.univ hs) q hqbound hq
    (cubeLattice H Γ) hΓ htop μ v f hf
    (fun χ hn hc hχΓ => grid_irrationality c H S hH Γ h01 s hs e a hirr χ hn hc hχΓ)
    c₀ C₀ B hc₀ hC₀ hB d₀ hd₀ r

end CubeLocalHaar

end
end
end
end
end

end OAI
